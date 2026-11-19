#!/usr/bin/env python3
"""Blind U5 D1–D4 suite; source = contract b2d79a3 + MAIN's interface addendum."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shlex
import shutil
import socket
import subprocess
import tempfile
import time
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "tests/sandbox"
DEV = Path(os.environ.get("FVDEP_DEV_BIN", ROOT / "tool/.lake/build/bin/fvdep-dev")).resolve()
BIN = Path(os.environ.get("FVDEP_BIN", ROOT / "tool/.lake/build/bin/fvdep")).resolve()
SEED = int(os.environ.get("FVDEP_TEST_SEED", "5006001"))
BASE = "b2d79a3"
SPEC_MODULE = "Fvdep.Base64.Encode.V1_0_0"
SPEC = SPEC_MODULE + ".encode"
HEX = r"[0-9a-f]{64}"
CAP = 32 * 1024 * 1024
CASES: list[Case] = []
# T1's toolchain record, computed once per run (`fvdep-dev cache fingerprint`: ≈ 14 CPU-s over the
# 2.9 GB toolchain) + copied into each case's empty cache: setup built once, no case's assertions
# touched (none checks T1; MAIN's `lake test` covers its recompute).
TOOLCHAIN_SEED: Path | None = None


def need(ok: object, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def frame_digest(tag: str, files: dict[str, bytes]) -> str:
    """U3 H2, independent encoder: UTF-8 lengths, big-endian, byte-sorted paths."""
    payload = bytearray()

    def sized(b: bytes) -> None:
        payload.extend(len(b).to_bytes(8, "big"))
        payload.extend(b)

    sized(tag.encode())
    payload.extend(len(files).to_bytes(8, "big"))
    for path in sorted(files, key=lambda s: s.encode()):
        sized(path.encode())
        sized(files[path])
    return sha(bytes(payload))


def escape(s: str) -> str:
    out: list[str] = []
    for c in s:
        n = ord(c)
        out.append({9: r"\t", 10: r"\n", 13: r"\r"}.get(n, f"\\u00{n:02X}")
                   if n < 32 or 127 <= n <= 159 else c)
    return "".join(out)


def text_lines(b: bytes) -> list[str]:
    # str.splitlines also splits raw C1/NEL; that would conceal a line-rule defect.
    s = b.decode("utf-8", "strict")
    need(not s or s.endswith("\n"), "text output lacks its final LF")
    return s[:-1].split("\n") if s else []


@dataclass
class Result:
    argv: list[str]
    rc: int
    out: bytes
    err: bytes

    @property
    def lines(self) -> list[str]:
        return text_lines(self.out)

    @property
    def all_text(self) -> str:
        return (self.out + self.err).decode("utf-8", "replace")

    def code(self, expected: int) -> None:
        need(self.rc == expected, f"exit {self.rc}, expected {expected}; "
             f"stdout={self.out[:350]!r}; stderr={self.err[:350]!r}")

    def line(self, pattern: str) -> re.Match[str]:
        matches = [m for s in self.lines if (m := re.fullmatch(pattern, s))]
        need(len(matches) == 1, f"expected one /{pattern}/, got {len(matches)}; "
             f"stdout={self.out[:500]!r}; stderr={self.err[:300]!r}")
        return matches[0]

    def clean_lines(self) -> None:
        for stream in (self.out, self.err):
            for s in text_lines(stream):
                need(all(not (ord(c) < 32 or 127 <= ord(c) <= 159) for c in s),
                     f"raw control character in output {s!r}")


@dataclass
class Case:
    id: str
    part: str
    clause: str
    expected: str
    run: Callable[[Context], None]


def case(id_: str, part: str, clause: str, expected: str):
    def wrap(fn: Callable[[Context], None]) -> Callable[[Context], None]:
        CASES.append(Case(id_, part, clause, expected, fn))
        return fn
    return wrap


@dataclass
class Context:
    home: Path
    records: list[dict[str, Any]] = field(default_factory=list)
    name: str = ""

    def __post_init__(self) -> None:
        self.cache = self.home / "cache"
        self.cache.mkdir()
        self.env = dict(os.environ)
        for k in tuple(self.env):
            if k.startswith("FVDEP_") and k not in {"FVDEP_TEST_SEED"}:
                self.env.pop(k)
        self.env.update(FVDEP_CACHE=str(self.cache), FVDEP_LIBRARY_URL=str(ROOT))
        if TOOLCHAIN_SEED is not None:
            shutil.copytree(TOOLCHAIN_SEED, self.cache / "toolchains")

    def call(self, args: list[str], *, env: dict[str, str] | None = None,
             timeout: int = 240, binary: Path = DEV) -> Result:
        merged = self.env | (env or {})
        argv = [str(binary), *map(str, args)]
        start = time.monotonic()
        try:
            p = subprocess.run(argv, cwd=ROOT, env=merged, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=timeout, check=False)
            r = Result(argv, p.returncode, p.stdout, p.stderr)
        except subprocess.TimeoutExpired as e:
            self.records.append({"case": self.name, "argv": argv, "exit": "harness-timeout",
                                 "stdout": repr(e.stdout), "stderr": repr(e.stderr)})
            raise AssertionError(f"driver exceeded harness bound {timeout}s: {shlex.join(argv)}") from e
        recorded_env = {k: v for k, v in merged.items() if k.startswith("FVDEP_")}
        if env and "PATH" in env:
            recorded_env["PATH"] = env["PATH"]
        self.records.append({"case": self.name, "argv": argv, "environment": recorded_env, "exit": r.rc,
                             "stdout": r.out.decode("utf-8", "backslashreplace"),
                             "stderr": r.err.decode("utf-8", "backslashreplace"),
                             "seconds": round(time.monotonic() - start, 4)})
        r.clean_lines()
        return r

    def sandbox(self, script: str, *options: str, timeout: int = 30,
                env: dict[str, str] | None = None) -> Result:
        return self.call(["sandbox", "run", *options, "--", "/usr/bin/python3", "-I", "-c", script],
                         timeout=timeout, env=env)

    def project(self, name: str = "project", fixture: str = "honest") -> Path:
        p = self.home / name
        shutil.copytree(HERE / "fixtures" / fixture, p)
        # D1 consumes a working copy, but a real 40-hex pin avoids an unrelated missing-pin refusal.
        pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        manifest = p / "fvdep.toml"
        manifest.write_text(manifest.read_text().replace("0" * 40, pin))
        return p

    def phase(self, p: Path, *options: str, library: Path = ROOT,
              spec_module: str = SPEC_MODULE, spec: str = SPEC,
              id_: str = "base64.encode", env: dict[str, str] | None = None) -> Result:
        return self.call(["phase", "check", str(p), id_, "--library", str(library),
                          "--spec-module", spec_module, "--spec", spec, *options], env=env)

    def library(self, name: str = "library") -> Path:
        p = self.home / name
        p.mkdir()
        (p / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
        return p


def put(p: Path, rel: str, contents: str | bytes) -> None:
    f = p / rel
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_bytes(contents.encode() if isinstance(contents, str) else contents)


def manifest_modules(p: Path, impls: list[str], proofs: list[str],
                     impl: str = "SandboxTrial.encode", proof: str = "SandboxTrial.encode_eq") -> None:
    f = p / "fvdep.toml"
    # The entry's keys alone: `[policy]` holds a `proof = ` line too (rewriting it = a manifest refusal).
    head, sep, s = f.read_text().partition("[modules.")
    s = re.sub(r"impl_modules = .*", "impl_modules = " + json.dumps(impls), s)
    s = re.sub(r"proof_modules = .*", "proof_modules = " + json.dumps(proofs), s)
    s = re.sub(r'^impl = .*', "impl = " + json.dumps(impl), s, flags=re.M)
    s = re.sub(r'^proof = .*', "proof = " + json.dumps(proof), s, flags=re.M)
    f.write_text(head + sep + s)


def sandbox_ok(r: Result, outcome: str = "exited 0", frame: str = "complete") -> None:
    r.code(0)
    r.line("outcome " + re.escape(outcome))
    r.line("frame " + re.escape(frame))
    need(not any(s.startswith(("PROVEN", "DELIVERED")) for s in r.lines),
         "a sandbox build is not proof/delivery evidence")


def stream(r: Result, name: str, original: bytes, cap: int) -> None:
    # MAIN Q2/Q4: total consumed; kept prefix + suffix concatenate before line escaping.
    r.line(rf"{name} {len(original)} dropped {max(0, len(original) - cap)}")
    prefix = "out: " if name == "stdout" else "err: "
    actual = [s[len(prefix):] for s in r.lines if s.startswith(prefix)]
    kept = original if len(original) <= cap else original[:cap // 2] + original[-(cap // 2):]
    expected = [escape(s) for s in kept.decode().split("\n")]
    if expected and expected[-1] == "":
        expected.pop()
    need(actual == expected, f"{name} capture {actual!r}, expected {expected!r}")


def files(r: Result) -> dict[str, tuple[int, str]]:
    found: dict[str, tuple[int, str]] = {}
    for s in r.lines:
        if s.startswith("file "):
            m = re.fullmatch(rf"file (.+) ([0-9]+) ({HEX})", s)
            need(m is not None, f"malformed file line {s!r}")
            assert m is not None
            need(m[1] not in found, f"duplicate framed file {m[1]}")
            found[m[1]] = (int(m[2]), m[3])
    return found


def source_digests(p: Path) -> tuple[str, str]:
    import tomllib
    entry = tomllib.loads((p / "fvdep.toml").read_text())["modules"]["base64.encode"]
    digests = []
    for field_, tag in (("impl_modules", "fvdep/impl-sources/1"),
                        ("proof_modules", "fvdep/proof-sources/1")):
        data = {m.replace(".", "/") + ".lean":
                (p / (m.replace(".", "/") + ".lean")).read_bytes() for m in entry[field_]}
        digests.append(frame_digest(tag, data))
    return digests[0], digests[1]


def built(r: Result) -> tuple[str, str]:
    r.code(0)
    e1 = r.line(rf"phase1 built ({HEX})")[1]
    e2 = r.line(rf"phase2 built ({HEX}) on ({HEX})")
    need(e2[2] == e1, "phase 2 does not bind the reported phase-1 export")
    need(not any(s.startswith(("infra ", "phase1 failed", "phase2 failed", "PROVEN", "DELIVERED"))
                 for s in r.lines), "built output carries a refusal or proof/delivery claim")
    return e1, e2[1]


def phase_failed(r: Result, n: int, path: str | None = None, line: int | None = None,
                 message: str | None = None) -> None:
    r.code(1)
    label = "implementation" if n == 1 else "proof"
    reason = r.line(rf"phase{n} failed: (.+)")[1]
    need(reason.startswith(label + " build failed ("), f"wrong phase reason {reason!r}")
    if path:
        need(re.search(re.escape(path) + (rf":{line}: " if line else r":[0-9]+: "), reason),
             f"missing project-relative position {path}:{line}: {reason!r}")
    if message:
        need(message in reason, f"diagnostic lost {message!r}: {reason!r}")
    need("/fvdep/src/" not in reason, f"sandbox path escaped mapping: {reason!r}")
    if n == 1:
        need(not any(s.startswith("phase2 ") for s in r.lines), "phase 2 ran after phase-1 refusal")
    else:
        r.line(rf"phase1 built ({HEX})")
    need(not any(s.startswith("infra ") for s in r.lines), "ordinary input refusal became infrastructure")
    r.line(r"bundle (.+) (complete|incomplete)")


def infra(r: Result, *parts: str, no_phases: bool = False) -> None:
    r.code(2)
    detail = r.line(r"infra io: (.+)")[1]
    for part in parts:
        need(part.lower() in detail.lower(), f"infrastructure detail lacks {part!r}: {detail!r}")
    need(not any(" failed:" in s for s in r.lines), "resource/setup failure became a negative verdict")
    if no_phases:
        need(not any(s.startswith(("phase1 ", "phase2 ")) for s in r.lines),
             "snapshot refusal emitted a phase observation")
        need(not any(s.startswith(("impl_sources ", "proof_sources ")) for s in r.lines),
             "snapshot refusal emitted source digests")


def artifacts(r: Result, phase: str) -> dict[str, tuple[int, str]]:
    data: dict[str, tuple[int, str]] = {}
    for s in r.lines:
        if s.startswith("artifact " + phase + " "):
            m = re.fullmatch(rf"artifact {phase} (.+) ([0-9]+) ({HEX})", s)
            need(m is not None, f"malformed artifact line {s!r}")
            assert m is not None
            need(m[1] not in data, f"duplicate artifact {m[1]}")
            data[m[1]] = (int(m[2]), m[3])
    return data


def family(module: str, modern: bool = False) -> set[str]:
    path = module.replace(".", "/")
    suffixes = [".olean", ".ilean", ".c"]
    if modern:
        suffixes += [".olean.server", ".olean.private", ".ir.sig", ".ir"]
    return {path + s for s in suffixes}


def artifact_layout(r: Result, outdir: Path) -> None:
    """D1 addendum: exact phase directories + canonical manifest in printed-file order."""
    entries: list[dict[str, Any]] = []
    expected_files: dict[str, tuple[int, str]] = {}
    for s in r.lines:
        if s.startswith("artifact "):
            m = re.fullmatch(rf"artifact (phase1|phase2) (.+) ([0-9]+) ({HEX})", s)
            need(m is not None, f"malformed artifact record {s!r}")
            assert m is not None
            phase, path, n, digest = m[1], m[2], int(m[3]), m[4]
            need(not Path(path).is_absolute() and ".." not in Path(path).parts,
                 f"artifact path is not project-relative: {path!r}")
            destination = phase + "/" + path
        elif s.startswith("export "):
            m = re.fullmatch(rf"export (phase1|phase2) (.+) ([0-9]+) ({HEX})", s)
            need(m is not None, f"malformed export record {s!r}")
            assert m is not None
            phase = "exports"
            path = "e1.ndjson" if m[1] == "phase1" else "e2.ndjson"
            destination = "exports/" + path
            need(m[2] == destination, f"export path {m[2]!r}, expected {destination!r}")
            n, digest = int(m[3]), m[4]
        else:
            continue
        need(destination not in expected_files, f"duplicate printed file {destination}")
        expected_files[destination] = (n, digest)
        entries.append({"phase": phase, "path": path, "size": n, "sha256": digest})
    need(outdir.is_dir() and not outdir.is_symlink(), "artifacts directory absent or a link")
    expected_dirs: set[str] = set()
    for path, (n, digest) in expected_files.items():
        f = outdir / path
        need(f.is_file() and not f.is_symlink(), f"retained file absent/nonregular: {path}")
        need(f.stat().st_size == n and sha(f.read_bytes()) == digest, f"retained tuple differs: {path}")
        expected_dirs.update(str(parent) for parent in Path(path).parents if str(parent) != ".")
    # The schema's strings are ASCII paths/digests; Python's sorted compact encoding = J4 here.
    canonical = json.dumps({"schema": 1, "files": entries}, sort_keys=True,
                           separators=(",", ":"), ensure_ascii=False).encode()
    metadata = outdir / "manifest.json"
    need(metadata.is_file() and not metadata.is_symlink(), "manifest.json absent/nonregular")
    need(metadata.read_bytes() == canonical, "manifest.json differs from canonical schema 1 / printed order")
    actual = {str(f.relative_to(outdir)) for f in outdir.rglob("*")}
    need(actual == set(expected_files) | expected_dirs | {"manifest.json"},
         f"artifacts directory has missing/extra entries: {actual ^ (set(expected_files) | expected_dirs | {'manifest.json'})}")


def bwrap_proxy(c: Context, fixture: str) -> dict[str, str]:
    directory = c.home / ("proxy-" + fixture)
    directory.mkdir()
    script = (HERE / "fixtures/bwrap" / fixture / "bwrap").read_text()
    if "@REAL_BWRAP@" in script:
        real = shutil.which("bwrap", path=c.env.get("PATH", "/usr/bin:/bin"))
        need(real is not None, "fixture requires the real bwrap on the original PATH")
        assert real is not None
        need(script.count("@REAL_BWRAP@") == 1, "ambiguous bwrap fixture substitution")
        script = script.replace("@REAL_BWRAP@", shlex.quote(str(Path(real).resolve())))
    proxy = directory / "bwrap"
    proxy.write_text(script)
    proxy.chmod(0o755)
    return {"PATH": str(directory) + ":" + c.env.get("PATH", "/usr/bin:/bin")}


def audit_artifacts() -> None:
    """Grade the artifacts checker with contract-shaped data, never a product stub."""
    payloads = {"phase1/Impl.olean": b"impl", "phase2/Proof.olean": b"proof",
                "exports/e1.ndjson": b"e1", "exports/e2.ndjson": b"e2"}
    entries = [{"phase": "phase1", "path": "Impl.olean", "sha256": sha(b"impl"), "size": 4},
               {"phase": "exports", "path": "e1.ndjson", "sha256": sha(b"e1"), "size": 2},
               {"phase": "phase2", "path": "Proof.olean", "sha256": sha(b"proof"), "size": 5},
               {"phase": "exports", "path": "e2.ndjson", "sha256": sha(b"e2"), "size": 2}]
    lines = [f"artifact phase1 Impl.olean 4 {sha(b'impl')}",
             f"export phase1 exports/e1.ndjson 2 {sha(b'e1')}",
             f"artifact phase2 Proof.olean 5 {sha(b'proof')}",
             f"export phase2 exports/e2.ndjson 2 {sha(b'e2')}"]
    observation = Result([], 0, ("\n".join(lines) + "\n").encode(), b"")
    text = json.dumps({"files": entries, "schema": 1}, sort_keys=True, separators=(",", ":")).encode()
    with tempfile.TemporaryDirectory(prefix="fvdep-artifact-audit-") as tmp:
        for variant in ("valid", "extra", "wrong-phase", "digest", "order", "schema", "missing", "whitespace", "link"):
            out = Path(tmp) / variant
            for path, data in payloads.items():
                put(out, path, data)
            put(out, "manifest.json", text)
            if variant == "extra":
                put(out, "unexpected", b"extra")
            elif variant == "wrong-phase":
                (out / "phase1/Impl.olean").rename(out / "phase2/Impl.olean")
            elif variant == "digest":
                put(out, "phase1/Impl.olean", b"IMPL")
            elif variant == "order":
                put(out, "manifest.json", json.dumps({"files": entries[::-1], "schema": 1},
                    sort_keys=True, separators=(",", ":")))
            elif variant == "schema":
                put(out, "manifest.json", text.replace(b'"schema":1', b'"schema":2'))
            elif variant == "missing":
                (out / "manifest.json").unlink()
            elif variant == "whitespace":
                put(out, "manifest.json", text + b"\n")
            elif variant == "link":
                actual = Path(tmp) / "link-target"
                actual.write_bytes(b"impl")
                target = out / "phase1/Impl.olean"
                target.unlink()
                target.symlink_to(actual)
            try:
                artifact_layout(observation, out)
            except AssertionError:
                need(variant != "valid", "artifact checker refused its contract-shaped positive control")
            else:
                need(variant == "valid", f"artifact checker accepted planted {variant}")
    print("ARTIFACT_AUDIT positive PASS; 8 planted deviations refused")


def bundle(r: Result) -> tuple[Path, str]:
    m = r.line(r"bundle (.+) (complete|incomplete)")
    p = Path(m[1])
    need(p.is_dir(), f"bundle directory absent: {p}")
    return p, m[2]


# D2: each usage test starts with a supported positive call, so pre-U5 generic usage is red.
for exit_ in (0, 1, 7, 127, 255):
    @case(f"R.exit.{exit_}", "D2", "D2/R5/R6/R8", f"exit 0; outcome exited {exit_}; complete frame")
    def _exit(c: Context, n: int = exit_) -> None:
        sandbox_ok(c.sandbox(f"raise SystemExit({n})"), f"exited {n}")


@case("R.exit.property", "D2", "D2/R6", "every code 0..255 preserved; driver exit 0")
def exit_property(c: Context) -> None:
    codes = list(range(256))
    random.Random(SEED).shuffle(codes)
    for n in codes:
        sandbox_ok(c.sandbox(f"raise SystemExit({n})"), f"exited {n}")


@case("R.signal", "D2", "R8/D2", "child SIGTERM -> outcome exited 143, exit 0")
def child_signal(c: Context) -> None:
    sandbox_ok(c.sandbox("import os,signal; os.kill(os.getpid(),signal.SIGTERM)"), "exited 143")


@case("R.not-started", "D2", "R8/D2", "missing child -> outcome exited 127, exit 0")
def not_started(c: Context) -> None:
    r = c.call(["sandbox", "run", "--", "/usr/bin/u5-nonexistent-executable"])
    sandbox_ok(r, "exited 127")


@case("R.timeout", "D2", "D2/R4/R6", "deadline -> timed_out; report exit 0")
def runner_timeout(c: Context) -> None:
    r = c.sandbox("import time; time.sleep(30)", "--deadline", "1", timeout=20)
    r.code(0)
    r.line("outcome timed_out")
    r.line(r"frame (complete|invalid)")


for channel in ("stdout", "stderr"):
    for nbytes in (0, 1, 63, 64, 65, 128, 4097):
        @case(f"R.pump.{channel}.{nbytes}", "D2", "R3/D2",
              f"{channel} consumes {nbytes}; keeps first/last within 64; exact dropped count")
        def _pump(c: Context, name: str = channel, n: int = nbytes) -> None:
            payload = bytes(65 + i % 26 for i in range(n))
            fd = 1 if name == "stdout" else 2
            r = c.sandbox(f"import os; os.write({fd},{payload!r})", "--diagnostic-bytes", "64")
            sandbox_ok(r)
            stream(r, name, payload, 64)
            stream(r, "stderr" if name == "stdout" else "stdout", b"", 64)


@case("R.pump.concurrent", "D2", "R3/D2", "both pipe-sized streams drained concurrently; exact caps/counts")
def concurrent_pumps(c: Context) -> None:
    r = c.sandbox("import os,threading\n"
                  "def go(fd,x):\n"
                  " for _ in range(128): os.write(fd,x*4096)\n"
                  "t=threading.Thread(target=go,args=(2,b'E'));t.start();go(1,b'O');t.join()",
                  "--diagnostic-bytes", "64", "--deadline", "10")
    sandbox_ok(r)
    stream(r, "stdout", b"O" * 524288, 64)
    stream(r, "stderr", b"E" * 524288, 64)


for channel in ("stdout", "stderr"):
    @case("R.line-controls." + channel, "D2", "D2/interface-1",
          "all C0/C1 except LF escaped; TAB/CR short forms; uppercase hex; no raw Cc")
    def _controls(c: Context, name: str = channel) -> None:
        s = "start:" + "".join(chr(n) for n in [*range(10), *range(11, 32), *range(127, 160)]) + ":end"
        fd = 1 if name == "stdout" else 2
        r = c.sandbox(f"import os; os.write({fd},{(s + chr(10)).encode()!r})")
        sandbox_ok(r)
        r.line(re.escape(("out: " if name == "stdout" else "err: ") + escape(s)))


@case("R.line-unicode", "D2", "D2/interface-1", "non-Cc Unicode/backslash text unchanged; LF separates relayed lines")
def unicode_lines(c: Context) -> None:
    s = "é λ 😀     ﻿ \\n"
    r = c.sandbox(f"print({s!r}); print('second')")
    sandbox_ok(r)
    r.line(re.escape("out: " + s))
    r.line("out: second")


for variant in ("empty", "zero", "nested", "binary", "unicode", "controls"):
    @case("R.files." + variant, "D2", "R8/D2/U3-H1", "complete frame; each file path, size and SHA-256 exact")
    def _files(c: Context, kind: str = variant) -> None:
        rng = random.Random(SEED)
        expected: dict[str, bytes] = {}
        if kind == "zero":
            expected = {"empty.bin": b""}
        elif kind == "nested":
            expected = {"z/final": b"last", "a/first": b"first", "mid": b"middle"}
        elif kind == "binary":
            expected = {f"n{n}.bin": rng.randbytes(n) for n in (1, 255, 256, 4096)}
        elif kind == "unicode":
            expected = {"space dir/é-😀.bin": b"utf8-name"}
        elif kind == "controls":
            expected = {"name\t\n\x1b\x85.bin": b"escaped-name"}
        script = "from pathlib import Path\n"
        for path, data in expected.items():
            script += (f"p=Path('/fvdep/work/out')/{path!r}; "
                       f"p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes({data!r})\n")
        r = c.sandbox(script)
        sandbox_ok(r)
        need(files(r) == {escape(path): (len(b), sha(b)) for path, b in expected.items()},
             f"framed files differ: {files(r)!r}")


@case("R.frame.overflow", "D2", "R3/R8/D2", "small frame cap -> frame overflow; report exit 0")
def runner_frame_overflow(c: Context) -> None:
    r = c.sandbox("from pathlib import Path; p=Path('/fvdep/work/out/x'); "
                  "p.parent.mkdir(exist_ok=True); p.write_bytes(b'x'*4096)", "--frame-bytes", "128")
    r.code(0)
    r.line(r"outcome exited [0-9]+")
    r.line("frame overflow")
    need(not files(r), "overflow frame exposed a trusted file")


@case("R.frame.invalid", "D2", "R5/R8/D2", "child kills its helper -> reported exited 137 with invalid frame, driver exit 0")
def invalid_frame(c: Context) -> None:
    r = c.sandbox("import os,signal; os.kill(os.getppid(),signal.SIGKILL)")
    sandbox_ok(r, "exited 137", "invalid")
    need(not files(r), "invalid frame exposed a file")


@case("R.setup-failed", "D2", "T1/R6/D2/addendum", "minimum bwrap 0.8.0 accepted; no status -> setup_failed using first stderr line")
def setup_failed(c: Context) -> None:
    sandbox_ok(c.sandbox("pass"))
    r = c.sandbox("pass", env=bwrap_proxy(c, "setup-failed"))
    r.code(0)
    r.line("outcome setup_failed: u5-setup-failure")
    r.line("frame invalid")


@case("R.preflight.old-version", "D2", "T1/D2/addendum", "PATH bwrap 0.7.0 -> infra tool_missing, exit 2 before a step")
def old_bwrap(c: Context) -> None:
    sandbox_ok(c.sandbox("pass"))
    r = c.sandbox("pass", env=bwrap_proxy(c, "old-version"))
    r.code(2)
    r.line(r"infra tool_missing: .*bwrap.*")
    need(not any(s.startswith("outcome ") for s in r.lines), "unqualified bwrap ran a step")
    need("u5-old-bwrap-must-not-run" not in r.all_text, "old bwrap was run after its refused preflight")


for kind in ("frame-junk", "frame-closed"):
    @case("R.proxy." + kind, "D2", "R8/D2/addendum", "PATH bwrap corrupts/closes frame descriptor -> frame invalid; no files; report exit 0")
    def _frame_proxy(c: Context, variant: str = kind) -> None:
        sandbox_ok(c.sandbox("pass"))
        r = c.sandbox("pass", env=bwrap_proxy(c, variant))
        r.code(0)
        r.line(r"outcome (exited [0-9]+|setup_failed: .+)")
        r.line("frame invalid")
        if variant == "frame-junk":
            r.line("outcome exited 0")
        need(not files(r), "corrupt/closed frame exposed a file")


@case("R.src", "D2", "D2", "--src copied to /fvdep/src; exact contents relayed")
def runner_sources(c: Context) -> None:
    src = c.home / "src"
    src.mkdir()
    (src / "message").write_text("source data")
    r = c.sandbox("from pathlib import Path; print(Path('/fvdep/src/message').read_text())", "--src", str(src))
    sandbox_ok(r)
    r.line("out: source data")


USAGE = [("missing-command", ["sandbox", "run"]),
         ("unknown-option", ["sandbox", "run", "--typo", "--", "/usr/bin/true"]),
         ("missing-value", ["sandbox", "run", "--deadline"]),
         ("bad-number", ["sandbox", "run", "--frame-bytes", "no", "--", "/usr/bin/true"]),
         ("negative-number", ["sandbox", "run", "--work-bytes", "-1", "--", "/usr/bin/true"])]
for suffix, argv in USAGE:
    @case("R.usage." + suffix, "D2", "D2/interface-1", "supported-command control; malformed argv -> exit 2, no outcome")
    def _usage(c: Context, args: list[str] = argv) -> None:
        sandbox_ok(c.sandbox("pass"))
        r = c.call(args)
        r.code(2)
        need(not any(s.startswith("outcome ") for s in r.lines), "usage error started a step")
        need(bool(r.err), "usage diagnostic absent")


# D1: base fixture uses a definition equal to the spec; launch trials use independent code.
@case("P.honest", "D1", "D1/P2/P3/P4/P6/addendum", "two builds; source hashes; exact retained files + canonical ordered manifest; e2 on e1")
def honest(c: Context) -> None:
    p = c.project()
    out = c.home / "artifacts"
    r = c.phase(p, "--artifacts", str(out))
    e1, e2 = built(r)
    i, proof = source_digests(p)
    r.line("impl_sources " + i)
    r.line("proof_sources " + proof)
    need(set(artifacts(r, "phase1")) == family("SandboxTrial.Impl"), "phase-1 artifact family differs")
    need(set(artifacts(r, "phase2")) == family("SandboxTrial.Proof"), "phase-2 artifact family differs")
    for phase, digest in (("phase1", e1), ("phase2", e2)):
        m = r.line(rf"export {phase} (.+) ([0-9]+) ({HEX})")
        need(m[3] == digest, f"{phase} export line disagrees with built digest")
    artifact_layout(r, out)
    need(r.lines.index("impl_sources " + i) < r.lines.index("phase1 built " + e1), "digest after phase 1")
    need(r.lines.index("phase1 built " + e1) < r.lines.index(f"phase2 built {e2} on {e1}"), "phase order reversed")


@case("P.module-proof", "D1", "D1/P2/P6/addendum", "module-header proof's 7-part family + exact retained layout/manifest")
def module_proof(c: Context) -> None:
    # Lean's module system refuses legacy imports. D1 roots are unqualified; the public True
    # witness tests P2's artifact family alone. Honest fn/ABI equalities run in the launch trials.
    p = c.project(fixture="module-proof")
    out = c.home / "artifacts"
    r = c.phase(p, "--artifacts", str(out))
    built(r)
    need(set(artifacts(r, "phase2")) == family("SandboxTrial.Proof", True), "module-system artifact family differs")
    artifact_layout(r, out)


for kind in ("frame-junk", "frame-closed"):
    @case("P.proxy." + kind, "D1", "P5/D1/addendum", "after cache warm-up, corrupt/closed phase frame -> infra io; no later phase")
    def _phase_frame_proxy(c: Context, variant: str = kind) -> None:
        p = c.project()
        built(c.phase(p))
        r = c.phase(p, env=bwrap_proxy(c, variant))
        infra(r)
        need(not any(s.startswith(("phase1 built ", "phase2 ")) for s in r.lines),
             "invalid phase-1 frame led to a built observation or phase 2")


for n in (1, 2):
    @case(f"P.compile-error.{n}", "D1", "D1/P5/B1", "Lean error -> exit 1; project-relative first diagnostic; later phase absent")
    def _compile_error(c: Context, phase: int = n) -> None:
        p = c.project()
        path = "SandboxTrial/Impl.lean" if phase == 1 else "SandboxTrial/Proof.lean"
        put(p, path, "import Fvdep.Base64.Encode.V1_0_0\n\ndef broken := u5_missing_identifier\n")
        r = c.phase(p)
        phase_failed(r, phase, path, 3, "u5_missing_identifier")


for n, root in ((1, "SandboxTrial.missing_impl"), (2, "SandboxTrial.missing_proof")):
    @case(f"P.missing-root.{n}", "D1", "P4/P5/D1", "absent consumer root -> phase failed naming root, exit 1")
    def _missing_root(c: Context, phase: int = n, constant: str = root) -> None:
        p = c.project()
        manifest_modules(p, ["SandboxTrial.Impl"], ["SandboxTrial.Proof"],
                         impl=constant if phase == 1 else "SandboxTrial.encode",
                         proof=constant if phase == 2 else "SandboxTrial.encode_eq")
        r = c.phase(p)
        phase_failed(r, phase, message=constant + " is not defined")


@case("P.first-diagnostic", "D1", "B1/D1", "reason selects first error diagnostic, not later errors")
def first_diagnostic(c: Context) -> None:
    p = c.project()
    put(p, "SandboxTrial/Proof.lean", "import SandboxTrial.Impl\n\n"
        "def broken1 := u5_first_missing\n\ndef broken2 := u5_later_missing\n")
    r = c.phase(p)
    phase_failed(r, 2, "SandboxTrial/Proof.lean", 3, "u5_first_missing")
    reason = r.line(r"phase2 failed: (.+)")[1]
    need("u5_later_missing" not in reason, "reason selected/combined a later diagnostic")


@case("P.diagnostic-line-rule", "D1", "B1/D1/interface-1", "reason retains first message line; controls escaped after path mapping")
def diagnostic_line_rule(c: Context) -> None:
    p = c.project()
    put(p, "SandboxTrial/Proof.lean", "import Lean\nimport SandboxTrial.Impl\n\n"
        "open Lean Elab Command\n\n"
        # Lean 4.35 leaves `throwError`'s result type open here without the ascription.
        'run_cmd (throwError ("u5 first " ++ String.singleton (Char.ofNat 27) ++ "\\tend\\nsecond line") : '
        'CommandElabM Unit)\n')
    r = c.phase(p)
    phase_failed(r, 2, "SandboxTrial/Proof.lean", message=r"u5 first \u001B\tend")
    need("second line" not in r.line(r"phase2 failed: (.+)")[1], "reason kept a later message line")


@case("P.missing-library-root", "D1", "P4/P5/D1", "absent spec constant -> infra io, exit 2")
def missing_library_root(c: Context) -> None:
    p = c.project()
    r = c.phase(p, spec=SPEC_MODULE + ".u5_missing_spec")
    infra(r, "u5_missing_spec")


@case("P.missing-abi-root", "D1", "P4/P5/D1", "absent ABI root -> infra io, exit 2")
def missing_abi_root(c: Context) -> None:
    r = c.phase(c.project(), "--abi-module", "Fvdep.Abi.V1_0_0", "--abi", "Fvdep.Abi.V1_0_0.u5_missing_abi")
    infra(r, "u5_missing_abi")


for phase in (1, 2):
    @case(f"P.override-root.{phase}", "D1", "D1/P4", "--roots override requests a missing constant -> phase failed")
    def _override(c: Context, n: int = phase) -> None:
        r = c.phase(c.project(), f"--roots{n}", "SandboxTrial.override_missing")
        phase_failed(r, n, message="SandboxTrial.override_missing is not defined")


@case("P.extra-spec-import", "D1", "P4/D1", "export imports spec even when consumer modules import neither it nor ABI")
def extra_spec_import(c: Context) -> None:
    p = c.project()
    put(p, "SandboxTrial/Impl.lean", "def SandboxTrial.encode : Nat → Nat := fun n => n\n")
    put(p, "SandboxTrial/Proof.lean", "import SandboxTrial.Impl\n"
        "theorem SandboxTrial.encode_eq : SandboxTrial.encode = (fun n => n) := rfl\n")
    # D1 roots are unqualified; U7, not U5, judges the equality's type.
    built(c.phase(p))


for phase in (1, 2):
    @case(f"P.deadline.{phase}", "D1", "P1/P5/D1", "sleeping compile + small phase deadline -> infra io in requested phase, never failed")
    def _deadline(c: Context, n: int = phase) -> None:
        p = c.project()
        path = "SandboxTrial/Impl.lean" if n == 1 else "SandboxTrial/Proof.lean"
        s = (p / path).read_text()
        put(p, path, s + "\n#eval IO.sleep 30000\n")
        r = c.phase(p, "--deadline", "1" if n == 1 else "10")
        infra(r)
        need(any(w in r.all_text.lower() for w in ("deadline", "timed", "limit")), "deadline cause absent")
        if n == 1:
            need(not any(s.startswith("phase2 ") for s in r.lines), "phase 2 after deadline")
        else:
            r.line(rf"phase1 built ({HEX})")


for flag in ("frame", "export"):
    @case("P.limit." + flag, "D1", "T3/P4/P5/D1", f"--{flag}-bytes 64 -> infra io, never failed")
    def _limit(c: Context, kind: str = flag) -> None:
        r = c.phase(c.project(), f"--{kind}-bytes", "64")
        infra(r, kind)


for variant in ("base", "ordered", "reversed", "utf8", "unrelated"):
    @case("S.digest." + variant, "D1", "S2/D1/U3-H2/H3", "impl/proof hashes equal independent frame+SHA-256 oracle")
    def _digests(c: Context, kind: str = variant) -> None:
        p = c.project()
        if kind in {"ordered", "reversed"}:
            # Lean 4.35 refuses `Aux` as a module component (a reserved file name on some systems).
            put(p, "SandboxTrial/Helper.lean", "def SandboxTrial.helper : Nat := 9\n")
            mods = ["SandboxTrial.Helper", "SandboxTrial.Impl"]
            if kind == "reversed":
                mods.reverse()
            manifest_modules(p, mods, ["SandboxTrial.Proof"])
        elif kind == "utf8":
            f = p / "SandboxTrial/Impl.lean"
            f.write_text(f.read_text() + "\n-- é λ 😀: UTF-8 byte lengths, not scalar counts\n")
        elif kind == "unrelated":
            put(p, "Unlisted.lean", "this is not Lean and must not enter either digest\n")
        r = c.phase(p)
        built(r)
        impl, proof = source_digests(p)
        r.line("impl_sources " + impl)
        r.line("proof_sources " + proof)


@case("S.digest.mutation-property", "D1", "S2/D1/U3-H3", "generated comment changes exactly implSources; proofSources stays fixed")
def digest_property(c: Context) -> None:
    p = c.project()
    rng = random.Random(SEED)
    previous: str | None = None
    for i in range(4):
        put(p, "SandboxTrial/Impl.lean", (HERE / "fixtures/honest/SandboxTrial/Impl.lean").read_text()
            + f"\n-- generated {i} {rng.randbytes(16).hex()} é\n")
        r = c.phase(p)
        built(r)
        impl, proof = source_digests(p)
        r.line("impl_sources " + impl)
        r.line("proof_sources " + proof)
        need(impl != previous, "independent oracle failed to distinguish generated source bytes")
        previous = impl


for shape in ("fn", "abi"):
    @case("P.reproducible." + shape, "D1", "P7/D1", "two fresh launch-trial runs: equal e1 and phase1 artifacts; e2 qualification pair recorded")
    def _reproduce(c: Context, kind: str = shape) -> None:
        p = c.project()
        shutil.rmtree(p / "SandboxTrial")
        trial = ROOT / "tests/library/conformance"
        suffix = "Encode" if kind == "fn" else "Decode"
        for rel in (f"Conformance/{suffix}.lean", f"Conformance/Proof/{suffix}.lean"):
            put(p, rel, (trial / rel).read_bytes())
        manifest_modules(p, ["Conformance." + suffix], ["Conformance.Proof." + suffix],
                         "Conformance." + suffix + "." + suffix.lower(),
                         "Conformance.Proof." + suffix + "." + suffix.lower() + "_eq")
        if kind == "abi":
            f = p / "fvdep.toml"
            f.write_text(f.read_text().replace('shape = "fn"', 'shape = "abi"')
                         .replace('modules."base64.encode"', 'modules."base64.decode"'))
        a = c.phase(p) if kind == "fn" else c.phase(p, "--abi-module", "Fvdep.Abi.V1_0_0", "--abi",
                    "Fvdep.Abi.V1_0_0.decoder", spec_module="Fvdep.Base64.Decode.V1_0_0",
                    spec="Fvdep.Base64.Decode.V1_0_0.decode", id_="base64.decode")
        ea = built(a)
        p2 = c.home / "other-path"
        shutil.copytree(p, p2)
        b = c.phase(p2) if kind == "fn" else c.phase(p2, "--abi-module", "Fvdep.Abi.V1_0_0", "--abi",
                    "Fvdep.Abi.V1_0_0.decoder", spec_module="Fvdep.Base64.Decode.V1_0_0",
                    spec="Fvdep.Base64.Decode.V1_0_0.decode", id_="base64.decode")
        eb = built(b)
        need(ea[0] == eb[0], f"e1 differs across path-independent runs: {ea[0]}, {eb[0]}")
        need(artifacts(a, "phase1") == artifacts(b, "phase1"), "phase-1 artifact digests differ")
        # This trial's proof has no arbitrary IO. e2 equality is qualification evidence, not a P7 theorem.
        need(ea[1] == eb[1], f"launch qualification e2 pair differs: {ea[1]}, {eb[1]}")
        c.records.append({"case": c.name, "qualification": {"e1": [ea[0], eb[0]], "e2": [ea[1], eb[1]]}})


@case("P.project-unchanged", "D1", "S/P0/D1", "project sources/manifest unchanged; no build files written under project")
def project_unchanged(c: Context) -> None:
    p = c.project()
    before = {str(f.relative_to(p)): f.read_bytes() for f in p.rglob("*") if f.is_file()}
    built(c.phase(p))
    after = {str(f.relative_to(p)): f.read_bytes() for f in p.rglob("*") if f.is_file()}
    need(before == after, "phase check wrote project files")


@case("P.own-toolchain", "D1", "I1/D1", "consumer lean-toolchain garbage ignored; two phases built")
def own_toolchain(c: Context) -> None:
    p = c.project()
    put(p, "lean-toolchain", "u5-nonexistent-toolchain\n")
    built(c.phase(p))


# Snapshot refusal paths: each calls the real driver first; no fixture-side negative can pass alone.
for kind in ("leaf-link", "parent-link", "proof-link", "missing", "fifo", "socket", "directory", "impl-large", "proof-large", "total-large"):
    @case("S.refuse." + kind, "D1", "S1/D1", "unsafe/oversized module -> infra io naming path; no digest/phase lines")
    def _snapshot_refusal(c: Context, variant: str = kind) -> None:
        p = c.project()
        bad = "SandboxTrial/Proof.lean" if variant.startswith("proof-") else "SandboxTrial/Impl.lean"
        path = p / bad
        sock: socket.socket | None = None
        if variant in {"leaf-link", "proof-link"}:
            target = c.home / "actual.lean"
            path.rename(target)
            path.symlink_to(target)
        elif variant == "parent-link":
            target = c.home / "actual-dir"
            (p / "SandboxTrial").rename(target)
            (p / "SandboxTrial").symlink_to(target, target_is_directory=True)
        elif variant == "missing":
            path.unlink()
        elif variant in {"fifo", "socket", "directory"}:
            path.unlink()
            if variant == "fifo":
                os.mkfifo(path)
            elif variant == "directory":
                path.mkdir()
            else:
                sock = socket.socket(socket.AF_UNIX)
                sock.bind(str(path))
        elif variant in {"impl-large", "proof-large"}:
            put(p, bad, b" " * (1024 * 1024 + 1))
        else:
            mods = []
            for i in range(17):
                mod = f"SnapshotFill.M{i:02}"
                mods.append(mod)
                put(p, mod.replace(".", "/") + ".lean", b" " * (1024 * 1024))
            manifest_modules(p, mods, ["SandboxTrial.Proof"])
            bad = "SnapshotFill/"
        try:
            infra(c.phase(p), bad, no_phases=True)
        finally:
            if sock is not None:
                sock.close()


@case("S.boundary.file", "D1", "S1/T3/D1", "exactly 1 MiB valid source accepted, not off-by-one refusal")
def source_file_boundary(c: Context) -> None:
    p = c.project()
    f = p / "SandboxTrial/Impl.lean"
    source = f.read_bytes()
    put(p, "SandboxTrial/Impl.lean", source + b" " * (1024 * 1024 - len(source)))
    built(c.phase(p))


@case("S.boundary.total", "D1", "S1/T3/D1", "exactly 16 MiB total (including proof) accepted")
def source_total_boundary(c: Context) -> None:
    p = c.project()
    proof_size = (p / "SandboxTrial/Proof.lean").stat().st_size
    mods = ["SandboxTrial.Impl"]
    for i in range(15):
        mod = f"SnapshotFill.M{i:02}"
        mods.append(mod)
        s = f"def snapshotValue{i:02} : Nat := {i}\n".encode()
        n = 1024 * 1024 - (proof_size if i == 14 else 0)
        put(p, mod.replace(".", "/") + ".lean", s + b" " * (n - len(s)))
    source = (p / "SandboxTrial/Impl.lean").read_bytes()
    put(p, "SandboxTrial/Impl.lean", source + b" " * (1024 * 1024 - len(source)))
    manifest_modules(p, mods, ["SandboxTrial.Proof"])
    built(c.phase(p))


for variant in ("missing-import", "cycle", "header", "external-proof"):
    @case("P.graph." + variant, "D1", "K2/S2/P5/D1", "consumer graph refusal -> phase failed, exit 1; no later phase")
    def _graph(c: Context, kind: str = variant) -> None:
        p = c.project()
        n = 1
        if kind == "missing-import":
            put(p, "SandboxTrial/Impl.lean", "import U5MissingDependency\n")
        elif kind == "cycle":
            put(p, "SandboxTrial/Impl.lean", "import SandboxTrial.Aux\n")
            put(p, "SandboxTrial/Aux.lean", "import SandboxTrial.Impl\n")
            manifest_modules(p, ["SandboxTrial.Impl", "SandboxTrial.Aux"], ["SandboxTrial.Proof"])
        elif kind == "header":
            put(p, "SandboxTrial/Impl.lean", "import\n")
        else:
            put(p, "External.lean", "def externalValue : Nat := 1\n")
            put(p, "SandboxTrial/Proof.lean", "import External\n")
            n = 2
        r = c.phase(p)
        phase_failed(r, n)


# D3: synthetic libraries are independent of the launch bodies; closure membership comes from imports.
def graph_library(c: Context) -> tuple[Path, list[str]]:
    p = c.library()
    modules = ["Fvdep.CacheTrial.Shared", "Fvdep.CacheTrial.Left", "Fvdep.CacheTrial.Right", "Fvdep.CacheTrial.Unrelated"]
    put(p, "Fvdep/CacheTrial/Shared.lean", "def cacheShared : Nat := 10\n")
    for name in ("Left", "Right"):
        put(p, f"Fvdep/CacheTrial/{name}.lean", "import Fvdep.CacheTrial.Shared\n"
            f"def cache{name} : Nat := cacheShared + 1\n")
    put(p, "Fvdep/CacheTrial/Unrelated.lean", "def cacheUnrelated : Nat := 8\n")
    return p, modules


def cache_build(c: Context, lib: Path, roots: list[str], **kwargs: Any) -> Result:
    return c.call(["cache", "build", str(lib), *roots], **kwargs)


def cache_list(c: Context) -> dict[str, tuple[int, str]]:
    r = c.call(["cache", "list"])
    r.code(0)
    found: dict[str, tuple[int, str]] = {}
    for s in r.lines:
        m = re.fullmatch(rf"({HEX}) ([0-9]+) ([A-Za-z_][A-Za-z0-9_'.]*)", s)
        need(m is not None, f"malformed cache list line {s!r}")
        assert m is not None
        need(m[1] not in found, "duplicate cache key")
        found[m[1]] = (int(m[2]), m[3])
    return found


def trace(c: Context, lib: Path, roots: list[str], name: str) -> list[tuple[str, str]]:
    path = c.home / (name + ".trace")
    path.write_text("")
    r = cache_build(c, lib, roots, env={"FVDEP_BUILD_TRACE": str(path)})
    r.code(0)
    need(path.is_file(), "build trace not created")
    found = []
    for s in path.read_text().splitlines():
        m = re.fullmatch(rf"({HEX}) (.+)", s)
        need(m is not None, f"malformed trace {s!r}")
        assert m is not None
        found.append((m[1], m[2]))
    return found


@case("K.closure", "D3", "K2/K7/D3", "each needed module compiled once, dependency first; unneeded omitted")
def cache_closure(c: Context) -> None:
    p, ms = graph_library(c)
    rows = trace(c, p, [ms[1], ms[2]], "cold")
    names = [m for _, m in rows]
    need(Counter(names) == Counter(ms[:3]), f"wrong compiled closure: {names}")
    need(names.index(ms[0]) < names.index(ms[1]) and names.index(ms[0]) < names.index(ms[2]),
         "dependent compiled before shared import")
    entries = cache_list(c)
    need({m for _, m in entries.values()} == set(ms[:3]), "cache list differs from needed closure")
    for key, (n, _) in entries.items():
        d = c.cache / "build/v1/entries" / key
        counted = sum(f.stat().st_size for f in d.rglob("*") if f.is_file() and f.name != "used")
        need(n == counted, f"entry charge {n} excludes artifacts or manifest: {counted}")


@case("K.repeat", "D3", "K7/D3", "same closure second command compiles zero modules")
def cache_repeat(c: Context) -> None:
    p, ms = graph_library(c)
    need(trace(c, p, [ms[1]], "cold"), "cold build compiled nothing")
    need(trace(c, p, [ms[1]], "warm") == [], "warm identical closure recompiled")


@case("K.pin-move", "D3", "K1/K7/D3", "new git commit + unchanged needed closure compiles zero")
def pin_move(c: Context) -> None:
    p, ms = graph_library(c)
    subprocess.run(["git", "init", "-q", str(p)], check=True)
    for args in (["config", "user.email", "fixture@example.invalid"],
                 ["config", "user.name", "Fixture"], ["add", "."], ["commit", "-qm", "first"]):
        subprocess.run(["git", "-C", str(p), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    need(trace(c, p, [ms[1]], "first"), "first pin compiled nothing")
    put(p, "NOTES", "unrelated pin move\n")
    for args in (["add", "."], ["commit", "-qm", "unrelated pin move"]):
        subprocess.run(["git", "-C", str(p), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    need(trace(c, p, [ms[1]], "second") == [], "identical needed closure rebuilt after pin move")


@case("K.shared-change", "D3", "K1/K7/D3", "shared source change recompiles shared+dependents alone")
def shared_change(c: Context) -> None:
    p, ms = graph_library(c)
    before = trace(c, p, ms, "before")
    need(Counter(m for _, m in before) == Counter(ms), "cold graph incomplete")
    put(p, "Fvdep/CacheTrial/Shared.lean", "def cacheShared : Nat := 11\n")
    after = trace(c, p, ms, "after")
    need(Counter(m for _, m in after) == Counter(ms[:3]), f"wrong invalidated set {after}")
    old = dict((m, k) for k, m in before)
    need(all(k != old[m] for k, m in after), "changed closure kept a stale key")


@case("K.comment-change", "D3", "K1/K7/D3", "byte-only source change invalidates module+dependents")
def comment_change(c: Context) -> None:
    p, ms = graph_library(c)
    trace(c, p, [ms[1]], "before")
    f = p / "Fvdep/CacheTrial/Shared.lean"
    f.write_text(f.read_text() + "\n-- bytes are keyed, not elaborated meaning\n")
    after = trace(c, p, [ms[1]], "after")
    need(Counter(m for _, m in after) == Counter(ms[:2]), f"comment did not rekey needed closure {after}")


for kind in ("cycle", "missing", "header", "compile"):
    @case("K.library-refusal." + kind, "D3", "K2/K3/D3", "bad library graph/fill -> exit 2, never consumer failed")
    def _lib_refusal(c: Context, variant: str = kind) -> None:
        p, ms = graph_library(c)
        cache_build(c, p, [ms[1]]).code(0)
        if variant == "cycle":
            put(p, "Fvdep/CacheTrial/Shared.lean", "import Fvdep.CacheTrial.Left\n")
        elif variant == "missing":
            put(p, "Fvdep/CacheTrial/Shared.lean", "import Fvdep.CacheTrial.Absent\n")
        elif variant == "header":
            put(p, "Fvdep/CacheTrial/Shared.lean", "import\n")
        else:
            put(p, "Fvdep/CacheTrial/Shared.lean", "def broken := u5_missing_library_value\n")
        r = cache_build(c, p, [ms[1]])
        r.code(2)
        need(bool(r.all_text.strip()), "library failure has no diagnostic")
        need("phase1 failed:" not in r.all_text, "library input became consumer refusal")


for kind in ("json", "schema", "key", "missing-artifact", "digest", "size", "extra", "missing-used"):
    @case("K.corrupt." + kind, "D3", "K3/K6/D3", "corrupt cache entry treated as miss; rebuild succeeds and revalidates")
    def _corrupt(c: Context, variant: str = kind) -> None:
        p, ms = graph_library(c)
        trace(c, p, [ms[0]], "control")
        entries = cache_list(c)
        key = next(k for k, (_, m) in entries.items() if m == ms[0])
        d = c.cache / "build/v1/entries" / key
        manifest = d / "manifest.json"
        data = json.loads(manifest.read_text())
        arts = [f for f in d.rglob("*") if f.is_file() and f.name not in {"manifest.json", "used"}]
        need(arts, "control entry has no artifacts")
        if variant == "json":
            manifest.write_text("{")
        elif variant in {"schema", "key"}:
            data[variant] = 99 if variant == "schema" else "0" * 64
            manifest.write_text(json.dumps(data))
        elif variant == "missing-artifact":
            arts[0].unlink()
        elif variant == "digest":
            b = arts[0].read_bytes()
            need(bool(b), "cannot plant a same-size digest error in an empty artifact")
            arts[0].write_bytes(bytes([b[0] ^ 1]) + b[1:])
        elif variant == "size":
            with arts[0].open("ab") as f:
                f.write(b"extra")
        elif variant == "extra":
            put(d, "unexpected", b"unlisted artifact")
        else:
            (d / "used").unlink()
        after = trace(c, p, [ms[0]], "repair")
        need([m for _, m in after] == [ms[0]], f"corrupt entry was reused: {after}")
        need(key in cache_list(c), "repaired entry not valid/listed")
        need(trace(c, p, [ms[0]], "warm") == [], "repair did not publish an intact entry")


@case("K.module-family", "D3", "K3/K6/P2/D3", "module-header cache entry retains all 7 parts; absent private part is a rebuildable miss")
def cache_module_family(c: Context) -> None:
    p = c.library()
    module = "Fvdep.CacheTrial.Modern"
    put(p, "Fvdep/CacheTrial/Modern.lean", "module\n\npublic def modernCacheValue : Nat := 1\n")
    trace(c, p, [module], "cold")
    key = next(iter(cache_list(c)))
    d = c.cache / "build/v1/entries" / key
    actual = [f for f in d.rglob("*") if f.is_file() and f.name not in {"manifest.json", "used"}]
    need(len(actual) == len(family(module, True)), f"cache artifact count differs: {actual}")
    for path in family(module, True):
        need(sum(f.as_posix().endswith("/" + path) for f in actual) == 1, f"cache missing/duplicating {path}")
    private = next(f for f in actual if f.as_posix().endswith("/Modern.olean.private"))
    private.unlink()
    need([m for _, m in trace(c, p, [module], "repair")] == [module], "missing private artifact reused")


@case("K.used-stamp", "D3", "K5/D3", "warm use explicitly advances used mtime without changing immutable manifest")
def used_stamp(c: Context) -> None:
    p, ms = graph_library(c)
    trace(c, p, [ms[0]], "cold")
    key = next(iter(cache_list(c)))
    d = c.cache / "build/v1/entries" / key
    before = (d / "manifest.json").read_bytes()
    os.utime(d / "used", ns=(1_000_000_000, 1_000_000_000))
    need(trace(c, p, [ms[0]], "warm") == [], "stamp-only change recompiled entry")
    need((d / "used").stat().st_mtime_ns > 1_000_000_000, "warm use did not advance explicit used stamp")
    need((d / "manifest.json").read_bytes() == before, "warm use modified immutable manifest")


@case("K.single-flight", "D3", "K3/K7/D3", "two simultaneous fills of same closure compile each module exactly once")
def single_flight(c: Context) -> None:
    from concurrent.futures import ThreadPoolExecutor
    import threading
    p, ms = graph_library(c)
    barrier = threading.Barrier(2)

    def fill(name: str) -> list[tuple[str, str]]:
        barrier.wait(timeout=20)
        return trace(c, p, [ms[1], ms[2]], name)

    with ThreadPoolExecutor(max_workers=2) as pool:
        a, b = list(pool.map(fill, ("concurrent-a", "concurrent-b")))
    need(Counter(m for _, m in a + b) == Counter(ms[:3]), f"duplicate/missing single-flight work: {a + b}")
    need({m for _, m in cache_list(c).values()} == set(ms[:3]), "concurrent publication left invalid entries")


@case("K.stale-temp", "D3", "K3/D3", "miss reclaims abandoned free-key fill temp and publishes intact entry")
def stale_temp(c: Context) -> None:
    p, ms = graph_library(c)
    trace(c, p, [ms[0]], "cold")
    key = next(iter(cache_list(c)))
    shutil.rmtree(c.cache / "build/v1/entries" / key)
    stale = c.cache / "build/v1/tmp" / (key + ".2147483646.0")
    stale.mkdir(parents=True)
    put(stale, "partial", b"abandoned fill")
    need([m for _, m in trace(c, p, [ms[0]], "refill")] == [ms[0]], "miss did not refill")
    need(not stale.exists(), "free-key abandoned temp not reclaimed")
    need(key in cache_list(c), "refill not published")


@case("K.lock-retained", "D3", "K3/K5/D3", "eviction leaves permanent per-key lock file")
def lock_retained(c: Context) -> None:
    p, ms = graph_library(c)
    trace(c, p, [ms[0]], "cold")
    key = next(iter(cache_list(c)))
    lock = c.cache / "build/v1/locks" / key
    need(lock.is_file(), "per-key lock absent after fill")
    c.call(["cache", "evict"], env={"FVDEP_CACHE_BYTES": "0"}).code(0)
    need(lock.is_file(), "eviction removed synchronization metadata")
    need(not cache_list(c), "zero-target cache did not evict unpinned entry")


@case("K.evict.empty", "D3", "K5/D3", "empty cache eviction reports success with zero/nothing evictable")
def evict_empty(c: Context) -> None:
    # Positive control makes the baseline's generic usage red before an empty-output assertion.
    p, ms = graph_library(c)
    cache_build(c, p, [ms[0]]).code(0)
    r = c.call(["cache", "evict"], env={"FVDEP_CACHE_BYTES": "0"})
    r.code(0)
    r.line(r"evicted [0-9]+|nothing evictable")
    need(cache_list(c) == {}, "zero-target unpinned cache still holds entries")
    again = c.call(["cache", "evict"], env={"FVDEP_CACHE_BYTES": "0"})
    again.code(0)
    again.line(r"evicted 0|nothing evictable")


@case("K.evict.lru", "D3", "K5/D3", "small target evicts least-used first, key breaks ties, exact charge target")
def evict_lru(c: Context) -> None:
    p, ms = graph_library(c)
    cache_build(c, p, ms).code(0)
    entries = cache_list(c)
    need(len(entries) == 4, "LRU control missing entries")
    ordered = sorted(entries)
    for i, key in enumerate(ordered):
        os.utime(c.cache / "build/v1/entries" / key / "used", ns=(1_000_000_000, (i // 2 + 1) * 1_000_000_000))
    target = sum(n for n, _ in entries.values()) - entries[ordered[0]][0]
    r = c.call(["cache", "evict"], env={"FVDEP_CACHE_BYTES": str(target)})
    r.code(0)
    r.line("evicted 1")
    need(set(cache_list(c)) == set(ordered[1:]), "eviction did not remove exactly the oldest/key-first entry")


@case("K.evict.pinned", "D3", "K3/K5/D3", "live shared lock prevents eviction; reports success; unpin makes it evictable")
def evict_pinned(c: Context) -> None:
    import fcntl
    p, ms = graph_library(c)
    cache_build(c, p, [ms[0]]).code(0)
    entries = cache_list(c)
    key = next(iter(entries))
    lock = c.cache / "build/v1/locks" / key
    with lock.open("rb") as f:
        fcntl.flock(f, fcntl.LOCK_SH)
        r = c.call(["cache", "evict"], env={"FVDEP_CACHE_BYTES": "0"})
        r.code(0)
        r.line(r"evicted 0|nothing evictable")
        need(key in cache_list(c), "eviction removed a pinned entry")
    c.call(["cache", "evict"], env={"FVDEP_CACHE_BYTES": "0"}).code(0)
    need(not cache_list(c), "unpinned entry not evicted")


# B/D4: a failure is first observed, then the bundle is consumed as external input.
for n in (1, 2):
    @case(f"B.complete.{n}", "B/D4", "B2/D1/D4", "failure creates complete schema-1 bundle; rerun repeats recorded failed step")
    def _bundle(c: Context, phase: int = n) -> None:
        p = c.project()
        rel = "SandboxTrial/Impl.lean" if phase == 1 else "SandboxTrial/Proof.lean"
        put(p, rel, "import Fvdep.Base64.Encode.V1_0_0\n\ndef broken := u5_bundle_missing\n")
        r = c.phase(p)
        phase_failed(r, phase, rel, 3, "u5_bundle_missing")
        d, status = bundle(r)
        need(status == "complete", "small failing step lost required bundle inputs")
        data = json.loads((d / "bundle.json").read_text())
        need(data.get("schema") == 1, "bundle schema is not 1")
        need(sum(f.stat().st_size for f in d.rglob("*") if f.is_file()) <= CAP, "bundle exceeds 32 MiB")
        # Change/remove the source project: rerun must use recorded inputs, not re-read the project.
        shutil.rmtree(p)
        again = c.call(["phase", "rerun", str(d)])
        again.code(1)
        need("u5_bundle_missing" in again.all_text, "rerun did not execute the recorded failing input")
        again.line(rf"phase{phase} failed: .+")
        if phase == 1:
            need(not any(s.startswith("phase2 ") for s in again.lines), "rerun ran a later phase")


@case("B.retention", "B/D4", "B2/D1", "17 failed attempts retain newest 16 bundles, each within 32MiB")
def bundle_retention(c: Context) -> None:
    p = c.project()
    put(p, "SandboxTrial/Impl.lean", "def broken := u5_retention_missing\n")
    paths = []
    for _ in range(17):
        r = c.phase(p)
        phase_failed(r, 1, message="u5_retention_missing")
        d, status = bundle(r)
        need(status == "complete", "small retention fixture yielded incomplete bundle")
        need(sum(f.stat().st_size for f in d.rglob("*") if f.is_file()) <= CAP, "retained bundle exceeds cap")
        paths.append(d)
    need(len(set(paths)) == 17, "distinct attempts reused one bundle path")
    need(not paths[0].exists() and all(d.is_dir() for d in paths[1:]), "retention did not keep newest 16")
    dirs = [d for d in (c.cache / "bundles/v1").iterdir() if d.is_dir()]
    need(set(dirs) == set(paths[1:]), "bundle store contains more/fewer than newest 16 attempts")


@case("B.incomplete", "B/D4", "B2/D4", "required artifacts >32MiB -> bounded incomplete bundle; rerun exit 2 names omissions")
def incomplete_bundle(c: Context) -> None:
    p = c.project()
    lib = c.library()
    # Copy the launch spec sources as data, then add 20 independent <1MiB library inputs.
    shutil.copytree(ROOT / "Fvdep", lib / "Fvdep", dirs_exist_ok=True)
    imports = []
    for i in range(20):
        mod = f"Fvdep.BundleFill.M{i:02}"
        imports.append(mod)
        put(lib, mod.replace(".", "/") + ".lean", f'def bundlePayload{i:02} : String := "' + "x" * 900000 + '"\n')
    proof = "\n".join("import " + m for m in imports)
    proof += "\nimport SandboxTrial.Impl\n\ndef broken := u5_bundle_missing\n"
    put(p, "SandboxTrial/Proof.lean", proof)
    r = c.phase(p, library=lib)
    phase_failed(r, 2, message="u5_bundle_missing")
    d, status = bundle(r)
    need(status == "incomplete", "oversized required view did not produce an incomplete bundle")
    need(sum(f.stat().st_size for f in d.rglob("*") if f.is_file()) <= CAP, "incomplete bundle exceeds cap")
    data = json.loads((d / "bundle.json").read_text())
    need(data.get("schema") == 1, "incomplete bundle schema is not 1")
    again = c.call(["phase", "rerun", str(d)])
    again.code(2)
    need("omitt" in again.all_text.lower() or "incomplete" in again.all_text.lower(), "rerun lacks omission cause")
    # B2 names the information, not JSON member spellings. Any omitted large input belongs
    # to this generated view; D4 must name its path rather than only saying 'incomplete'.
    need("Fvdep/BundleFill/" in again.all_text, "rerun does not name an omitted view artifact")


def seed_toolchain(parent: Path) -> None:
    """TOOLCHAIN_SEED = the toolchain record of one `cache fingerprint` run (left unset when it fails:
    each case then computes its own)."""
    global TOOLCHAIN_SEED
    cache = parent / "seed-cache"
    cache.mkdir()
    env = {k: v for k, v in os.environ.items() if not k.startswith("FVDEP_")}
    p = subprocess.run([str(DEV), "cache", "fingerprint"], env=env | {"FVDEP_CACHE": str(cache)},
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600, check=False)
    if p.returncode == 0 and (cache / "toolchains").is_dir():
        TOOLCHAIN_SEED = cache / "toolchains"
    print(f"TOOLCHAIN-SEED {'ready' if TOOLCHAIN_SEED else 'absent (exit ' + str(p.returncode) + ')'}",
          flush=True)


def coverage_text() -> str:
    return "id\tpart\tclause\texpected\n" + "".join(
        f"{c.id}\t{c.part}\t{c.clause}\t{c.expected}\n" for c in CASES)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", help="id substring (repeatable: a case matching any runs)")
    parser.add_argument("--exact", help="one exact case id")
    parser.add_argument("--coverage", action="store_true", help="print the deterministic coverage table")
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--audit", action="store_true", help="validate coverage + artifact-checker controls without fvdep")
    args = parser.parse_args()
    need(len({c.id for c in CASES}) == len(CASES), "duplicate case id")
    if args.coverage:
        print(coverage_text(), end="")
        return 0
    if args.audit:
        need((HERE / "COVERAGE.tsv").read_text() == coverage_text(), "COVERAGE.tsv differs from registered cases")
        print(f"AUDIT {len(CASES)} cases, {len(CASES)} coverage rows")
        audit_artifacts()
        return 0
    cases = args.case or [os.environ.get("FVDEP_SANDBOX_CASE", "")]
    selected = [c for c in CASES if any(s in c.id for s in cases) and (args.exact is None or c.id == args.exact)]
    need(selected, "case filter matched no cases")
    need(DEV.is_file() and BIN.is_file(), "run.sh must build fvdep-dev + fvdep before the suite")
    print(f"SEED {SEED}", flush=True)
    errors = 0
    evidence: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="fvdep-sandbox-suite-") as tmp:
        parent = Path(tmp)
        if any(c.part != "D2" for c in selected):
            seed_toolchain(parent)
        for n, spec in enumerate(selected):
            home = parent / f"case-{n:03}"
            home.mkdir()
            c = Context(home, name=spec.id)
            start = time.monotonic()
            try:
                spec.run(c)
                print("PASS " + spec.id, flush=True)
                verdict, detail = "PASS", ""
            except (AssertionError, OSError, ValueError, subprocess.SubprocessError) as e:
                errors += 1
                detail = escape(str(e))
                print(f"FAIL {spec.id}: {detail}", flush=True)
                verdict = "FAIL"
            evidence.extend(c.records)
            evidence.append({"case": spec.id, "verdict": verdict, "detail": detail,
                             "replay": f"tools/vflab-run bash tests/sandbox/run.sh --exact {spec.id}",
                             "seconds": round(time.monotonic() - start, 4)})
            shutil.rmtree(home)
    print(f"SUMMARY {len(selected)} cases; {len(selected) - errors} passed; {errors} failed", flush=True)
    if args.evidence:
        args.evidence.parent.mkdir(parents=True, exist_ok=True)
        text = "".join(json.dumps(r, sort_keys=True, ensure_ascii=True) + "\n" for r in evidence)
        # Commit portable evidence: private home paths are not needed to rerun the commands.
        text = text.replace(str(ROOT), "<repo>")
        text = text.replace(str(Path.home()), "<home>")
        text = re.sub(r"/tmp/fvdep-sandbox-suite-[^/\\\" ]+", "<tmp>", text)
        args.evidence.write_text(text)
    return min(errors, 255)


if __name__ == "__main__":
    raise SystemExit(main())
