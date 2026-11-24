"""U6 dev seam: frozen sources, independent request bytes, effects observed from outside."""
from __future__ import annotations

from collections.abc import Mapping
import hashlib
import json
import os
from dataclasses import dataclass, field
from pathlib import Path
import re
import shutil
import subprocess
import time
from typing import Any, Callable

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEV = Path(os.environ.get("FVDEP_DEV_BIN", ROOT / "tool/.lake/build/bin/fvdep-dev")).resolve()
BIN = Path(os.environ.get("FVDEP_BIN", ROOT / "tool/.lake/build/bin/fvdep")).resolve()
BASE = "9e31b4f"
SEED = int(os.environ.get("FVDEP_TEST_SEED", "5008001"))
HEX = r"[0-9a-f]{64}"
NAME = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
SPEC_MODULE = "Fvdep.Trial"
SPEC = SPEC_MODULE + ".sample"
PROFILE = "fvdep/profile/1"
PARSE_LIMITS = {"batchNodes": 2**24, "depth": 4096, "nodes": 2**22}
INIT = ("Init",)
STD = (*INIT, "Std")
LIBRARY_HEADERS = {"Fvdep": (SPEC_MODULE,), SPEC_MODULE: ()}
SIMPLE = "def a := 1\n"
PHASE_IMPL = "def ProfileTrial.impl : Nat := 1\n"
PHASE_PROOF = ("import Impl\nimport Fvdep.Trial\n"
               "theorem ProfileTrial.agrees : ProfileTrial.impl = Fvdep.Trial.sample := rfl\n")
Sources = dict[str, bytes]
Grammars = Mapping[str, tuple[str, ...]]


def need(ok: object, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def line_rule(text: str) -> str:
    return "".join({9: r"\t", 10: r"\n", 13: r"\r"}.get(n, f"\\u{n:04X}")
                   if n < 32 or 127 <= n <= 159 else ch for ch in text for n in (ord(ch),))


def lines(data: bytes) -> list[str]:
    # splitlines() would consume a leaked C1/NEL instead of checking it.
    need(not data or data.endswith(b"\n"), f"missing final LF: {data[-200:]!r}")
    result = data[:-1].decode("utf-8").split("\n") if data else []
    for line in result:
        need(line == line_rule(line), f"raw Unicode Cc in text: {line[:200]!r}")
    return result


def jtext(value: Any) -> bytes:
    # U3 J4; Python's compact sorted non-ASCII printer differs on DEL alone in this domain.
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False, sort_keys=True,
                      allow_nan=False).replace("\x7f", r"\u007f").encode()


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def put(directory: Path, name: str, data: str | bytes) -> Path:
    path = directory / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data.encode() if isinstance(data, str) else data)
    return path


def sources(data: Mapping[str, str | bytes]) -> Sources:
    return {m: s.encode() if isinstance(s, str) else s for m, s in data.items()}


def layout(root: Path, batch: Sources) -> None:
    root.mkdir(exist_ok=True)
    for module, body in batch.items():
        put(root, module_path(module), body)


def request_bytes(batch: Sources, fingerprint: str, *, role: str = "consumer",
                  library: Grammars | None = None, limits: dict[str, int] | None = None) -> bytes:
    """P5a, not derived from D1 output or the parser child's record."""
    counts = PARSE_LIMITS | {k: n for k, n in (limits or {}).items() if k in PARSE_LIMITS}
    return jtext({"library": [{"imports": list(imports), "module": m}
                              for m, imports in sorted((library or {}).items())],
                  "limits": counts,
                  "modules": [{"module": m, "path": module_path(m), "sha256": sha(body)}
                              for m, body in sorted(batch.items())],
                  "profile": PROFILE, "recipe": role + "/1", "role": role, "schema": 1,
                  "toolchain": fingerprint})


def source_digest(role: str, batch: Sources) -> str:
    """U3 H2/H3: S2 hashes the whole path/bytes frame, not just file digests."""
    def sized(b: bytes) -> bytes:
        return len(b).to_bytes(8, "big") + b

    files = sorted((module_path(m).encode(), b) for m, b in batch.items())
    return sha(sized(f"fvdep/{role}-sources/1".encode()) + len(files).to_bytes(8, "big")
               + b"".join(sized(path) + sized(body) for path, body in files))


def env_base() -> dict[str, str]:
    return {k: v for k, v in os.environ.items()
            if not k.startswith("FVDEP_") and k not in {"LEAN_PATH", "LEAN_SYSROOT"}}


@dataclass(frozen=True)
class Toolchain:
    fingerprint: str
    records: Path

    @staticmethod
    def seed(directory: Path) -> Toolchain:
        cache = directory / "seed-cache"
        result = subprocess.run([DEV, "cache", "fingerprint"], cwd=ROOT,
                                env=env_base() | {"FVDEP_CACHE": str(cache)}, input=b"",
                                capture_output=True, timeout=600, check=False)
        match = re.fullmatch(rb"fingerprint ([0-9a-f]{64})\n", result.stdout)
        assert result.returncode == 0 and match is not None, (
            f"U5 T1 fingerprint: exit {result.returncode}; stdout={result.stdout[:300]!r}; "
            f"stderr={result.stderr[:500]!r}")
        records = cache / "toolchains"
        need(records.is_dir(), "U5 T1 toolchain record absent")
        return Toolchain(match[1].decode(), records)


@dataclass(frozen=True)
class Result:
    rc: int
    out: bytes
    err: bytes
    launches: list[list[str]]
    build_trace: list[str]

    def code(self, want: int) -> None:
        need(self.rc == want, f"exit {self.rc}, expected {want}; "
             f"stdout={self.out[:280]!r}; stderr={self.err[:340]!r}")

    @property
    def output(self) -> list[str]:
        return lines(self.out)

    def usage(self, *tokens: str) -> None:
        self.code(2)
        stderr = self.err.decode()
        need(not self.out and "usage" in stderr.lower() and all(t in stderr for t in tokens),
             f"expected usage for {' '.join(tokens)} on stderr only: stdout={self.out[:200]!r}; stderr={self.err[:400]!r}")
        self.no_build(launches=0)

    def no_build(self, *, launches: int, child: bool = False) -> None:
        need(not self.build_trace, f"K7 build trace is not empty: {self.build_trace!r}")
        need(len(self.launches) == launches, f"expected {launches} sandbox launches, observed "
             f"{[step_argv(a) for a in self.launches]!r}")
        for args in self.launches:
            words = step_argv(args)
            need(not any(Path(a).name in {"lean", "leanexport"} for a in words),
                 f"compile/export despite the barrier: {words!r}")
            # D1 stages the override as fvdep-parse or retains the seam file's name (D3).
            names = {"fvdep-parse", "child.sh"} if child else {"fvdep-parse"}
            need(any(Path(a).name in names for a in words), f"not the parse step: {words!r}")


def step_argv(args: list[str]) -> list[str]:
    """U5 R1 puts the step-helper invocation after the bwrap options."""
    need("--" in args, f"no bwrap command separator: {args!r}")
    return args[args.index("--") + 1:]


def profile_lines(result: Result, batch: Sources, final: str, *, request: str | None,
                  grammars: Grammars | None = None, prefix: tuple[str, ...] = (),
                  exit_: int | None = None) -> list[str]:
    """Consume D1's ordered prefix once. With no grammar oracle, check order + shape."""
    want_rc = (0 if final == "accepted" else 1 if final.startswith("refused ") else 2)
    result.code(want_rc if exit_ is None else exit_)
    output = result.output
    initial = list(prefix) + [f"module {m} {sha(body)}" for m, body in sorted(batch.items())]
    need(output[:len(initial)] == initial, f"wrong source lines: {output[:len(initial)]!r}, expected {initial!r}")
    rest = output[len(initial):]
    want_hash = HEX if request is None else request
    need(rest and re.fullmatch(f"request {want_hash}", rest[0]),
         f"expected request {want_hash}; got {rest[:1]!r}")
    rest = rest[1:]
    grammar_lines: list[str] = []
    while rest and rest[0].startswith("grammar "):
        grammar_lines.append(rest.pop(0))
    if grammars is not None:
        want = [f"grammar {m} {' '.join(g)}" for m, g in sorted(grammars.items()) if g]
        need(grammar_lines == want, f"grammar order or contents: {grammar_lines!r}, expected {want!r}")
    else:
        names: list[str] = []
        for line in grammar_lines:
            need(re.fullmatch(rf"grammar {NAME}(?: {NAME})+", line), f"malformed grammar line: {line!r}")
            names.append(line.split()[1])
        need(set(names) <= set(batch) and names == sorted(set(names)), f"grammar module order: {names!r}")
    need(rest and rest[0] == line_rule(final), f"expected outcome {line_rule(final)!r}; got {rest[:1]!r}")
    return rest[1:]


@dataclass
class Context:
    directory: Path
    name: str
    toolchain: Toolchain
    calls: list[dict[str, Any]] = field(default_factory=list)
    cache: Path = field(init=False)

    def __post_init__(self) -> None:
        self.cache = self.directory / "cache"
        shutil.copytree(self.toolchain.records, self.cache / "toolchains")

    def library(self, name: str = "library", *, body: str = "def Fvdep.Trial.sample : Nat := 1\n") -> Path:
        root = self.directory / name
        put(root, "lean-toolchain", (ROOT / "lean-toolchain").read_bytes())
        put(root, "Fvdep.lean", f"import {SPEC_MODULE}\n")
        put(root, module_path(SPEC_MODULE), body)
        return root

    def trial(self, batch: Sources, name: str = "src") -> Path:
        src = self.directory / name
        layout(src, batch)
        return src

    def project(self, batch: Sources, modules: list[str] | None = None,
                proof: str = PHASE_PROOF) -> tuple[Path, Sources]:
        src = self.trial(batch, "project")
        proofs = sources({"Proof": proof})
        layout(src, proofs)
        names = json.dumps(list(batch) if modules is None else modules)
        put(src, "fvdep.toml", f'''schema = 1
[library]
commit = "{'0' * 40}"
[modules."trial.sample"]
version = "1.0.0"
shape = "fn"
impl_modules = {names}
proof_modules = ["Proof"]
impl = "ProfileTrial.impl"
proof = "ProfileTrial.agrees"
''')
        return src, proofs

    def proxy(self, stem: str, log: Path, fault: str, edit: tuple[Path, bytes] | None) -> Path:
        # Forward unchanged. The T1/P5c preflight controls terminate without starting a step.
        change = (str(edit[0]), edit[1]) if edit is not None else None
        real = shutil.which("bwrap")
        assert real is not None, "bwrap required by U5 T1"
        script = put(self.directory, f"{stem}-path/bwrap", f'''#!/usr/bin/python3 -I
import json, os, sys
args = sys.argv[1:]
with open({str(log)!r}, "a", encoding="utf-8") as f:
    f.write(json.dumps(args) + "\\n")
if args == ["--version"] and {fault!r} == "old-version":
    print("bubblewrap 0.7.0")
    sys.exit(0)
if args != ["--version"] and {fault!r} == "setup":
    os.write(2, b"fixture setup error \\x1b\\n")
    sys.exit(7)
edit = {change!r}
if edit is not None and any(os.path.basename(a) == "fvdep-parse" for a in args):
    with open(edit[0], "wb") as f:
        f.write(edit[1])
os.execv({real!r}, [{real!r}, *args])
''')
        script.chmod(0o700)
        return script.parent

    def call(self, argv: list[str], *, observe: bool = False, fault: str = "",
             edit: tuple[Path, bytes] | None = None) -> Result:
        label = f"call-{len(self.calls)}"
        log = self.directory / (label + "-bwrap.jsonl")
        trace = self.directory / (label + "-build.trace")
        env = env_base() | {"FVDEP_CACHE": str(self.cache), "FVDEP_BUILD_TRACE": str(trace)}
        if observe or fault or edit:
            env["PATH"] = f"{self.proxy(label, log, fault, edit)}:{env['PATH']}"
        start = time.monotonic()
        try:
            p = subprocess.run([DEV, *argv], cwd=ROOT, env=env, input=b"", capture_output=True,
                               timeout=360, check=False)
        except subprocess.TimeoutExpired as exc:
            self.calls.append({"case": self.name, "argv": [str(DEV), *argv], "exit": "harness timeout",
                               "stdout": repr(exc.stdout), "stderr": repr(exc.stderr)})
            raise AssertionError("driver exceeded harness timeout (360 s)") from exc
        calls: list[list[str]] = [json.loads(row) for row in log.read_text().splitlines()] if log.exists() else []
        r = Result(p.returncode, p.stdout, p.stderr,
                   [a for a in calls if a != ["--version"]],
                   trace.read_text().splitlines() if trace.exists() else [])
        self.calls.append({"case": self.name, "argv": [str(DEV), *argv], "exit": r.rc,
                           "stdout": r.out.decode("utf-8", "backslashreplace"),
                           "stderr": r.err.decode("utf-8", "backslashreplace"),
                           "bwrap": calls, "build_trace": r.build_trace,
                           "seconds": round(time.monotonic() - start, 4)})
        lines(r.err)
        return r

    def profile(self, src: Path, modules: list[str], *, role: str = "consumer", library: Path | None = None,
                limits: dict[str, int] | None = None, results: Path | None = None, child: Path | None = None,
                observe: bool = False, fault: str = "") -> Result:
        args = ["profile", "check", "--role", role, *options(library, limits, results, child)]
        return self.call([*args, str(src), *modules], observe=observe, fault=fault)

    def phase(self, project: Path, library: Path, *, limits: dict[str, int] | None = None,
              results: Path | None = None, child: Path | None = None, fault: str = "",
              profiled: bool = True, edit: tuple[Path, bytes] | None = None) -> Result:
        argv = ["phase", "check", str(project), "trial.sample", "--library", str(library),
                "--spec-module", SPEC_MODULE, "--spec", SPEC]
        if profiled:
            argv.extend(["--profile", *options(None, limits, results, child)])
        return self.call(argv, observe=True, fault=fault, edit=edit)

    def child(self, script: str) -> Path:
        path = put(self.directory, "child.sh", "#!/bin/sh\nset -eu\n" + script + "\n")
        path.chmod(0o700)
        return path


def options(library: Path | None, limits: dict[str, int] | None, result: Path | None,
            child: Path | None) -> list[str]:
    args = ["--library", str(library)] if library else []
    for name, n in (limits or {}).items():
        args.extend(("--limit", f"{name}={n}"))
    if result is not None:
        args.extend(("--results", str(result)))
    if child is not None:
        args.extend(("--child", str(child)))
    return args


def refusal(line: int, col: int, cause: str, module: str = "Impl") -> str:
    return f"refused {module} {line}:{col} {cause}"


def check(c: Context, batch: Sources, want: str = "accepted", *, role: str = "consumer",
          grammar: Grammars | None = None, library: Path | None = None,
          headers: Grammars | None = None, limits: dict[str, int] | None = None,
          args_order: list[str] | None = None, results: Path | None = None) -> None:
    key = sha(request_bytes(batch, c.toolchain.fingerprint, role=role, library=headers, limits=limits))
    r = c.profile(c.trial(batch), list(batch) if args_order is None else args_order, role=role, library=library,
                  limits=limits, results=results, observe=results is not None)
    rest = profile_lines(r, batch, want, request=key if library is None or headers is not None else None,
                         grammars=grammar)
    need(not rest, f"text after D1 outcome: {rest!r}")
    if results is not None:
        r.no_build(launches=0)


@dataclass(frozen=True)
class Case:
    id: str
    part: str
    clause: str
    expected: str
    run: Callable[[Context], None]


CASES: list[Case] = []


def case(id_: str, clause: str, expected: str) -> Callable[[Callable[[Context], None]], Callable[[Context], None]]:
    def register(run: Callable[[Context], None]) -> Callable[[Context], None]:
        CASES.append(Case(id_, id_.split(".", 1)[0], clause, expected, run))
        return run
    return register
