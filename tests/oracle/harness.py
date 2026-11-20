"""U5b test plumbing: local git sources, isolated caches, byte-oriented observations."""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BIN = Path(os.environ.get("FVDEP_BIN", ROOT / "tool/.lake/build/bin/fvdep")).resolve()
DEV = Path(os.environ.get("FVDEP_DEV_BIN", ROOT / "tool/.lake/build/bin/fvdep-dev")).resolve()
BASE = "3218be6"
SEED = int(os.environ.get("FVDEP_TEST_SEED", "5007001"))
TIMEOUT = 360
ROOTS = (
    "lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "FvdepPreview.lean",
    "FvdepProofs.lean", "Fvdep", "FvdepPreview", "FvdepProofs",
)
SHA1 = r"[0-9a-f]{40}"
UTC = r"[0-9]{4}-(?:0[1-9]|1[0-2])-(?:0[1-9]|[12][0-9]|3[01])T(?:[01][0-9]|2[0-3]):[0-5][0-9]:(?:[0-5][0-9]|60)Z"


def need(ok: object, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def cc_escape(s: str) -> str:
    return "".join({9: r"\t", 10: r"\n", 13: r"\r"}.get(ord(c), f"\\u{ord(c):04X}")
                   if ord(c) < 32 or 127 <= ord(c) <= 159 else c for c in s)


def text_lines(b: bytes) -> list[str]:
    # splitlines() treats raw C1/NEL as a delimiter and would hide a line-rule violation.
    if not b:
        return []
    need(b.endswith(b"\n"), f"text stream missing final LF: {b[-160:]!r}")
    lines = b[:-1].decode("utf-8").split("\n")
    for line in lines:
        need(line == cc_escape(line), f"raw Unicode Cc in text: {line[:160]!r}")
    return lines


def jtext(value: Any) -> bytes:
    """U3 J4: json.dumps at ensure_ascii=False keeps DEL raw; J4 escapes DEL."""
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False, sort_keys=True,
                      allow_nan=False).replace("\x7f", r"\u007f").encode()


def put(root: Path, name: str, data: str | bytes) -> Path:
    p = root / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data.encode() if isinstance(data, str) else data)
    return p


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class Op:
    suffix: str
    camel: str
    fn: str
    version: str = "1.0.0"

    @property
    def id(self) -> str:
        return f"trial.{self.suffix}"

    @property
    def target(self) -> str:
        return f"{self.id}@{self.version}"

    @property
    def spec(self) -> str:
        return f"Fvdep.Trial.{self.camel}.V{self.version.replace('.', '_')}"

    @property
    def entry(self) -> str:
        return self.spec.replace("Fvdep.", "Fvdep.Registry.", 1)

    @property
    def spec_path(self) -> str:
        return self.spec.replace(".", "/") + ".lean"

    @property
    def entry_path(self) -> str:
        return self.entry.replace(".", "/") + ".lean"


TRIAL = Op("weight_mix", "WeightMix", "foldPulse")
NEXT = Op("weight_mix", "WeightMix", "foldPulse", "2.0.0")
BYTES = Op("bytes_out", "BytesOut", "turnOctets")
UNITS = Op("units_out", "UnitsOut", "turnUnits")
TEXT = Op("text_out", "TextOut", "turnText")
NAT = Op("nat_step", "NatStep", "nextOdd")
INT = Op("signed_step", "SignedStep", "leanLeft")
ORDER = Op("order_step", "OrderStep", "spin")
VERSION = Op("version_out", "VersionOut", "reverseMarks")
WORK = Op("work", "Work", "crank")
FIXTURE_OPS = (TRIAL, BYTES, UNITS, TEXT, NAT, INT, ORDER, VERSION, WORK)


def argv_of(*args: str | Path) -> list[str]:
    return list(map(str, args))


def git_env() -> dict[str, str]:
    return {
        "PATH": os.environ["PATH"], "LC_ALL": "C", "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_TERMINAL_PROMPT": "0",
        "GIT_AUTHOR_NAME": "Oracle Fixture", "GIT_COMMITTER_NAME": "Oracle Fixture",
        "GIT_AUTHOR_EMAIL": "oracle@example.invalid", "GIT_COMMITTER_EMAIL": "oracle@example.invalid",
        "GIT_AUTHOR_DATE": "2026-01-02T03:04:05Z", "GIT_COMMITTER_DATE": "2026-01-02T03:04:05Z",
    }


def gitp(repo: Path, *args: str, data: bytes = b"") -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(["git", "-C", str(repo), *args], env=git_env(), input=data,
                          capture_output=True, timeout=60, check=False)


def git(repo: Path, *args: str, data: bytes = b"") -> bytes:
    result = gitp(repo, *args, data=data)
    need(result.returncode == 0, f"fixture git {args!r}: exit {result.returncode}; {result.stderr[:450]!r}")
    return result.stdout


def git_init(root: Path) -> None:
    root.mkdir(exist_ok=True)
    git(root, "init", "--quiet", "--initial-branch=main", "--object-format=sha1", "--template=")
    put(root, ".git/info/exclude", ".lake/\n")


def commit(repo: Path, note: str = "Oracle fixture") -> str:
    git(repo, "add", "--all")
    git(repo, "-c", "core.hooksPath=/dev/null", "commit", "--quiet", "--allow-empty", "-m", note)
    pin = git(repo, "rev-parse", "HEAD").decode().strip()
    need(re.fullmatch(SHA1, pin), f"fixture commit is not full SHA-1: {pin!r}")
    return pin


def add_op(root: Path, op: Op) -> None:
    put(root, op.spec_path, (HERE / "fixtures" / op.spec_path).read_bytes())
    put(root, op.entry_path, f"""import {op.spec}
import Fvdep.Registry.Types.V1

namespace {op.entry}

def entry : Fvdep.Registry.Types.V1.Module := {{
  id := \"{op.id}\"
  version := \"{op.version}\"
  spec := ``{op.spec}.{op.fn}
  obligations := []
  abi := none
  compat := none
}}

end {op.entry}
""")


def add_to_registry(root: Path, original: str, ops: tuple[Op, ...]) -> None:
    renamed, count = re.subn(r"^def modules(?=\s*:)", "def oracleFixtureBase", original, flags=re.M)
    before, sep, after = renamed.rpartition("end Fvdep.Registry")
    need(count == 1 and sep, "the launch root has no unique modules definition in Fvdep.Registry")
    imports = "".join(f"import {op.entry}\n" for op in ops)
    entries = ",\n  ".join(f"{op.entry}.entry" for op in ops)
    definition = f"def modules : List Fvdep.Registry.Types.V1.Module := oracleFixtureBase ++\n  [{entries}]\n\n"
    put(root, "Fvdep/Registry.lean", imports + before + definition + sep + after)


def read_index(source: Path) -> dict[str, Any]:
    return json.loads((source / "index.json").read_bytes())


def edit_index(source: Path, edit: Callable[[dict[str, Any]], None]) -> None:
    index = read_index(source)
    edit(index)
    put(source, "index.json", jtext(index) + b"\n")


def index_row(index: dict[str, Any], op: Op) -> dict[str, Any]:
    rows = [row for row in index["operations"] if (row["id"], row["version"]) == (op.id, op.version)]
    need(len(rows) == 1, f"fixture index: {op.target} occurs {len(rows)} times")
    return rows[0]


def refresh_digest(source: Path, op: Op) -> None:
    # E2/U4 C4/U3 H2: known fixtures import only their spec, Registry.Types, and (VersionOut) Version.
    paths = [op.entry_path, op.spec_path, "Fvdep/Registry/Types/V1.lean"]
    if op == VERSION:
        paths.append("Fvdep/Semver/Version/V1_0_0.lean")

    def length(n: int) -> bytes:
        return n.to_bytes(8, "big")

    def sized(data: bytes) -> bytes:
        return length(len(data)) + data

    body = b"".join(sized(p.encode()) + sized((source / p).read_bytes()) for p in sorted(paths))
    digest = sha(sized(b"fvdep/entry/1") + length(len(paths)) + body)
    edit_index(source, lambda index: index_row(index, op).update(digest=digest))


@dataclass(frozen=True)
class Fixture:
    root: Path
    first: str
    second: str
    toolchain: str

    @staticmethod
    def build(parent: Path) -> Fixture:
        root = parent / "fixture"
        git_init(root)
        for name in ROOTS:
            src = ROOT / name
            if src.is_dir():
                shutil.copytree(src, root / name, symlinks=True)
            elif src.is_file():
                shutil.copy2(src, root / name)
        base_registry = (root / "Fvdep/Registry.lean").read_text()
        fixture_env = dict(os.environ) | {"FVDEP_CACHE": str(parent / "index-cache"),
                                         "FVDEP_LIBRARY_URL": str(root)}

        def reindex(ops: tuple[Op, ...]) -> None:
            add_to_registry(root, base_registry, ops)
            result = subprocess.run([BIN, "index"], cwd=root, env=fixture_env, input=b"",
                                    capture_output=True, timeout=TIMEOUT, check=False)
            need(result.returncode == 0, f"fixture fvdep index: exit {result.returncode}; "
                 f"stdout={result.stdout[-700:]!r}; stderr={result.stderr[-2500:]!r}")
            index = read_index(root)
            for op in ops:
                index_row(index, op)

        for op in FIXTURE_OPS:
            add_op(root, op)
        reindex(FIXTURE_OPS)
        first = commit(root, "Oracle fixture version one")
        first_index = read_index(root)
        # Check the independent digest recipe on admitted fixture metadata, not on oracle output.
        for op in (TRIAL, TEXT, VERSION):
            refresh_digest(root, op)
            need(index_row(read_index(root), op)["digest"] == index_row(first_index, op)["digest"],
                 f"independent H2 closure disagrees with fixture index for {op.target}")
        add_op(root, NEXT)
        reindex((*FIXTURE_OPS, NEXT))
        second_index = read_index(root)
        need(all(index_row(first_index, op) == index_row(second_index, op) for op in FIXTURE_OPS),
             "adding a version changed an existing fixture identity")
        second = commit(root, "Add a different oracle operation version")
        need(first != second, "fixture history lacks its second snapshot")
        return Fixture(root, first, second, (root / "lean-toolchain").read_text().strip())

    def copy(self, into: Path, *, first: bool = False) -> Path:
        shutil.copytree(self.root, into, ignore=shutil.ignore_patterns(".lake"))
        if first:
            git(into, "reset", "--hard", self.first)
        return into


@dataclass(frozen=True)
class Result:
    rc: int
    out: bytes
    err: bytes

    def code(self, rc: int) -> Result:
        need(self.rc == rc, f"exit {self.rc}, expected {rc}; stdout={self.out[:250]!r}; stderr={self.err[:450]!r}")
        return self

    def failure(self, *patterns: str, absent: tuple[str, ...] = ()) -> Result:
        self.code(2)
        need(not self.out, f"exit 2 wrote {len(self.out)} stdout bytes: {self.out[:160]!r}")
        lines = text_lines(self.err)
        for pattern in patterns:
            need(any(re.search(pattern, line) for line in lines),
                 f"missing stderr /{pattern}/; got {self.err[:480]!r}")
        for text in absent:
            need(text not in "\n".join(lines), f"misleading diagnostic {text!r}: {self.err[:480]!r}")
        return self


@dataclass(frozen=True)
class Case:
    id: str
    part: str
    clause: str
    expected: str
    run: Callable[[Context], None]
    fixture: bool


CASES: list[Case] = []


def case(id_: str, clause: str, expected: str, *, fixture: bool = True):
    def register(run: Callable[[Context], None]) -> Callable[[Context], None]:
        CASES.append(Case(id_, id_.split(".", 1)[0], clause, expected, run, fixture))
        return run
    return register


def seed_toolchain(parent: Path) -> Path:
    cache = parent / "toolchain-seed"
    env = dict(os.environ) | {"FVDEP_CACHE": str(cache)}
    result = subprocess.run([DEV, "cache", "fingerprint"], cwd=ROOT, env=env, input=b"",
                            capture_output=True, timeout=TIMEOUT, check=False)
    need(result.returncode == 0 and re.fullmatch(rb"fingerprint [0-9a-f]{64}\n", result.stdout),
         f"toolchain seed: exit {result.returncode}; {result.stdout[:200]!r}; {result.stderr[:500]!r}")
    seed = cache / "toolchains"
    need(seed.is_dir(), "T1 toolchain record missing")
    return seed


@dataclass
class Context:
    home: Path
    name: str
    fixture: Fixture | None
    toolchain_seed: Path | None
    records: list[dict[str, Any]] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.cache = self.home / "cache"
        self.source = self.home / "source"
        self.work = self.home / "cwd"
        self.work.mkdir()
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("FVDEP_")}
        self.env.update(FVDEP_CACHE=str(self.cache), FVDEP_LIBRARY_URL=str(self.source))
        if self.toolchain_seed is not None and self.fixture is not None:
            self.cache.mkdir()
            shutil.copytree(self.toolchain_seed, self.cache / "toolchains")

    def lib(self, *, first: bool = False, into: Path | None = None) -> Path:
        fixture = self.need_fixture()
        return fixture.copy(into or self.source, first=first)

    def need_fixture(self) -> Fixture:
        assert self.fixture is not None, "case requires the fixture library"
        return self.fixture

    def project(self, directory: Path, pin: str, text: str | bytes | None = None) -> Path:
        put(directory, "fvdep.toml", text if text is not None else manifest(pin))
        return directory

    def store(self, source: Path | str | None = None) -> Path:
        anchored = os.fsencode(self.source if source is None else source)
        return self.cache / "library" / "v1" / sha(anchored)

    def head(self, source: Path | str | None = None) -> tuple[bytes, dict[str, Any]]:
        key_dir = self.store(source)
        raw = (key_dir / "head.json").read_bytes()
        obj = json.loads(raw)
        need(set(obj) == {"commit", "fetched", "schema", "source"}, f"bad L5 fields: {obj!r}")
        need(type(obj["schema"]) is int and obj["schema"] == 1, f"bad head schema: {obj!r}")
        need(obj["source"] == key_dir.name, f"wrong source key in head: {obj!r}")
        need(re.fullmatch(SHA1, obj["commit"]) and re.fullmatch(UTC, obj["fetched"]), f"bad L5 head: {obj!r}")
        # The contract fixes canonical J text; it does not specify a final file LF.
        need(raw in (jtext(obj), jtext(obj) + b"\n"), f"noncanonical head record: {raw!r}")
        return raw, obj

    def published(self, commit_: str, source: Path | str | None = None) -> Path:
        tree = self.store(source) / "trees" / commit_
        need(tree.is_dir() and not tree.is_symlink(), f"snapshot {commit_} not published")
        mark = tree / ".complete"
        need(mark.is_file() and not mark.is_symlink(), "snapshot lacks a regular .complete marker")
        return tree

    def noted(self, commit_: str, source: Path | str | None = None) -> tuple[bytes, dict[str, Any]]:
        raw, obj = self.head(source)
        need(obj["commit"] == commit_, f"head points at {obj['commit']}, expected {commit_}")
        self.published(commit_, source)
        return raw, obj

    def local_stdout(self, *args: str, data: bytes = b"", cwd: Path | None = None) -> Result:
        return self.invoke(argv_of(BIN, *args), data=data, cwd=cwd)

    def oracle_argv(self, target: str | Op, *, project: Path | None = None,
                    limits: dict[str, int] | None = None, replies: bytes | None = None) -> list[str]:
        argv = argv_of(DEV if limits is not None or replies is not None else BIN,
                       "oracle", target.target if isinstance(target, Op) else target)
        if project is not None:
            argv.extend(argv_of("--project", project))
        for field_, n in (limits or {}).items():
            argv.extend(("--limit", f"{field_}={n}"))
        if replies is not None:
            with tempfile.NamedTemporaryFile(prefix="replies-", dir=self.home, delete=False) as f:
                f.write(replies)
                argv.extend(("--replies", f.name))
        return argv

    def oracle(self, target: str | Op, data: bytes = b"", *, cwd: Path | None = None,
               project: Path | None = None, source: str | Path | None = None, limits: dict[str, int] | None = None,
               replies: bytes | None = None) -> Result:
        argv = self.oracle_argv(target, project=project, limits=limits, replies=replies)
        env = {} if source is None else {"FVDEP_LIBRARY_URL": str(source)}
        return self.invoke(argv, data=data, cwd=cwd, extra_env=env)

    def invoke(self, argv: list[str], *, data: bytes = b"", cwd: Path | None = None,
               extra_env: dict[str, str] | None = None, stdin_fd: int | None = None,
               stdout_fd: int | None = None, timeout: int = TIMEOUT) -> Result:
        cwd = cwd or self.work
        env = self.env | (extra_env or {})
        try:
            p = subprocess.run(argv, cwd=cwd, env=env, input=data if stdin_fd is None else None,
                               stdin=stdin_fd, stdout=stdout_fd if stdout_fd is not None else subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=timeout, check=False)
        except subprocess.TimeoutExpired as exc:
            self.record(argv, cwd, env, "harness timeout", exc.stdout or b"", exc.stderr or b"")
            raise AssertionError(f"driver exceeded harness timeout {timeout}s: {argv!r}") from exc
        return self.observed(argv, cwd, env, p.returncode, p.stdout or b"", p.stderr)

    def observed(self, argv: list[str], cwd: Path, env: dict[str, str], rc: int, out: bytes, err: bytes) -> Result:
        self.record(argv, cwd, env, rc, out, err)
        text_lines(err)
        return Result(rc, out, err)

    def record(self, argv: list[str], cwd: Path, env: dict[str, str], rc: int | str,
               out: bytes, err: bytes) -> None:
        self.records.append({"case": self.name, "argv": argv, "cwd": str(cwd), "exit": rc,
                             "environment": {k: v for k, v in env.items() if k.startswith("FVDEP_")},
                             "stdout": out.decode("utf-8", "backslashreplace"),
                             "stderr": err.decode("utf-8", "backslashreplace")})

    def proxy(self, name: str, before_exec: str = "") -> Path:
        """Observe real subprocess invocations; any fault is local to this case's git shim."""
        real = shutil.which(name)
        need(real is not None, f"fixture command unavailable: {name}")
        log = self.home / f"{name}.jsonl"
        script = put(self.home, f"shims/{name}", f"""#!/usr/bin/python3 -I
import json, os, sys, time

args = sys.argv[1:]
log = {str(log)!r}
real = {real!r}
fd = os.open(log, os.O_CREAT | os.O_APPEND | os.O_WRONLY, 0o600)
os.write(fd, (json.dumps(dict(argv=args, cwd=os.getcwd(), env=sorted(os.environ))) + '\\n').encode())
os.close(fd)
{before_exec}
os.execv(real, [real, *args])
""")
        script.chmod(0o700)
        self.env["PATH"] = f"{script.parent}:{os.environ['PATH']}"
        return log

    def unread_input(self, argv: list[str], expected: bytes = b"still here\n") -> Result:
        read, write = os.pipe()
        try:
            os.write(write, expected)
            result = self.invoke(argv, stdin_fd=read, timeout=60)
            os.set_blocking(read, False)
            try:
                remaining = os.read(read, len(expected) + 1)
            except BlockingIOError:
                remaining = b""
            need(remaining == expected, "resolution consumed stdin before refusing")
            return result
        finally:
            os.close(read)
            os.close(write)


def manifest(pin: str) -> str:
    return f'schema = 1\n\n[library]\ncommit = "{pin}"\n'


def proxy_entries(log: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in log.read_bytes().split(b"\n") if line] if log.exists() else []


def evals(log: Path) -> int:
    return sum("--run" in row["argv"] and any(Path(a).name == "Driver.lean" for a in row["argv"])
               for row in proxy_entries(log))


def assert_regular_644(path: Path) -> None:
    mode = path.lstat().st_mode
    need(stat.S_ISREG(mode) and stat.S_IMODE(mode) == 0o644, f"{path.name}: expected regular 0644, got {mode:o}")


def wait_until(predicate: Callable[[], bool], secs: float, what: str) -> None:
    limit = time.monotonic() + secs
    while not predicate():
        need(time.monotonic() < limit, f"timed out waiting for {what}")
        time.sleep(0.02)


def held_lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    f = path.open("wb")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        f.close()
        raise
    return f
