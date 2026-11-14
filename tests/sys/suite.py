#!/usr/bin/env python3
"""Blind F1–F6 suite: protocol invariants from the contract + B2 directives, not F code."""
from __future__ import annotations

import argparse
import csv
import errno
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shutil
import signal
import subprocess
import time
from dataclasses import dataclass, field
from typing import Any

SEED = 0xF4DE6F02
CHUNK = 1 << 20
CAP = 1 << 30
OPS = ["create", "write", "sync", "close", "openDir", "syncDir", "closeDir", "openRead", "read", "rename", "unlink", "openLock", "lock"]
CAUSES = {"errno", "retryExhausted", "noProgress", "alreadyClosed", "busy", "tempsTaken", "tooLarge"}
DRIVER_OPS = {"create", "write", "sync", "close", "drop", "syncdir", "replace", "read", "lock", "unlock", "wait"}
OLD = b"old: never a partial replacement\x00\xff"
DATA = b"0123456789abcdefg"


def jd(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def need(condition: Any, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def file_bytes(path: Path) -> bytes | None:
    try:
        return path.read_bytes()
    except FileNotFoundError:
        return None


def file_size(path: Path) -> int | None:
    try:
        return path.stat().st_size
    except FileNotFoundError:
        return None


def file_mode(path: Path) -> int | None:
    try:
        return path.stat().st_mode & 0o777
    except FileNotFoundError:
        return None


def entry_names(path: Path) -> set[str] | None:
    try:
        return {p.name for p in path.iterdir()}
    except FileNotFoundError:
        return None


@dataclass(frozen=True)
class Rule:
    op: str
    start: int = 1
    count: int = 1
    action: str = "errno"
    arg: int = 5

    def text(self) -> str:
        return f"{self.op} {self.start} {self.count} {self.action} {self.arg}\n"


@dataclass
class Case:
    id: str
    row: str
    kind: str
    p: dict[str, Any] = field(default_factory=dict)
    method: str = "example"
    notes: str = "-"


def err(op: str, cause: str = "errno", number: int | None = 5, where: str = "temp", secondary: list[tuple[str, int]] | None = None, durability: bool = False) -> dict[str, Any]:
    return {"op": op, "cause": cause, "number": number, "where": where, "secondary": secondary or [], "durability": durability}


def generic_error(op: str, number: int, repeats: int = 1) -> dict[str, Any] | None:
    if number == errno.EINTR and op not in {"close", "closeDir"}:
        return None if repeats <= 64 else err(op, "retryExhausted", None, {"openRead": "file", "read": "file", "openLock": "lock", "lock": "lock", "openDir": "dir", "syncDir": "dir", "closeDir": "dir", "rename": "target"}.get(op, "temp"), durability=op in {"openDir", "syncDir", "closeDir"})
    if op == "create" and number == errno.EEXIST:
        return None if repeats < 64 else err("create", "tempsTaken", None)
    if op == "openRead" and number == errno.ENOENT:
        return None
    if op == "lock" and number == errno.EWOULDBLOCK:
        return err(op, "busy", None, "lock")
    return err(op, "errno", number, {"openRead": "file", "read": "file", "openLock": "lock", "lock": "lock", "openDir": "dir", "syncDir": "dir", "closeDir": "dir", "rename": "target"}.get(op, "temp"), durability=op in {"openDir", "syncDir", "closeDir"})


def catalog(seed: int) -> list[Case]:
    rng = random.Random(seed)
    out: list[Case] = []
    def add(case_id: str, row: str, kind: str, method: str = "example", notes: str = "-", **p: Any) -> None:
        out.append(Case(case_id, row, kind, p, method, notes))

    # Every Linux errno slot, plus generated positive errno values, for each F logical step.
    numbers = list(range(1, 134)) + rng.sample(range(134, 4096), 5)
    for op in OPS:
        for n in numbers:
            scope = "read" if op in {"openRead", "read"} else "lock" if op in {"openLock", "lock"} else "replace"
            rules = [Rule(op, arg=n, action="posterrno" if op in {"close", "closeDir"} else "errno")]
            expected = generic_error(op, n)
            if op == "unlink":
                rules = [Rule("write", arg=5), Rule("unlink", arg=n)]
                expected = err("write", secondary=[] if n == 4 else [("unlink", n)])
            add(f"F.errno.{op}.{n}", "F6-errno", scope, "generator" if n > 133 else "oracle", rules=rules, error=expected,
                absent=(op == "openRead" and n == 2), fault=op, fault_count=1, data=b"N")

    for op in OPS:
        if op in {"close", "closeDir"}:
            add(f"F.eintr.{op}.once", "F6-eintr", "replace", "oracle", rules=[Rule(op, count=65, action="posterrno", arg=4)], error=generic_error(op, 4), fault=op, fault_count=1, data=b"N")
            continue
        for n in [64, 65]:
            scope = "read" if op in {"openRead", "read"} else "lock" if op in {"openLock", "lock"} else "replace"
            rules = [Rule(op, count=n, arg=4)]
            expected = generic_error(op, 4, n)
            if op == "unlink":
                rules = [Rule("write", arg=5), Rule("unlink", count=n, arg=4)]
                expected = err("write", secondary=[] if n == 64 else [("unlink", 4)])
            add(f"F.eintr.{op}.{n}", "F6-eintr", scope, "oracle", rules=rules, error=expected, fault=op, fault_count=n, data=b"N")
    for op, scope in [("write", "writer"), ("read", "read")]:
        rules = [Rule(op, count=64, arg=4), Rule(op, start=65, action="short", arg=1), Rule(op, start=66, count=64, arg=4)]
        add(f"F.reset.{op}", "F6-budget-reset", scope, "oracle", rules=rules, error=None, data=DATA, initial=DATA, resets=True)
    add("F.eintr.new-temp-budget", "F6-eintr", "replace", "oracle", rules=[Rule("create", count=64, arg=4), Rule("create", start=65, arg=17), Rule("create", start=66, count=64, arg=4)], error=None, data=b"N")
    add("F.eintr.lock-step-budget", "F6-eintr", "lock", "oracle", rules=[Rule("openLock", count=64, arg=4), Rule("lock", count=64, arg=4)], error=None, data=b"N")

    add("F.write.zero-nonempty", "F6-noprogress", "replace", rules=[Rule("write", action="zero", arg=0)], error=err("write", "noProgress", None), data=DATA)
    add("F.write.overreported", "F6-noprogress", "replace", rules=[Rule("write", action="over", arg=1)], error="any", data=DATA)
    add("F.write.zero-empty", "F6-noprogress", "replace", rules=[], error=None, data=b"")
    for present in [False, True]:
        for after in [False, True]:
            for at in range(1, 9):
                add(f"F.crash.{int(present)}.{int(after)}.{at}", "F6-crash-present" if present else "F6-crash-absent", "crash", "oracle", present=present, after=after, at=at, data=b"N")
    for action in ["errno", "posterrno"]:
        add(f"F.rename.{action}", "F6-rename-fail", "replace", rules=[Rule("rename", action=action, arg=5)], error=err("rename", where="target", secondary=[("unlink", 2)] if action == "posterrno" else []), data=b"N", committed=(action == "posterrno"))
    add("F.rename.unlink-secondary", "F6-rename-fail", "replace", rules=[Rule("rename", arg=5), Rule("unlink", arg=13)], error=err("rename", where="target", secondary=[("unlink", 13)]), data=b"N")
    for op in ["openDir", "syncDir", "closeDir"]:
        add(f"F.durability.{op}", "F6-durability", "replace", rules=[Rule(op, action="posterrno" if op == "closeDir" else "errno", arg=5)], error=generic_error(op, 5), data=b"N")
    for n in [1, 2, 63, 64]:
        add(f"F.temps.taken.{n}", "F6-temps", "replace", "oracle", foreign=n, rules=[], error=err("create", "tempsTaken", None) if n == 64 else None, data=b"N")
    add("F.temp.symlink", "F6-symlink", "replace", foreign=1, foreign_symlink=True, rules=[], error=None, data=b"N")
    add("F.target.symlink", "F6-symlink", "replace", target_symlink=True, rules=[], error=None, data=DATA)
    for primary in ["write", "sync", "close", "rename"]:
        for close_err, unlink_err in [(0, 0), (13, 0), (0, 28), (13, 28)]:
            if primary == "close" and close_err:
                continue
            rules = [Rule(primary, action="posterrno" if primary == "close" else "errno", arg=5)]
            secondary = []
            if close_err:
                rules.append(Rule("close", action="posterrno", arg=close_err))
                secondary.append(("close", close_err))
            if unlink_err:
                rules.append(Rule("unlink", arg=unlink_err))
                secondary.append(("unlink", unlink_err))
            expected = err(primary, where="target" if primary == "rename" else "temp", secondary=secondary)
            notes = "-"
            if primary == "rename" and close_err:
                expected = err("close", number=close_err, secondary=[("unlink", unlink_err)] if unlink_err else [])
                notes = "B3-5: pre-rename close fails; rename rule is not reached"
            add(f"F.cleanup.{primary}.{close_err}.{unlink_err}", "F6-cleanup", "replace", "oracle", notes, rules=rules, error=expected, data=DATA)

    for n in [0, 1, 55, 64, 65, 4095, 4096, CHUNK - 1, CHUNK, CHUNK + 1]:
        initial = bytes(i % 256 for i in range(n))
        add(f"F.read.size.{n}", "F6-read", "read", "oracle", initial=initial, rules=[], error=None)
    add("F.read.absent", "F6-read", "read", absent=True, rules=[], error=None)
    add("F.read.short", "F6-read", "read", initial=DATA, rules=[Rule("read", count=1000, action="short", arg=1)], error=None)
    add("F.read.zero-eof", "F6-read", "read", initial=DATA, rules=[Rule("read", action="zero", arg=0)], error=None, read_expected=b"")
    add("F.read.prefix-then-error", "F6-read", "read", initial=DATA, rules=[Rule("read", action="short", arg=2), Rule("read", start=2, arg=5)], error=err("read", where="file"))
    add("F.read.primary-secondary", "F6-read", "read", initial=DATA, rules=[Rule("read", arg=5), Rule("close", action="posterrno", arg=13)], error=err("read", where="file", secondary=[("close", 13)]))
    add("F.read.close-error", "F6-read", "read", initial=DATA, rules=[Rule("close", action="posterrno", arg=5)], error=err("close", where="file"))
    add("F.read.symlink", "F6-read", "read", initial=DATA, symlink=True, rules=[], error=None)
    for n in [CAP, CAP + 1]:
        add(f"F.read.cap.{n}", "F6-read", "read-size", "oracle", virtual=n, rules=[Rule("read", count=2**32 - 1, action="virtual", arg=n)], error=None if n == CAP else err("read", "tooLarge", None, "file"))

    for mode in ["release", "exit", "alias"]:
        add(f"F.lock.contention.{mode}", "F6-lock", "contention", mode=mode)
    add("F.lock.first-refusal", "F6-lock", "lock", rules=[Rule("lock", arg=errno.EWOULDBLOCK)], error=err("lock", "busy", None, "lock"), data=b"N", first_refusal=True)
    add("F.lock.value", "F6-lock", "lock-extra", operation="lock-count", rules=[], error=None)
    add("F.lock.exception", "F6-lock", "lock-extra", operation="lock-throw", rules=[], error=None)
    add("F.lock.exception-close", "F6-lock", "lock-extra", operation="lock-throw", rules=[Rule("close", action="posterrno", arg=5)], error=None)
    for op in ["openLock", "lock"]:
        for n in [5, 13, 28]:
            add(f"F.lock.fail.{op}.{n}", "F6-lock-fail", "lock", rules=[Rule(op, arg=n)], error=generic_error(op, n), data=b"N")
    add("F.lock.primary-secondary", "F6-lock-fail", "lock", rules=[Rule("lock", arg=5), Rule("close", action="posterrno", arg=13)], error=err("lock", where="lock", secondary=[("close", 13)]), data=b"N")
    add("F.lock.close-error", "F6-lock-fail", "lock", "oracle", "B2-8: act result survives lock close failure", rules=[Rule("close", start=2, action="posterrno", arg=5)], error=None, data=b"N")

    for n in [0, 1, 64, 65, 4096]:
        add(f"F.writer.basic.{n}", "F6-writer", "writer", rules=[], error=None, data=bytes(i % 256 for i in range(n)))
    for n in [0, 1]:
        add(f"F.writer.closed.{n}", "F6-writer", "lifecycle", variant="closed", n=n)
    add("F.writer.finalizer", "F6-writer", "lifecycle", variant="drop")
    for i in range(8):
        add(f"F.writer.race.{i}", "F6-writer", "race", "generator")
    for mode in ["guard-live", "guard-closed", "guard-reuse", "guard-mutex"]:
        add(f"F.guard.{mode}", "F6-writer", "guard", operation=mode, rules=[])
    add("F.guard.finalizer-eintr", "F6-writer", "guard", operation="guard-live", rules=[Rule("close", action="posterrno", arg=4)])

    names = ["", ".", "..", ".fvdep-writer.lock", "/", "a/b", "\0", "a\0b", "a", "a b", "a\\b", "...", ".hidden", "é", "😀", "\n", "\x7f", "a" * 255, "a" * 256, "x" * 4097]
    for i, value in enumerate(names):
        add(f"F.types.named.{i}", "F6-names", "types", "oracle", path=value, name=value, mode=420)
    alphabet = list("ab09 /._-\\") + ["\0", "\n", "é", "😀", "￾"]
    for i in range(128):
        value = "".join(rng.choice(alphabet) for _ in range(rng.randrange(0, 40)))
        add(f"F.types.generated.{i}", "F6-names", "types", "generator", path=value, name=value, mode=rng.randrange(0, 1024))
    for n in list(range(513)) + [1024, 65535, 2**32, 2**64, 10**100]:
        add(f"F.types.mode.{n}", "F6-names", "types", "oracle", path="valid", name="valid", mode=n)
    for n in ["", "-1", "+1", "1.0", "1e2", " 1", "1 ", "١", "0x10", "1a"]:
        add(f"F.usage.count.{len(out)}", "F6-names", "usage", args=["replace", "$dir", "target", n])
    for m in ["", "8", "888", "0777", "-1", "+7", "0o644", " 7", "7777"]:
        add(f"F.usage.mode.{len(out)}", "F6-names", "usage", args=["create", "$file", m])
    for n in ["", ".", "..", ".fvdep-writer.lock", "a/b"]:
        add(f"F.usage.name.{len(out)}", "F6-names", "usage", args=["replace", "$dir", n, "0"])
    for args in [[], ["write", "0"], ["sync"], ["close"], ["drop"], ["unlock"], ["create"], ["replace", "$dir", "target"], ["read", "$dir"], ["bogus"]]:
        add(f"F.usage.state.{len(out)}", "F6-names", "usage", args=args)
    add("F.usage.create-occupied", "F6-names", "usage-state", variant="create")
    add("F.usage.nested-lock", "F6-names", "usage-state", variant="lock")
    add("F.usage.early-stdin", "F6-names", "usage-state", variant="stdin")
    for m in ["0", "007", "600", "644", "777"]:
        add(f"F.grammar.mode.{m}", "F6-names", "writer", mode=m, rules=[], error=None, data=b"")
    for n in ["0", "00", "0001", "01", "17"]:
        add(f"F.grammar.count.{n}", "F6-names", "replace", count=n, rules=[], error=None, data=bytes(range(int(n))))

    for op in ["create", "write", "sync", "close", "drop", "syncdir", "replace", "read", "lock", "unlock", "wait"]:
        add(f"F.records.{op}", "F6-records", "records", operation=op)
    for fs in ["gate", "zfs"]:
        add(f"F.filesystem.{fs}", "F6-fs", "filesystem", filesystem=fs)
    for i, component in enumerate(["é space😀", 'quote"backslash\\line\n']):
        add(f"F.filesystem.path.{i}", "F6-names", "filesystem", filesystem="gate", component=component)

    for op in OPS:
        add(f"F.shim.{op}.ok", "F6-shim", "shim", "oracle", operation=op, rules=[], number=None)
        for n in [4, 5, 9, 13, 17, 28, 133, 4095]:
            add(f"F.shim.{op}.errno.{n}", "F6-shim", "shim", "oracle", operation=op, rules=[Rule(op, action="posterrno" if op in {"close", "closeDir"} else "errno", arg=n)], number=n)
    for offset, count in [(0, 0), (0, 1), (1, 3), (55, 1), (63, 2), (255, 1), (256, 0), (257, 0), (255, 2), (2**64 - 1, 1), (1, 2**64 - 1)]:
        add(f"F.shim.bounds.{offset}.{count}", "F6-shim", "shim", "oracle", operation="write", offset=offset, count=count, rules=[], number=22 if offset > 256 or count > 256 - min(offset, 256) else None)
    for op in OPS:
        add(f"F.san.{op}", "F6-sanitizers", "shim", "oracle", operation=op, rules=[], number=None, sanitized=True)
    for mode in ["guard-live", "guard-closed", "guard-reuse", "guard-mutex"]:
        add(f"F.san.{mode}", "F6-sanitizers", "guard", operation=mode, rules=[], sanitized=True)
    for offset, count in [(0, 0), (1, 255), (256, 0), (255, 2), (2**64 - 1, 1), (1, 2**64 - 1)]:
        add(f"F.san.bounds.{offset}.{count}", "F6-sanitizers", "shim", "oracle", operation="write", offset=offset, count=count, rules=[], number=22 if offset > 256 or count > 256 - min(offset, 256) else None, sanitized=True)
    # MAIN, U3 close (survivor D4: the count guard removed): `String.toNat?` accepts `_` separators ⇒
    # N = decimal digits (contract F6) needs the bytes such a count would read.
    for args in [["replace", "$dir", "target", "1_0"], ["create", "$file", "write", "1_0"]]:
        add(f"F.usage.separator.{args[2] if args[0] == 'create' else args[0]}", "F6-names", "usage", args=args, stdin=bytes(10))
    need(len({c.id for c in out}) == len(out), "duplicate case ids")
    return out


@dataclass
class Event:
    seq: int
    op: str
    index: int
    fd: int
    flags: int
    count: int
    ret: int
    number: int
    action: str
    path: str
    aux: str


def trace(path: Path) -> list[Event]:
    try:
        text = path.read_text(encoding="ascii")
    except FileNotFoundError:
        return []
    out = []
    for line in text.splitlines():
        xs = line.split("\t")
        need(len(xs) == 11, "interposer trace protocol")
        out.append(Event(int(xs[0]), xs[1], int(xs[2]), int(xs[3]), int(xs[4]), int(xs[5]), int(xs[6]), int(xs[7]), xs[8], bytes.fromhex(xs[9]).decode(), bytes.fromhex(xs[10]).decode()))
    need([x.seq for x in out] == list(range(1, len(out) + 1)), "trace sequence")
    return out


@dataclass
class Observation:
    root: Path
    pid: int
    rc: int
    stdout: str
    stderr: str
    events: list[Event]
    records: list[dict[str, Any]]


class Harness:
    def __init__(self, project: Path, work: Path, zfs: Path | None):
        self.project, self.work, self.zfs = project, work, zfs
        self.dev = project / "tool/.lake/build/bin/fvdep-dev"
        self.extra = project / "tests/sys/.lake/build/bin/sys-extra"
        self.native = project / "tests/sys/.build/native"
        self.sanitized = project / "tests/sys/.build/native-asan"
        self.control = project / "tests/sys/.build/control"
        self.fault = project / "tests/sys/.build/fault.so"
        self.last: dict[str, Any] = {}

    def env(self, root: Path, rules: list[Rule], preload: bool = True, channel: str = "main") -> dict[str, str]:
        ctl = root / ".control" / channel
        ctl.mkdir(parents=True, exist_ok=True)
        script, log = ctl / "script", ctl / "trace"
        script.write_text("".join(q.text() for q in rules), encoding="ascii")
        log.write_bytes(b"")
        env = {**os.environ, "FVDEP_SYS_ROOT": str(root), "FVDEP_SYS_SCRIPT": str(script), "FVDEP_SYS_TRACE": str(log),
               "LEAN_ABORT_ON_PANIC": "1", "ASAN_OPTIONS": "detect_leaks=1:abort_on_error=1", "UBSAN_OPTIONS": "halt_on_error=1:print_stacktrace=1"}
        if preload:
            env["LD_PRELOAD"] = str(self.fault)
        else:
            env.pop("LD_PRELOAD", None)
        return env

    def run(self, argv: list[str], root: Path, rules: list[Rule], data: bytes = b"", foreign: int = 0, symlink: bool = False, preload: bool = True, channel: str = "main") -> Observation:
        env = self.env(root, rules, preload, channel)
        with subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, start_new_session=True, umask=0) as child:
            if foreign:
                for i in range(foreign):
                    p = root / f".target.tmp-{child.pid}-{i}"
                    if symlink:
                        p.symlink_to(root / "victim")
                    else:
                        p.write_bytes(f"FOREIGN-{i}".encode())
            try:
                stdout, stderr = child.communicate(data, timeout=90)
            except subprocess.TimeoutExpired:
                child.kill()
                stdout, stderr = child.communicate()
                self.last = {"rc": child.returncode, "stdout": stdout.decode(errors="replace"), "stderr": stderr.decode(errors="replace"), "timeout": 90}
                raise AssertionError("INFRA: target process exceeded the harness deadline") from None
            records: list[dict[str, Any]] = []
            for line in stdout.decode(errors="replace").splitlines():
                try:
                    value = json.loads(line)
                except json.JSONDecodeError:
                    value = {"invalid_json": line}
                records.append(value)
            assert child.returncode is not None
            o = Observation(root, child.pid, child.returncode, stdout.decode(errors="replace"), stderr.decode(errors="replace"), trace(root / ".control" / channel / "trace"), records)
        self.last = observed(o)
        return o

    def devrun(self, root: Path, args: list[str], rules: list[Rule], data: bytes = b"", **kwargs: Any) -> Observation:
        return self.run([str(self.dev), "sys", "run", *args], root, rules, data, **kwargs)

    def extrarun(self, root: Path, request: dict[str, Any], rules: list[Rule]) -> Observation:
        return self.run([str(self.extra)], root, rules, (jd(request) + "\n").encode())


def observed(o: Observation) -> dict[str, Any]:
    def norm(x: Any) -> Any:
        if isinstance(x, str):
            return x.replace(str(o.root), "$CASE").replace(f".tmp-{o.pid}-", ".tmp-$PID-")
        if isinstance(x, dict):
            return {k: norm(v) for k, v in x.items()}
        if isinstance(x, (list, tuple)):
            return [norm(v) for v in x]
        return x
    events = [{"op": e.op, "index": e.index, "fd": e.fd, "count": e.count, "ret": e.ret, "errno": e.number,
               "flags": e.flags, "action": e.action, "path": e.path, "aux": e.aux} for e in o.events]
    files: list[dict[str, Any]] = []
    try:
        entries = sorted(o.root.iterdir(), key=lambda p: p.name.encode())
    except FileNotFoundError:
        entries = []
        files.append({"name": ".", "absent": True})
    for p in entries:
        if p.name == ".control":
            continue
        try:
            if p.is_symlink():
                files.append({"name": p.name, "symlink": os.readlink(p)})
            elif p.is_file():
                info = p.stat()
                content = b"" if info.st_size == 0 else file_bytes(p)
                if content is None:
                    files.append({"name": p.name, "absent": True})
                else:
                    files.append({"name": p.name, "size": info.st_size, "sha256": digest(content), "mode": info.st_mode & 0o777})
            else:
                files.append({"name": p.name, "directory": True} if p.exists() else {"name": p.name, "absent": True})
        except FileNotFoundError:
            files.append({"name": p.name, "absent": True})
    return norm({"rc": o.rc, "records": o.records, "stderr": o.stderr, "trace": events, "files": files})


def record(op: str, error: dict[str, Any] | None = None, **extra: Any) -> dict[str, Any]:
    return {"op": op, "ok": error is None, **({"error": error} if error is not None else {}), **extra}


def error_value(spec: dict[str, Any], o: Observation, name: str = "target", attempt: int = 0) -> dict[str, Any]:
    paths = {"temp": str(o.root / f".{name}.tmp-{o.pid}-{attempt}"), "target": str(o.root / name), "file": str(o.root / "file"), "dir": str(o.root), "lock": str(o.root / ".fvdep-writer.lock")}
    value: dict[str, Any] = {"op": spec["op"], "cause": spec["cause"], "path": paths[spec["where"]]}
    if spec["cause"] == "errno":
        value["errno"] = spec["number"]
    if spec["secondary"]:
        value["secondary"] = [{"op": op, "errno": n} for op, n in spec["secondary"]]
    if spec["durability"]:
        value["durability"] = True
    return value


def record_shape(value: dict[str, Any]) -> None:
    need(isinstance(value, dict) and value.get("op") in DRIVER_OPS and type(value.get("ok")) is bool, "record op/ok shape")
    if value["ok"]:
        keys = {"op", "ok", "bytes"} if value["op"] == "read" else {"op", "ok"}
        need(set(value) == keys, "success record fields")
        if value["op"] == "read":
            b = value["bytes"]
            need(b is None or (isinstance(b, str) and re.fullmatch(r"(?:[0-9a-f]{2})*", b) is not None), "read bytes lowercase hex|null")
    else:
        need(set(value) == {"op", "ok", "error"}, "failure record fields")
        e = value["error"]
        need(isinstance(e, dict) and e.get("op") in OPS and e.get("cause") in CAUSES and isinstance(e.get("path"), str), "error primary fields")
        keys = {"op", "cause", "path"}
        if e["cause"] == "errno":
            keys.add("errno")
            need(type(e.get("errno")) is int and e["errno"] >= 0, "errno Nat")
        if "secondary" in e:
            keys.add("secondary")
            need(isinstance(e["secondary"], list) and bool(e["secondary"]), "nonempty secondary list")
            for secondary in e["secondary"]:
                need(isinstance(secondary, dict) and set(secondary) == {"op", "errno"} and secondary["op"] in OPS and type(secondary["errno"]) is int and secondary["errno"] >= 0, "secondary object shape")
        if "durability" in e:
            keys.add("durability")
            need(e["durability"] is True, "durability absent or true")
        need(set(e) == keys, "no non-applicable/null/unknown error field")


def completed(o: Observation) -> None:
    need(o.rc == 0, f"completed run exit 0, got {o.rc}")
    for r in o.records:
        record_shape(r)


def group_events(o: Observation, op: str) -> list[Event]:
    return [e for e in o.events if e.op == op]


def retries(events: list[Event], progress: bool = False) -> None:
    failures = 0
    for i, e in enumerate(events):
        if e.ret < 0 and e.number == errno.EINTR:
            failures += 1
            need(failures <= 65, "retry bound")
            if failures == 65:
                need(i == len(events) - 1, "65th EINTR ends step")
        else:
            failures = 0
            if not progress or e.ret < 0 or (e.ret == 0 and e.count > 0):
                need(i == len(events) - 1, "non-EINTR failure/finished step ends the loop")
        if i + 1 < len(events) and e.ret < 0 and e.number == errno.EINTR:
            need(events[i + 1].fd == e.fd and events[i + 1].count == e.count, "EINTR retries same description/request")


def closed_once(events: list[Event], op: str = "close") -> None:
    need(len(events) == 1 and events[0].op == op, f"{op} attempted exactly once")


def create_flags(e: Event, mode: int = 0o644) -> None:
    required = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    need(e.flags & required == required and e.flags & os.O_ACCMODE == os.O_WRONLY and e.count == mode, "exclusive create flags/mode")


def replace_protocol(o: Observation, data: bytes, name: str = "target", allow_over: bool = False) -> None:
    events = o.events
    need(bool(events), "replace issued no syscall")
    at = 0
    def take(op: str) -> list[Event]:
        nonlocal at
        start = at
        while at < len(events) and events[at].op == op:
            at += 1
        return events[start:at]
    creates = take("create")
    need(bool(creates), "replace starts with exclusive temp create")
    attempt = 0
    for i, e in enumerate(creates):
        need(attempt < 64, "create never attempts temp index 64")
        need(e.path == str(o.root / f".{name}.tmp-{o.pid}-{attempt}"), "temp path/pid/attempt")
        create_flags(e)
        if e.ret < 0 and e.number == errno.EEXIST:
            attempt += 1
        elif e.ret < 0 and e.number == errno.EINTR:
            pass
        else:
            need(i == len(creates) - 1, "create stops on result")
        need(attempt <= 64, "64 temp attempts")
    got = creates[-1].ret >= 0
    if not got:
        need(at == len(events), "failed create neither closes nor unlinks a foreign temp")
        return
    temp, fd = creates[-1].path, creates[-1].ret
    writes, syncs, closes, renames = take("write"), take("sync"), take("close"), take("rename")
    opens, dirsyncs, dircloses, unlinks = take("openDir"), take("syncDir"), take("closeDir"), take("unlink")
    need(at == len(events), "replace phase order / no extra syscall")
    remaining = len(data)
    for e in writes:
        need(e.fd == fd and 0 <= e.count <= remaining, "write uses create-owned description and bounded remainder")
        if remaining:
            need(e.count > 0, "nonempty write requests positive progress")
        if e.ret >= 0:
            if e.ret > e.count:
                need(allow_over, "write never reports beyond its request")
            else:
                remaining -= e.ret
    retries(writes, progress=True)
    for e in syncs + closes:
        need(e.fd == fd, "temp sync/close uses the owned description")
    closed_once(closes)
    if syncs:
        need(remaining == 0 and all(e.ret > 0 or len(data) == 0 for e in writes if e.ret >= 0), "sync follows complete data")
        retries(syncs)
    if renames:
        need(remaining == 0 and bool(syncs) and syncs[-1].ret == 0 and closes[0].ret == 0, "rename follows successful data-sync-close")
        for e in renames:
            need(e.path == str(o.root / name) and e.aux == temp, "rename is the sole target-path touch")
        retries(renames)
    if opens:
        need(bool(renames) and renames[-1].ret == 0, "directory phase follows reported rename success")
        for e in opens:
            need(e.path == str(o.root) and e.flags & (os.O_DIRECTORY | os.O_CLOEXEC) == os.O_DIRECTORY | os.O_CLOEXEC and e.flags & os.O_ACCMODE == os.O_RDONLY, "directory open path/flags")
        retries(opens)
        if opens[-1].ret >= 0:
            dfd = opens[-1].ret
            need(bool(dirsyncs), "directory is synced")
            for e in dirsyncs + dircloses:
                need(e.fd == dfd, "directory sync/close shares its acquired description")
            retries(dirsyncs)
            closed_once(dircloses, "closeDir")
        else:
            need(not dirsyncs and not dircloses, "no directory description acquired")
    else:
        need(not dirsyncs and not dircloses, "no unopened directory use")
    if renames and renames[-1].ret == 0:
        need(bool(opens), "reported rename success reaches directory durability step")
        need(not unlinks, "reported rename success consumes the temp even on durability failure")
    if unlinks:
        for e in unlinks:
            need(e.path == temp, "only the created temp can be unlinked")
        retries(unlinks)
    elif not renames or renames[-1].ret < 0:
        need(False, "failure unlinks its create-owned temp")
    need(not any(e.path == str(o.root / name) for e in creates + writes + syncs + closes + opens + dirsyncs + dircloses + unlinks), "target is only named by rename")


def read_protocol(o: Observation) -> None:
    need(bool(o.events), "readFile issued no syscall")
    at = 0
    opens = []
    while at < len(o.events) and o.events[at].op == "openRead":
        opens.append(o.events[at]); at += 1
    need(bool(opens), "read starts with openRead")
    retries(opens)
    for e in opens:
        need(e.path == str(o.root / "file") and e.flags & os.O_CLOEXEC and e.flags & os.O_ACCMODE == os.O_RDONLY, "read open path/flags")
    if opens[-1].ret < 0:
        need(at == len(o.events), "no close for failed openRead")
        return
    reads = []
    while at < len(o.events) and o.events[at].op == "read":
        reads.append(o.events[at]); at += 1
    need(bool(reads), "readFile attempts a read")
    closes = o.events[at:]
    closed_once(closes)
    for e in reads + closes:
        need(e.fd == opens[-1].ret, "read/close uses its acquired description")
    for i, e in enumerate(reads):
        need(0 <= e.count <= CHUNK and e.ret <= e.count, "read asks at most 1 MiB")
        if e.ret == 0 or (e.ret < 0 and e.number != 4):
            need(i == len(reads) - 1, "EOF or read error ends the loop")
    retries(reads, progress=True)


def fault_reached(c: Case, o: Observation) -> None:
    if c.p.get("fault"):
        events = [e for e in o.events if e.op == c.p["fault"] and e.action in {"errno", "posterrno"}]
        need(len(events) == c.p["fault_count"], "scripted fault calls were reached exactly")


def describe(c: Case) -> dict[str, Any]:
    p = c.p
    return {"kind": c.kind, "parameters": {k: (v.hex() if isinstance(v, bytes) else [q.text().strip() for q in v] if k == "rules" else v) for k, v in p.items()}, "contract": c.row}


def short(value: Any, full: bool = False) -> str:
    text = jd(value)
    raw = text.encode()
    if full or len(raw) <= 2400:
        return text
    return f"sha256:{digest(raw)} bytes:{len(raw)} prefix:{text[:200]!r} [abbreviated]"


def extra_error(value: dict[str, Any]) -> dict[str, Any]:
    return {k: v for k, v in value.items() if not (k == "errno" and v is None) and not (k == "secondary" and not v) and not (k == "durability" and not v)}


def extra_value(o: Observation) -> dict[str, Any]:
    need(o.rc == 0 and len(o.records) == 1 and "invalid_json" not in o.records[0], "extra-driver protocol")
    return o.records[0]


def lock_protocol(o: Observation, acquired: bool, inner: bool = False, directory: Path | None = None) -> None:
    lock_dir = o.root if directory is None else directory
    events = o.events
    need(bool(events), "lock issued no syscall")
    opens = group_events(o, "openLock")
    need(bool(opens) and events[:len(opens)] == opens, "lock starts with openLock")
    for e in opens:
        need(e.path == str(lock_dir / ".fvdep-writer.lock"), "project-local permanent lock name")
        need(e.flags & (os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW) == os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW and not e.flags & os.O_EXCL and e.count == 0o644, "lock open flags/mode")
    retries(opens)
    if opens[-1].ret < 0:
        need(len(events) == len(opens), "failed lock open acquires no description")
        return
    fd = opens[-1].ret
    locks = group_events(o, "lock")
    need(bool(locks) and events[len(opens):len(opens) + len(locks)] == locks, "flock follows lock-file open")
    retries(locks)
    for e in locks:
        need(e.fd == fd and e.flags == 2 | 4, "LOCK_EX|LOCK_NB on the acquired description")
    need((locks[-1].ret == 0) == acquired, "flock acquisition outcome")
    closes = [e for e in events if e.op == "close" and e.fd == fd]
    # With an inner replace the OS may reuse the same numeric fd only after its own close;
    # the lock's still-open description prevents that reuse during the region.
    closed_once(closes)
    need(events[-1] == closes[-1], "lock description closes after the action")
    need(not any(e.op == "unlink" and e.path == str(lock_dir / ".fvdep-writer.lock") for e in events), "permanent lock is never unlinked")
    if not inner:
        need(len(events) == len(opens) + len(locks) + 1, "no unrequested lock effects")


def execute(c: Case, h: Harness, root: Path) -> None:
    p = c.p
    root.mkdir(parents=True)
    h.last = {}
    rules: list[Rule] = p.get("rules", [])
    data: bytes = p.get("data", b"N")
    if c.kind == "types":
        request = {"op": "types", "path": p["path"], "name": p["name"], "mode": p["mode"]}
        o = h.extrarun(root, request, [])
        value = extra_value(o)
        path_ok = "\0" not in p["path"]
        name_ok = bool(p["name"]) and "\0" not in p["name"] and "/" not in p["name"] and p["name"] not in {".", "..", ".fvdep-writer.lock"}
        need(value == {"path": path_ok, "name": name_ok, "mode": p["mode"] <= 511, "path_value": p["path"] if path_ok else None, "name_value": p["name"] if name_ok else None}, "Path/Name/Mode independent predicate + preservation")
        need(not o.events, "pure name checks have no syscall")
        return
    if c.kind == "replace":
        target = root / "target"
        (root / "victim").write_bytes(OLD)
        if p.get("target_symlink"):
            target.symlink_to(root / "victim")
        else:
            target.write_bytes(OLD)
        args = ["replace", str(root), "target", p.get("count", str(len(data)))]
        foreign = p.get("foreign", 0)
        payload = data
        if foreign:
            args = ["wait", *args]
            payload = b"\n" + data
        o = h.devrun(root, args, rules, payload, foreign=foreign, symlink=p.get("foreign_symlink", False))
        completed(o)
        replace_protocol(o, data, allow_over=p.get("error") == "any")
        fault_reached(c, o)
        expected = p.get("error")
        first = [record("wait")] if foreign else []
        if expected == "any":
            need(len(o.records) == len(first) + 1 and o.records[-1].get("op") == "replace" and o.records[-1].get("ok") is False, "over-reported write fails closed")
            need(o.records[-1]["error"]["op"] == "write" and o.records[-1]["error"]["path"] == str(root / f".target.tmp-{o.pid}-0"), "overreported-write failure names its step/path")
        else:
            attempt = 63 if expected and expected["cause"] == "tempsTaken" else 0
            error = error_value(expected, o, attempt=attempt) if expected else None
            need(o.records == first + [record("replace", error)], "replace result/primary/secondary/durability")
        committed = expected is None or p.get("committed") or bool(expected and expected != "any" and expected["durability"])
        need(not target.is_symlink() if committed else True, "rename replaces the target symlink itself")
        need(file_bytes(target) == (data if committed else OLD), "target exact old/new content")
        need(file_bytes(root / "victim") == OLD, "symlink victim unchanged")
        foreign_paths = {root / f".target.tmp-{o.pid}-{i}" for i in range(foreign)}
        for i, f in enumerate(sorted(foreign_paths, key=lambda x: int(x.name.rsplit("-", 1)[1]))):
            if p.get("foreign_symlink"):
                need(f.is_symlink() and f.resolve() == root / "victim", "foreign temp symlink untouched")
            else:
                need(file_bytes(f) == f"FOREIGN-{i}".encode(), "foreign temp bytes untouched")
        owned = [f for f in root.glob(".target.tmp-*") if f not in foreign_paths]
        failed_unlink = any(e.op == "unlink" and e.ret < 0 and e.number != 4 for e in o.events) or (len(group_events(o, "unlink")) == 65 and all(e.number == 4 for e in group_events(o, "unlink")))
        # A post-commit rename error can make cleanup report ENOENT without leaving a temp.
        should_remain = failed_unlink and not p.get("committed")
        need(len(owned) == int(should_remain), "owned temp cleanup / retained failed-unlink temp")
        return
    if c.kind in {"read", "read-size"}:
        file = root / "file"
        initial: bytes = p.get("initial", DATA)
        if not p.get("absent"):
            if p.get("symlink"):
                (root / "victim").write_bytes(initial)
                file.symlink_to(root / "victim")
            else:
                file.write_bytes(b"" if c.kind == "read-size" else initial)
        if c.kind == "read-size":
            o = h.extrarun(root, {"op": "read-size", "dir": str(root), "name": "file"}, rules)
            value = extra_value(o)
            expected = p.get("error")
            if expected:
                need(value.get("ok") is False and extra_error(value.get("error", {})) == error_value(expected, o), "read cap refuses with read/tooLarge and no prefix")
            else:
                n = p["virtual"]
                points = [0, n // 2, n - 1]
                need(value == {"ok": True, "size": n, "samples": [{"at": at, "value": 0} for at in points]}, "exact read cap still returns the whole value")
        else:
            o = h.devrun(root, ["read", str(root), "file"], rules)
            completed(o)
            expected = p.get("error")
            if expected:
                need(o.records == [record("read", error_value(expected, o))], "read error discards prefix and preserves close secondary")
            else:
                content = None if p.get("absent") else p.get("read_expected", initial).hex()
                need(o.records == [record("read", bytes=content)], "read exact bytes/absent/empty result")
        read_protocol(o)
        fault_reached(c, o)
        if p.get("resets"):
            need(sum(e.ret < 0 and e.number == 4 for e in o.events) == 128, "both 64-EINTR runs reached")
        if file.exists() and c.kind != "read-size":
            need(file_bytes(file) == initial, "read leaves input unchanged")
        return
    if c.kind == "writer":
        file = root / "file"
        args = ["create", str(file)] + ([p["mode"]] if "mode" in p else [])
        args += ["write", str(len(data)), "sync", "close", "drop"]
        o = h.devrun(root, args, rules, data)
        completed(o)
        need(o.records == [record(op) for op in ["create", "write", "sync", "close", "drop"]], "writer operations complete")
        need(file_size(file) == len(data), "writer size")
        if data:
            need(file_bytes(file) == data, "short writes preserve full input order")
        need(file_mode(file) == int(p.get("mode", "644"), 8), "writer mode with umask zero")
        creates = group_events(o, "create")
        need(len(creates) == 1, "writer one exclusive create")
        create_flags(creates[0], int(p.get("mode", "644"), 8))
        closed_once(group_events(o, "close"))
        need(all(e.fd == creates[0].ret for e in o.events if e.op in {"write", "sync", "close"}), "writer description identity")
        retries(group_events(o, "write"), progress=True)
        if p.get("resets"):
            need(sum(e.ret < 0 and e.number == 4 for e in o.events) == 128, "write progress resets the retry budget")
        return
    if c.kind == "lock":
        args = ["lock", str(root), "replace", str(root), "target", str(len(data)), "unlock"]
        o = h.devrun(root, args, rules, data)
        completed(o)
        expected = p.get("error")
        ran = expected is None
        if ran:
            need(any(r.get("op") == "replace" and r.get("ok") is True for r in o.records), "lock action runs")
            need(file_bytes(root / "target") == data, "lock action result")
        else:
            assert isinstance(expected, dict)
            need(o.records == [record("lock", error_value(expected, o))], "refused lock skips all inner operations and unlock")
            need(not (root / "target").exists(), "refused lock runs no action")
        if expected is None:
            need(o.records == [record("lock"), record("replace"), record("unlock")], "scoped lock records")
        acquired = ran
        lock_protocol(o, acquired, inner=ran)
        fault_reached(c, o)
        opened = group_events(o, "openLock")[-1].ret >= 0
        lockfile = root / ".fvdep-writer.lock"
        need(lockfile.exists() == opened, "lock file created iff open succeeded")
        if opened:
            need(file_bytes(lockfile) == b"", "permanent lock file empty")
        if p.get("first_refusal"):
            need(entry_names(root) == {".control", ".fvdep-writer.lock"}, "first refused writer leaves only lock metadata")
        return
    if c.kind == "lock-extra":
        o = h.extrarun(root, {"op": p["operation"], "dir": str(root)}, rules)
        value = extra_value(o)
        if p["operation"] == "lock-count":
            need(value == {"count": 1, "result": {"ok": True, "value": 37}}, "lock action exactly once + value propagation")
        else:
            need(value.get("count") == 1 and value.get("result", {}).get("threw") is True and "F6-sentinel" in value["result"].get("message", ""), "lock action exception propagates after close")
        lock_protocol(o, True)
        need(file_bytes(root / ".fvdep-writer.lock") == b"", "lock metadata retained after action/exception")
        return
    if c.kind == "lifecycle":
        file = str(root / "file")
        if p["variant"] == "drop":
            o = h.devrun(root, ["create", file, "drop"], [], b"")
            expected_records = [record("create"), record("drop")]
        else:
            o = h.devrun(root, ["create", file, "close", "write", str(p["n"]), "sync", "close", "drop"], [], b"N" * p["n"])
            e = {"op": "write", "cause": "alreadyClosed", "path": file}
            expected_records = [record("create"), record("close"), record("write", e), record("sync", {**e, "op": "sync"}), record("close", {**e, "op": "close"}), record("drop")]
        completed(o)
        need(o.records == expected_records, "closed writer causes / drop lifecycle")
        need([e.op for e in o.events] == ["create", "close"], "one close, no closed-writer syscall, finalizer close-if-open")
        need(file_size(root / "file") == 0, "closed writer never writes")
        return
    if c.kind == "race":
        o = h.extrarun(root, {"op": "writer-race", "path": str(root / "file")}, [])
        value = extra_value(o)
        need(value.get("created") is True, "race writer created")
        records = value.get("records", [])
        need(len(records) == 32 and value.get("close", {}).get("ok") is True, "all racing operations joined + one close succeeds")
        successful_writes = 0
        for r in records:
            if r.get("ok") is True:
                successful_writes += r.get("op") == "write"
            else:
                need(r.get("error", {}).get("cause") == "alreadyClosed", "race returns success or alreadyClosed, never EBADF")
        need(value.get("again", {}).get("error", {}).get("cause") == "alreadyClosed", "second close is alreadyClosed")
        need(file_bytes(root / "file") == bytes(range(256)) * successful_writes, "linearized full writes, no partial successful operation")
        closes = group_events(o, "close")
        closed_once(closes)
        need(not any(e.op in {"write", "sync"} and e.seq > closes[0].seq for e in o.events), "guard prevents syscall after close")
        return
    if c.kind == "crash":
        if p["present"]:
            (root / "target").write_bytes(OLD)
        action = "aftercrash" if p["after"] else "crash"
        o = h.devrun(root, ["replace", str(root), "target", "1"], [Rule("*", start=p["at"], action=action, arg=0)], b"N")
        need(o.rc == 99 and len(o.events) == p["at"], "every selected syscall cut is actually reached")
        logical = ["create", "write", "sync", "close", "rename", "openDir", "syncDir", "closeDir"]
        need([e.op for e in o.events] == logical[:p["at"]], "crash prefix follows F2's one-byte protocol")
        target = root / "target"
        actual = file_bytes(target) if target.exists() else None
        need(actual in {OLD if p["present"] else None, b"N"}, "crash leaves old-or-new, never partial")
        if p["at"] < 5 or (p["at"] == 5 and not p["after"]):
            need(actual == (OLD if p["present"] else None), "pre-rename crash preserves old/absent")
        if p["at"] > 5 or (p["at"] == 5 and p["after"]):
            need(actual == b"N", "post-rename process cut observes new bytes")
        for f in root.glob(".target.tmp-*"):
            need(f.name == f".target.tmp-{o.pid}-0" and file_bytes(f) in {b"", b"N"}, "interruption leaves only the create-owned temp")
        return
    if c.kind == "usage":
        substitutions = {"$dir": str(root), "$file": str(root / "file")}
        args = [substitutions.get(a, a) for a in p["args"]]
        o = h.devrun(root, args, [], p.get("stdin", b""))
        need(o.rc == 2 and bool(o.stderr) and not o.events and not o.records, "syntax/state usage stop before effects")
        return
    if c.kind == "usage-state":
        variant = p["variant"]
        if variant == "create":
            args, input_bytes = ["create", str(root / "file"), "create", str(root / "later")], b""
        elif variant == "lock":
            args, input_bytes = ["lock", str(root), "lock", str(root), "unlock", "unlock"], b""
        else:
            args, input_bytes = ["replace", str(root), "target", "2", "read", str(root), "later"], b"N"
        o = h.devrun(root, args, [], input_bytes)
        need(o.rc == 2 and bool(o.stderr), "usage state or early stdin exits 2")
        if variant == "create":
            need(o.records == [record("create")] and not (root / "later").exists(), "occupied create stops before later op")
        elif variant == "lock":
            need(o.records == [record("lock")] and len(group_events(o, "lock")) == 1, "nested lock stops and closes outer description")
            closed_once(group_events(o, "close"))
        else:
            need(not o.events and not o.records and not (root / "target").exists(), "early stdin never runs replace/later op")
        return
    if c.kind == "shim":
        op = p["operation"]
        assert isinstance(op, str)
        initial = bytes(range(256)) if op != "write" else b"x" * 300
        if op not in {"create", "openLock"}:
            (root / "file").write_bytes(initial)
        (root / "source").write_bytes(OLD)
        (root / "target").write_bytes(b"target-old")
        binary = h.sanitized if p.get("sanitized") else h.native
        offset, count = p.get("offset", 0), p.get("count", 16)
        o = h.run([str(binary), op, str(root), str(offset), str(count)], root, rules, preload=not p.get("sanitized", False))
        value = extra_value(o)
        need(value.get("io") is True and value.get("shape") is True and value.get("unchanged") is True and value.get("failures") == 0, "C shim preserves IO/Except ABI + borrowed input")
        number = p.get("number")
        need(value.get("ok") == (number is None), "raw shim success/error polarity")
        if number is not None:
            need(value.get("number") == number and value.get("bytes") == "", "raw shim returns errno immediately")
        else:
            if op in {"create", "openDir", "openRead", "openLock"}:
                need(type(value.get("number")) is int and value["number"] >= 0, "open descriptor")
            elif op == "write":
                need(value.get("number") == count, "write count")
                need(file_bytes(root / "file") == bytes(range(256))[offset:offset + count] + initial[count:], "write offset/count exact bytes")
            elif op == "read":
                need(value.get("number") == min(count, len(initial)) and value.get("bytes") == initial[:count].hex(), "fresh ByteArray read payload/size")
            else:
                need(value.get("number") == 0, "POSIX zero success value")
            if op == "create":
                need(file_size(root / "file") == 0, "create side effect")
            if op == "rename":
                need(file_bytes(root / "target") == OLD and not (root / "source").exists(), "rename side effect")
            if op == "unlink":
                need(not (root / "file").exists(), "unlink side effect")
        if not p.get("sanitized"):
            bounds = op == "write" and number == 22 and not rules
            need(len(o.events) == (0 if bounds else 1), "raw shim exactly one libc call; bounds refusal none")
            if not bounds:
                e = o.events[0]
                need(e.op == op, "raw shim routes to its named libc call")
                if op == "create": create_flags(e)
                if op == "openRead": need(e.flags & os.O_CLOEXEC and e.flags & os.O_ACCMODE == os.O_RDONLY, "open read flags")
                if op == "openDir": need(e.flags & (os.O_DIRECTORY | os.O_CLOEXEC) == os.O_DIRECTORY | os.O_CLOEXEC, "open dir flags")
                if op == "openLock": need(e.flags & (os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW) == os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW and e.count == 0o644, "open lock flags")
                if op == "lock": need(e.flags == 2 | 4, "raw flock flags")
                if op in {"read", "write"}: need(e.count == count, "raw syscall request count")
                if op in {"create", "openDir", "openRead", "openLock"} and number is None:
                    need(value["number"] == e.ret, "returned fd is the exact libc descriptor")
        if p.get("sanitized"):
            need(not any(s in o.stderr for s in ["AddressSanitizer", "LeakSanitizer", "runtime error:"]), "no sanitizer finding")
        return
    if c.kind == "guard":
        binary = h.sanitized if p.get("sanitized") else h.native
        o = h.run([str(binary), p["operation"], str(root)], root, rules, preload=not p.get("sanitized", False))
        value = extra_value(o)
        need(value.get("guard_ok") is True and value.get("checks", 0) > 0 and value.get("failures") == 0, "guard lifecycle/ownership/mutex assertions")
        if not p.get("sanitized"):
            closed_once(group_events(o, "close"))
        else:
            need(not any(s in o.stderr for s in ["AddressSanitizer", "LeakSanitizer", "runtime error:"]), "guard sanitizer run clean")
        if p["operation"] == "guard-reuse":
            need(file_bytes(root / "reused") == b"still-open", "closed guard finalizer preserves reused descriptor")
        return
    if c.kind == "records":
        op = p["operation"]
        args = {"create": ["create", str(root / "file")], "write": ["create", str(root / "file"), "write", "1"],
                "sync": ["create", str(root / "file"), "sync"], "close": ["create", str(root / "file"), "close"],
                "drop": ["create", str(root / "file"), "drop"], "syncdir": ["syncdir", str(root)],
                "replace": ["replace", str(root), "target", "1"], "read": ["read", str(root), "file"],
                "lock": ["lock", str(root), "unlock"], "unlock": ["lock", str(root), "unlock"], "wait": ["wait"]}[op]
        o = h.devrun(root, args, [], b"\n" if op == "wait" else b"N")
        completed(o)
        need(any(r.get("op") == op for r in o.records), "requested operation record exists")
        pairs: list[list[str]] = []
        def hook(items: list[tuple[str, Any]]) -> dict[str, Any]:
            pairs.append([k for k, _ in items])
            return dict(items)
        for line in o.stdout.splitlines():
            json.loads(line, object_pairs_hook=hook)
        need(all(keys == sorted(set(keys), key=lambda k: k.encode()) for keys in pairs), "record keys unique in canonical byte order")
        return
    if c.kind == "filesystem":
        directory = root / p["component"] if "component" in p else root
        if directory != root:
            directory.mkdir()
        payload = b"F6-filesystem\x00\xff"
        o = h.devrun(root, ["replace", str(directory), "target", str(len(payload)), "read", str(directory), "target", "lock", str(directory), "replace", str(directory), "locked", str(len(payload)), "unlock"], [], payload + payload)
        completed(o)
        need(o.records == [record("replace"), record("read", bytes=payload.hex()), record("lock"), record("replace"), record("unlock")], "filesystem replace/read/lock round trip")
        need(file_bytes(directory / "target") == payload and file_bytes(directory / "locked") == payload and file_bytes(directory / ".fvdep-writer.lock") == b"", "filesystem exact effects")
        kind = subprocess.check_output(["stat", "-f", "-c", "%T", str(directory)], text=True).strip()
        if p["filesystem"] == "zfs": need(kind == "zfs", "ZFS test root is actually ZFS")
        h.last["filesystem_type"] = kind
        return
    if c.kind == "contention":
        contention(c, h, root)
        return
    raise RuntimeError(f"unknown case kind {c.kind}")


def contention(c: Case, h: Harness, root: Path) -> None:
    lockdir = root
    if c.p["mode"] == "alias":
        (root / "alias").symlink_to(root, target_is_directory=True)
        lockdir = root / "alias"
    env = h.env(root, [], channel="holder")
    argv = [str(h.dev), "sys", "run", "lock", str(root), "wait", "unlock"]
    holder = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, start_new_session=True, umask=0)
    out = b""; errors = b""
    try:
        deadline = time.monotonic() + 8
        ready = False
        events: list[Event] = []
        while time.monotonic() < deadline:
            events = trace(root / ".control/holder/trace")
            if any(e.op == "lock" and e.ret == 0 for e in events):
                ready = True
                break
            if holder.poll() is not None:
                break
            time.sleep(0.01)
        h.last = {"holder_ready": ready, "holder_rc": holder.poll(), "holder_trace": [e.op for e in events]}
        need(ready and holder.poll() is None, "holder actually acquires flock and remains in its wait region")
        during = h.devrun(root, ["lock", str(lockdir), "replace", str(root), "during", "1", "unlock"], [], b"D", channel="during")
        during_snapshot = h.last
        completed(during)
        e = {"op": "lock", "cause": "busy", "path": str(lockdir / ".fvdep-writer.lock")}
        need(during.records == [record("lock", e)] and not (root / "during").exists(), "contending process is busy and runs no action")
        lock_protocol(during, False, directory=lockdir)
        if c.p["mode"] == "exit":
            holder.send_signal(signal.SIGKILL)
            out, errors = holder.communicate(timeout=8)
            need(holder.returncode == -signal.SIGKILL, "holder interrupted by process exit")
        else:
            out, errors = holder.communicate(b"\n", timeout=8)
            need(holder.returncode == 0, "scoped unlock completes")
        after = h.devrun(root, ["lock", str(root), "replace", str(root), "after", "1", "unlock"], [], b"A", channel="after")
        after_snapshot = h.last
        completed(after)
        need(after.records == [record("lock"), record("replace"), record("unlock")] and file_bytes(root / "after") == b"A", "lock released at region/process end")
        lock_protocol(after, True, inner=True)
        need(file_bytes(root / ".fvdep-writer.lock") == b"", "lock file stays empty and present")
        holder_events = trace(root / ".control/holder/trace")
        need(not any(e.op == "unlink" for e in holder_events + during.events + after.events), "lock metadata never unlinked")
        h.last = {"holder_ready": True, "holder_rc": holder.returncode, "holder_stdout": out.decode(errors="replace"), "holder_stderr": errors.decode(errors="replace"), "holder_trace": [e.op for e in holder_events], "during": during_snapshot, "after": after_snapshot}
    finally:
        if holder.poll() is None:
            holder.kill()
            out, errors = holder.communicate()
        elif not out and not errors:
            out, errors = holder.communicate()
        if not h.last.get("holder_ready"):
            h.last.update({"holder_rc": holder.returncode, "holder_stdout": out.decode(errors="replace"), "holder_stderr": errors.decode(errors="replace")})


def preflight(h: Harness) -> None:
    controls = h.work / "controls"
    controls.mkdir()
    for op in OPS:
        root = controls / op
        root.mkdir()
        (root / "file").write_bytes(bytes(range(64)))
        (root / "source").write_bytes(OLD)
        target = root if op in {"openDir", "syncDir", "closeDir", "rename"} else root / "file"
        o = h.run([str(h.control), op, str(target)], root, [Rule(op, arg=13)])
        need(o.rc == 0 and len(o.records) == 1 and o.records[0].get("return") == -1 and o.records[0].get("errno") == 13, f"fault control {op}: injected errno")
        need(len(o.events) == 1 and o.events[0].op == op and o.events[0].number == 13, f"fault control {op}: trace")
    for alias in ["open64", "openat", "open2"]:
        root = controls / alias
        root.mkdir()
        if alias == "open2":
            (root / "new").write_bytes(b"control")
        o = h.run([str(h.control), alias, str(root / "new")], root, [Rule("openRead" if alias == "open2" else "create", arg=13)])
        need(o.rc == 0 and o.records[0]["errno"] == 13 and len(o.events) == 1, f"fault control alias {alias}")
    for action, wanted in [("short", 1), ("zero", 0), ("over", 17)]:
        root = controls / action
        root.mkdir(); (root / "file").write_bytes(bytes(range(64)))
        o = h.run([str(h.control), "write", str(root / "file")], root, [Rule("write", action=action, arg=1)])
        need(o.rc == 0 and o.records[0]["return"] == wanted and len(o.events) == 1, f"fault control {action}")
    root = controls / "retries"
    root.mkdir(); (root / "file").write_bytes(bytes(range(64)))
    o = h.run([str(h.control), "write", str(root / "file"), "5"], root, [Rule("write", count=4, arg=4)])
    need([r["errno"] for r in o.records] == [4, 4, 4, 4, 0] and len(o.events) == 5, "fault control repeat then pass")
    root = controls / "virtual"
    root.mkdir(); (root / "file").write_bytes(b"")
    o = h.run([str(h.control), "read", str(root / "file"), "3", "16"], root, [Rule("read", count=3, action="virtual", arg=20)])
    need([r["return"] for r in o.records] == [16, 4, 0] and o.records[0]["bytes"] == "00" * 16, "fault control virtual stream")
    for action in ["crash", "aftercrash"]:
        root = controls / action
        root.mkdir(); (root / "file").write_bytes(bytes(range(64)))
        o = h.run([str(h.control), "write", str(root / "file")], root, [Rule("write", action=action, arg=0)])
        need(o.rc == 99 and len(o.events) == 1 and o.events[0].action == action, f"fault control {action}")
    root = controls / "posterrno"
    root.mkdir(); (root / "source").write_bytes(OLD)
    o = h.run([str(h.control), "rename", str(root)], root, [Rule("rename", action="posterrno", arg=5)])
    need(o.records[0]["errno"] == 5 and file_bytes(root / "target") == OLD and not (root / "source").exists(), "fault control post-commit errno")
    root = controls / "scope"
    root.mkdir()
    outside = controls / "scope-other-owned-file"
    o = h.run([str(h.control), "create", str(outside)], root, [Rule("create", arg=13)])
    need(o.rc == 0 and o.records[0]["return"] >= 0 and not o.events and outside.exists(), "faults stay inside the named test root")
    for binary in [h.native, h.sanitized]:
        root = controls / binary.name
        root.mkdir()
        o = h.run([str(binary), "runtime-thread", str(root)], root, [], preload=False)
        need(o.rc == 0 and o.records == [{"runtime_ok": True}] and not o.stderr, "runtime-only thread/allocator control with leak detection")
        print(f"CONTROL runtime {binary.name} rc={o.rc}", flush=True)
    for sanitizer, mode, marker in [("address", "asan", "AddressSanitizer"), ("undefined", "ubsan", "runtime error:")]:
        root = controls / ("engine-" + sanitizer)
        root.mkdir()
        binary = h.project / "tests/sys/.build" / ("san-control-" + sanitizer)
        clean = h.run([str(binary), "clean"], root, [], preload=False)
        need(clean.rc == 0 and not clean.stderr, "sanitizer clean positive control")
        planted = h.run([str(binary), mode], root, [], preload=False)
        need(planted.rc != 0 and marker in planted.stderr, f"{sanitizer} planted bad input fires")
        print(f"CONTROL {sanitizer} clean_rc={clean.rc} planted_rc={planted.rc} marker={marker}", flush=True)
    root = controls / "engine-leak"
    root.mkdir()
    leak = h.run([str(h.project / "tests/sys/.build/san-control-address"), "leak"], root, [], preload=False)
    need(leak.rc != 0 and "LeakSanitizer" in leak.stderr, "owned-malloc leak canary fires with leak detection enabled")
    print(f"CONTROL standalone_leak rc={leak.rc} LeakSanitizer=1", flush=True)
    root = controls / "shim-owned-leak"
    root.mkdir()
    reached = h.run([str(h.project / "tests/sys/.build/native-leak-canary"), "create", str(root)], root, [], preload=False)
    need(reached.rc != 0 and "LeakSanitizer" in reached.stderr and "8193 byte" in reached.stderr and "owned_leak" in reached.stderr, "same-build C-shim-path 8193-byte owned leak canary fires")
    print(f"CONTROL shim_path_leak bytes=8193 rc={reached.rc} LeakSanitizer=1", flush=True)
    h.last = {}
    print("CONTROLS PASS: 13 logical ops + aliases; errno/retry/short/zero/over/virtual/crash/posterrno; path scope; runtime + ASan/UBSan canaries", flush=True)


def evaluate(c: Case, h: Harness, root: Path, full: bool = False) -> tuple[list[str], str]:
    before = time.monotonic()
    reasons: list[str] = []
    h.last = {}
    try:
        execute(c, h, root)
    except Exception as error:
        reasons.append(f"{type(error).__name__}: {error}")
    try:
        if root.exists():
            shutil.rmtree(root)
    except Exception as error:
        reasons.append(f"cleanup {type(error).__name__}: {error}")
    try:
        expected = short(describe(c))
        actual = short(h.last)
        display = short(h.last, full)
    except Exception as error:
        reasons.append(f"render {type(error).__name__}: {error}")
        expected = jd({"case": c.id, "expectation_unrenderable": True})
        actual = display = jd({"exception": type(error).__name__, "message": str(error)})
    elapsed = time.monotonic() - before
    reason = "; ".join(reasons)
    verdict = "FAIL" if reasons else "PASS"
    command = f"tools/vflab-run bash tests/sys/run.sh --case {c.id}"
    row = [c.id, c.row, expected, verdict, command, actual, reason or "-", f"{elapsed:.6f}", c.method, c.notes]
    return row, display


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--work", type=Path)
    parser.add_argument("--zfs", type=Path)
    parser.add_argument("--report", type=Path, default=Path("tests/sys/.results/latest.tsv"))
    parser.add_argument("--label", default="current")
    parser.add_argument("--case")
    parser.add_argument("--row", action="append", default=[])
    parser.add_argument("--append", action="store_true")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--controls-only", action="store_true")
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args()
    seed = int(os.environ.get("FVDEP_TEST_SEED", str(SEED)), 0)
    all_cases = catalog(seed)
    print(f"SEED {seed} (0x{seed:x}); CASES {len(all_cases)}; SOURCE F1–F6 + B2", flush=True)
    if args.list:
        for c in all_cases:
            print(f"{c.id}\t{c.row}\t{c.method}")
        return 0
    if args.work is None:
        parser.error("--work is required")
    work = args.work.resolve(strict=True)
    need(work.is_dir() and work.stat().st_uid == os.getuid(), "owned work root")
    # MAIN, U3 close: the ZFS root = a private child of the provisioned sys-test/ (no sudo); absent
    # (a host without fvdep's dataset) ⇒ every `filesystem=zfs` case reports SKIP by name.
    zfs = args.zfs.resolve(strict=True) if args.zfs is not None else None
    if zfs is not None:
        need(zfs.is_dir() and zfs.parent == Path("/srv/data/fvdep/sys-test") and zfs.name.startswith("f6.") and zfs.stat().st_uid == os.getuid(), "owned dedicated ZFS root")
    h = Harness(Path(__file__).resolve().parents[2], work, zfs)
    preflight(h)
    if args.controls_only:
        return 0
    selected = [c for c in all_cases if (args.case is None or c.id == args.case) and (not args.row or c.row in args.row)]
    if not selected:
        parser.error(f"case not found: {args.case}")
    rows: list[list[str]] = []
    failures = skips = 0
    times: list[tuple[float, str]] = []
    start = time.monotonic()
    for c in selected:
        on_zfs = c.p.get("filesystem") == "zfs"
        if on_zfs and zfs is None:
            reason = "no ZFS root (--zfs): fvdep's dataset lives on vflab"
            rows.append([c.id, c.row, short(describe(c)), "SKIP", f"tools/vflab-run bash tests/sys/run.sh --case {c.id}", "-", reason, "0.000000", c.method, c.notes])
            skips += 1
            print(f"SKIP {c.id}: {reason}", flush=True)
            continue
        base = zfs if on_zfs and zfs is not None else work
        root = base / c.id
        row, display = evaluate(c, h, root, args.full)
        rows.append(row)
        verdict, reason = row[3], row[6]
        failed = verdict == "FAIL"
        failures += failed
        times.append((float(row[7]), c.id))
        if args.case or (failed and failures <= 8):
            print(f"{verdict} {c.id}: {reason if failed else 'contract holds'}; actual={display}", flush=True)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    header = ["id", "row", "expected", args.label, "command", "output", "reason", "seconds", "method", "notes"]
    stored = rows
    if args.append and args.report.exists():
        with args.report.open(newline="", encoding="utf-8") as f:
            reader = csv.reader(f, delimiter="\t")
            need(next(reader) == header, "incremental report label/header")
            combined = {r[0]: r for r in reader}
        combined.update({r[0]: r for r in rows})
        need(set(combined) <= {c.id for c in all_cases}, "incremental report case ids")
        stored = [combined[c.id] for c in all_cases if c.id in combined]
    with args.report.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(stored)
    if args.case is None:
        args.report.with_name(f"GREEN.F.{args.label}.txt").write_text("".join(r[0] + "\n" for r in stored if r[3] == "PASS"), encoding="utf-8")
    print(f"RESULT {len(rows)} cases; {len(rows) - failures - skips} PASS; {failures} FAIL; {skips} SKIP; wall {time.monotonic() - start:.3f}s; report {args.report}")
    print("SLOWEST " + "; ".join(f"{name}={seconds:.3f}s" for seconds, name in sorted(times, reverse=True)[:5]))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
