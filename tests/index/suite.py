"""Blind black-box U4 C suite; bounded concurrency, shared fixture observations."""
from __future__ import annotations

import argparse
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import dataclass
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from typing import Any, Callable

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
DEFAULT_SEED = 0xF4DE_0402


def load(name: str) -> Any:
    spec = importlib.util.spec_from_file_location("index_test_" + name, HERE / (name + ".py"))
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


fx: Any = load("fixtures")
ref: Any = load("reference")


class Failure(Exception):
    pass


class Blocked(Exception):
    pass


class Setup(Exception):
    pass


def brief(value: Any) -> str:
    text = repr(value)
    return text if len(text) <= 420 else text[:360] + f"… ({len(text)} chars)"


def eq(got: Any, want: Any, where: str = "") -> None:
    if got != want:
        raise Failure(f"assert: {where} got={brief(got)} want={brief(want)}")


@dataclass
class Case:
    name: str
    family: str
    clause: str
    check: Callable[[], None]
    domain: str = "named fixture"


@dataclass
class Observation:
    root: Path
    proc: subprocess.CompletedProcess[bytes]
    before: bytes | None
    after: bytes | None


class Context:
    def __init__(self, binary: Path, dev: Path, work: Path, seed: int, jobs: int):
        self.binary, self.dev = str(binary.resolve()), str(dev.resolve())
        self.work, self.seed = work, seed
        self.repo, self.here, self.fx, self.ref = REPO, HERE, fx, ref
        self.cases: list[Case] = []
        self.cache: dict[str, Future[Any]] = {}
        self.lock = threading.Lock()
        self.preflight = os.environ.get("FVDEP_INDEX_PREFLIGHT") == "1"
        self.calls = 0
        self.slots = threading.BoundedSemaphore(jobs)

    @staticmethod
    def eq(got: Any, want: Any, where: str = "") -> None:
        eq(got, want, where)

    @staticmethod
    def need(condition: bool, why: str) -> None:
        if not condition:
            raise Blocked("blocked: " + why)

    def add(self, name: str, family: str, clause: str, check: Callable[[], None],
            domain: str = "named fixture") -> None:
        self.cases.append(Case(name, family, clause, check, domain))

    def shared(self, key: str, make: Callable[[], Any]) -> Any:
        with self.lock:
            existing = key in self.cache
            future = self.cache.setdefault(key, Future())
        if not existing:
            try:
                future.set_result(make())
            except BaseException as exc:
                future.set_exception(exc)
        return future.result()

    def library(self, key: str, mutate: Callable[[Any], None] | None = None,
                launch: bool = False) -> Any:
        def make() -> Any:
            lib = fx.Library(self.work / key, REPO, launch=launch)
            if mutate:
                mutate(lib)
            return lib
        return self.shared("library:" + key, make)

    def call(self, root: Path, args: list[str], *, dev: bool = False,
             env: dict[str, str] | None = None) -> subprocess.CompletedProcess[bytes]:
        settings = {**os.environ, **(env or {})}
        settings.pop("FVDEP_INDEX_FAULT_PID", None)
        with self.lock:
            self.calls += 1
        try:
            with self.slots:
                return subprocess.run([self.dev if dev else self.binary, *args], cwd=root,
                                      env=settings, input=b"", capture_output=True,
                                      timeout=240, check=False)
        except subprocess.TimeoutExpired as exc:
            raise Blocked("timeout: product call exceeded 240s; no credit") from exc

    def build_fixture(self, lib: Any) -> bytes | None:
        if not self.preflight:
            return None
        def build() -> bytes:
            proc = subprocess.run(["lake", "build", "Fvdep", "FvdepPreview", "FvdepProofs"],
                                  cwd=lib.root, capture_output=True, timeout=180, check=False)
            if proc.returncode:
                output = (proc.stdout + proc.stderr).decode(errors="replace")
                errors = [line for line in output.splitlines() if "error:" in line]
                raise Setup("setup: fixture does not build: " + brief(errors or output[-1600:]))
            return proc.stdout + proc.stderr
        return self.shared("preflight:" + str(lib.root), build)

    def observe(self, key: str, mutate: Callable[[Any], None] | None = None, *,
                launch: bool = False, args: list[str] | None = None,
                env: dict[str, str] | None = None, preflight: bool = True) -> Observation:
        def make() -> Observation:
            lib = self.library(key, mutate, launch)
            path = lib.root / "index.json"
            path.write_bytes(b"index sentinel: unchanged before a refusal\n")
            before = path.read_bytes()
            if preflight:
                self.build_fixture(lib)
            proc = self.call(lib.root, ["index", *(args or [])], env=env)
            after = path.read_bytes() if path.is_file() else None
            return Observation(lib.root, proc, before, after)
        return self.shared("observe:" + key, make)

    @staticmethod
    def document(obs: Observation) -> dict[str, Any]:
        if obs.proc.returncode != 0 or obs.after is None:
            raise Blocked(f"blocked: index result unavailable (exit {obs.proc.returncode})")
        try:
            value = json.loads(obs.after)
        except ValueError as exc:
            raise Failure("assert: successful index is not JSON") from exc
        if not isinstance(value, dict):
            raise Failure("assert: successful index root is not an object")
        return value

    def op(self, obs: Observation, id: str = "base64.encode", version: str = "1.0.0") -> Any:
        values = self.document(obs).get("operations", [])
        matches = [x for x in values if x.get("id") == id and x.get("version") == version]
        self.need(len(matches) == 1, f"operation {id}@{version} unavailable")
        return matches[0]

    @staticmethod
    def refusal(obs: Observation, line: str) -> None:
        eq(obs.proc.returncode, 2, "refusal exit")
        eq(obs.proc.stdout, b"", "refusal stdout")
        last = obs.proc.stderr.splitlines(keepends=True)[-1:] or [b""]
        eq(last[0], ref.line(line), "last stderr line")

    def refusal_case(self, name: str, family: str, clause: str, line: str,
                     mutate: Callable[[Any], None], *, preflight: bool = True,
                     launch: bool = False) -> None:
        get = lambda: self.observe(name, mutate, preflight=preflight, launch=launch)
        self.add(name, family, clause, lambda: self.refusal(get(), line))
        self.add(name + ".unchanged", family, "C1 no write before decision",
                 lambda: eq(get().after, get().before, "index byte preservation"))

    def decode(self, key: str, data: bytes) -> subprocess.CompletedProcess[bytes]:
        def make() -> Any:
            root = self.work / ("decode-" + key)
            root.mkdir()
            path = root / "input.json"
            path.write_bytes(data)
            return self.call(root, ["index", "decode", str(path)], dev=True)
        return self.shared("decode:" + key, make)

    def decode_case(self, name: str, data: bytes, want: bytes, code: int,
                    clause: str = "C6/C9 decode; U3 D5") -> None:
        def check() -> None:
            proc = self.decode(name, data)
            eq(proc.returncode, code, "decode exit")
            eq(proc.stdout, want, "decode stdout")
            eq(proc.stderr, b"", "decode stderr")
        self.add(name, "F11", clause, check, f"input bytes={len(data)}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--dev", type=Path, required=True)
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    seed = int(os.environ.get("FVDEP_TEST_SEED", str(DEFAULT_SEED)), 0)
    jobs = int(os.environ.get("FVDEP_INDEX_JOBS", "3"))
    if not 1 <= jobs <= 6:
        parser.error("FVDEP_INDEX_JOBS must be 1..6 (bounded fixture build memory)")
    work = Path(tempfile.mkdtemp(prefix=".run.", dir=HERE))
    try:
        ctx = Context(args.binary, args.dev, work, seed, jobs)
        for module in ("library_cases", "driver_cases"):
            load(module).register(ctx)
        names = [case.name for case in ctx.cases]
        if len(names) != len(set(names)):
            raise RuntimeError("duplicate case ids")
        if args.list:
            print("case\tclause\tfamily\tdomain")
            for case in ctx.cases:
                print(f"{case.name}\t{case.clause}\t{case.family}\t{case.domain}")
            return 0
        only = os.environ.get("FVDEP_INDEX_CASE", "")
        cases = [case for case in ctx.cases if only in case.name]
        if not cases:
            parser.error(f"no case contains {only!r}")
        print(f"SEED {seed} (0x{seed:x}); cases={len(cases)}; jobs={jobs}; "
              f"preflight={int(ctx.preflight)}; scope={only or 'all'}", flush=True)
        def run(case: Case) -> tuple[str, str, float, str]:
            start = time.monotonic()
            try:
                case.check()
                result, detail = "PASS", ""
            except (Failure, Blocked, Setup) as exc:
                result, detail = "FAIL", str(exc)
            except (OSError, RuntimeError, subprocess.TimeoutExpired) as exc:
                result, detail = "FAIL", "setup: " + str(exc)
            except (ValueError, TypeError, KeyError, IndexError) as exc:
                result, detail = "FAIL", "assert: malformed product result: " + str(exc)
            return case.name, result, time.monotonic() - start, detail.replace("\n", " ").replace("\t", " ")
        # One worker per shared observation; waiting assertion siblings consume no build slot.
        groups: dict[str, list[Case]] = {}
        for case in cases:
            key = case.name.removesuffix(".unchanged")
            if case.name.startswith(("C3.status.", "C3.warning.", "C4.compat.", "C4.warning.")):
                parts = case.name.split(".")
                key = parts[0] + "." + parts[-1]
            if case.name in {"C2.identity.comment", "C2.identity.proof", "C2.identity.shared",
                             "C2.identity.closure-boundary"}:
                key = "C2.identity-sequence"
            if case.name in {"C2.identity.unrelated", "C12.schema.new-version-after-index"}:
                key = "C2.unrelated-sequence"
            if case.name.startswith("C6.purity."):
                key = "C6.purity-sequence"
            groups.setdefault(key, []).append(case)
        def run_group(group: list[Case]) -> list[tuple[str, str, float, str]]:
            return [run(case) for case in group]
        results = []
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for rows in pool.map(run_group, groups.values()):
                for name, result, seconds, detail in rows:
                    results.append((name, result, seconds, detail))
                    print(f"{result} {name}\t{seconds:.6f}\t{detail}", flush=True)
        for name, result, seconds, _ in sorted(results, key=lambda row: row[2], reverse=True)[:10]:
            print(f"SLOW {name} {seconds:.6f}s {result}")
        failures = sum(result == "FAIL" for _, result, _, _ in results)
        print(f"CALLS {ctx.calls}")
        print(f"TOTAL {len(results)} PASS {len(results) - failures} FAIL {failures}")
        return min(failures, 255)
    finally:
        shutil.rmtree(work)


if __name__ == "__main__":
    raise SystemExit(main())
