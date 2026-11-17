#!/usr/bin/env python3
"""Run the contract-only suite: python3 -I tests/acceptance/run.py [--merged] [--unit U1] [--jobs N]."""
from __future__ import annotations

import argparse
import csv
import importlib.util
import os
import subprocess
import sys
import time
import traceback
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
from harness import CASES, SEED, Context  # noqa: E402 — isolated mode loads only this suite.


def load() -> dict[str, str]:
    for path in sorted(HERE.glob("test_*.py")):
        spec = importlib.util.spec_from_file_location(path.stem, path)
        assert spec is not None and spec.loader is not None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    with (HERE / "MANIFEST.tsv").open(newline="") as file:
        rows = list(csv.DictReader(file, delimiter="\t"))
    assert rows, "MANIFEST.tsv is empty"
    assert len({row["id"] for row in rows}) == len(rows), "duplicate MANIFEST id"
    assert set(CASES) == {row["id"] for row in rows}, "MANIFEST and discovered cases differ"
    for row in rows:
        test = CASES[row["id"]]
        assert list(row) == ["id", "unit", "source", "predicate", "kind", "status"]
        assert row["status"] in {"merged", "unmerged"}, (row["id"], row["status"])
        for field in ("unit", "source", "predicate", "kind"):
            assert row[field] == getattr(test, field), (row["id"], field)
    return {row["id"]: row["status"] for row in rows}


def run_case(test) -> bool:
    """One case → its PASS/FAIL line (+ the traceback of an unexpected exception) on stdout."""
    context = None
    try:
        # Preflight every case, including properties, before creating any fixture.
        context = Context()
        test.run(context)
    except Exception as exc:
        print(f"FAIL {test.id}: {type(exc).__name__}: {exc}", flush=True)
        if not isinstance(exc, AssertionError):
            traceback.print_exc(file=sys.stdout)
        return False
    else:
        print(f"PASS {test.id}", flush=True)
        return True
    finally:
        if context is not None:
            context.close()


def worker(case_id: str) -> tuple[bool, str, str, float]:
    """`--case ID` in its own process (a Context per case; fvdep's state + temp dirs per Context)."""
    start = time.monotonic()
    proc = subprocess.run([sys.executable, "-I", str(Path(__file__).resolve()), "--case", case_id],
                          capture_output=True, text=True, encoding="utf-8", errors="replace", check=False)
    out = proc.stdout
    passed = proc.returncode == 0 and f"PASS {case_id}\n" in out
    if not passed and f"FAIL {case_id}:" not in out:
        out += f"FAIL {case_id}: the case's process exited with code {proc.returncode}\n"
    return passed, out, proc.stderr, time.monotonic() - start


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="List selected MANIFEST ids without invoking fvdep.")
    parser.add_argument("--merged", action="store_true",
                        help="Select the cases merged into the gate (MANIFEST status merged).")
    parser.add_argument("--unit", choices=[f"U{i}" for i in range(1, 16)])
    parser.add_argument("-k", default="", metavar="SUBSTRING", help="Select ids containing this text.")
    parser.add_argument("--jobs", type=int, metavar="1-8", default=os.environ.get("FVDEP_ACCEPTANCE_JOBS", "3"),
                        help="Cases at once, each in its own process (default FVDEP_ACCEPTANCE_JOBS, else 3).")
    parser.add_argument("--case", metavar="ID", help="Run exactly this case in this process (the parallel worker).")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 8:
        parser.error("--jobs (FVDEP_ACCEPTANCE_JOBS) must be 1-8")
    status = load()
    if args.case is not None:
        return 0 if run_case(CASES[args.case]) else 1
    selected = [test for test in CASES.values()
                if (args.unit is None or test.unit == args.unit) and args.k in test.id
                and (not args.merged or status[test.id] == "merged")]
    selected.sort(key=lambda test: (int(test.unit[1:]), test.id))
    if not selected:
        parser.error("no tests match the selection")
    if args.list:
        for test in selected:
            print(f"{test.id}\t{test.unit}\t{test.kind}\t{test.predicate}")
        return 0
    print(f"seed={SEED} (0x{SEED:x}); tests={len(selected)}; jobs={args.jobs}", flush=True)
    failures = 0
    durations = []
    if args.jobs == 1:
        for test in selected:
            start = time.monotonic()
            failures += not run_case(test)
            durations.append((time.monotonic() - start, test.id))
    else:
        # Results print in case order: a case's lines wait for the cases before it.
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            runs = [(test.id, pool.submit(worker, test.id)) for test in selected]
            for case_id, run in runs:
                passed, out, err, seconds = run.result()
                sys.stdout.write(out)
                sys.stdout.flush()
                sys.stderr.write(err)
                sys.stderr.flush()
                failures += not passed
                durations.append((seconds, case_id))
    print("Slowest tests:")
    for seconds, id in sorted(durations, reverse=True)[:5]:
        print(f"  {id} {seconds:.3f}s")
    print(f"tests={len(selected)} passed={len(selected) - failures} failed={failures}")
    # POSIX status is one byte: 256 failures must never become a false green.
    return min(failures, 255)


if __name__ == "__main__":
    sys.exit(main())
