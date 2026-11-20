#!/usr/bin/env python3
"""Blind U5b oracle contract suite. Run via tests/oracle/run.sh in a vflab unit."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from typing import Any

# Resolve sibling test modules against the trusted checkout even under python -I.
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tests.oracle.harness import (  # noqa: E402 -- isolated checkout-local import path above
    BASE, BIN, CASES, DEV, HERE, ROOT, SEED, Case, Context, Fixture, cc_escape, need, seed_toolchain,
)

RUNS = HERE / ".runs"


def load_cases() -> None:
    from tests.oracle import protocol_cases, snapshot_cases  # noqa: F401 -- register contract rows


def coverage_text() -> str:
    return "id\tpart\tclause\texpected\n" + "".join(
        f"{c.id}\t{c.part}\t{c.clause}\t{c.expected}\n" for c in CASES
    )


def execute(c: Case, parent: Path, fixture: Fixture | None, seed: Path | None) -> tuple[str, list[dict[str, Any]]]:
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix=c.id + "-", dir=parent) as directory:
        ctx = Context(Path(directory), c.id, fixture if c.fixture else None, seed)
        try:
            c.run(ctx)
            need(ctx.records, "case never called a driver")
            verdict, detail = "PASS", ""
        except (AssertionError, OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
            verdict = "FAIL" if ctx.records else "ERROR"
            detail = cc_escape(str(exc))
        ctx.records.append({"case": c.id, "verdict": verdict, "detail": detail,
                            "replay": f"tools/vflab-run bash tests/oracle/run.sh --case {c.id}",
                            "seconds": round(time.monotonic() - start, 4)})
    return verdict, ctx.records


def write_evidence(path: Path, parent: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "".join(json.dumps(row, sort_keys=True, ensure_ascii=True) + "\n" for row in rows)
    path.write_text(text.replace(str(parent), "<run>").replace(str(ROOT), "<repo>")
                    .replace(str(Path.home()), "<home>"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", help="case id prefix; repeatable")
    parser.add_argument("--coverage", action="store_true", help="print the registration table")
    parser.add_argument("--qualify-fixture", action="store_true", help="build and index only the two trusted fixture snapshots")
    parser.add_argument("--evidence", type=Path, help="portable JSONL invocations and verdicts")
    args = parser.parse_args()
    if not args.qualify_fixture:
        load_cases()
        need(len({c.id for c in CASES}) == len(CASES), "duplicate case id")
        if args.coverage:
            print(coverage_text(), end="")
            return 0
        need((HERE / "COVERAGE.tsv").read_text() == coverage_text(), "COVERAGE.tsv differs from registered tests")
    jobs = int(os.environ.get("FVDEP_ORACLE_JOBS", "2"))
    need(1 <= jobs <= 8, "FVDEP_ORACLE_JOBS must be an integer in 1..8")
    need(all(p.is_file() and os.access(p, os.X_OK) for p in (BIN, DEV)), "run.sh must build both binaries")
    cases = [c for c in CASES if any(c.id.startswith(p) for p in (args.case or [""]))]
    need(args.qualify_fixture or cases, "case filter matched no cases")
    print(f"SEED {SEED}", flush=True)
    RUNS.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="trial-", dir=RUNS) as tmp:
        parent = Path(tmp)
        fixture = Fixture.build(parent) if args.qualify_fixture or any(c.fixture for c in cases) else None
        if args.qualify_fixture:
            assert fixture is not None
            print(f"QUALIFY fixture index + H2 controls: {fixture.first} -> {fixture.second}", flush=True)
            return 0
        seed = seed_toolchain(parent) if fixture is not None else None
        red: list[dict[str, Any]] = [{"contract": BASE, "seed": SEED, "jobs": jobs}]
        passed = failed = errors = 0
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            runs = [pool.submit(execute, c, parent, fixture, seed) for c in cases]
            for future in runs:
                verdict, rows = future.result()
                red.extend(rows)
                item = rows[-1]
                name, detail = item["case"], item["detail"]
                print(f"{verdict} {name}" + (f": {detail}" if detail else ""), flush=True)
                passed += verdict == "PASS"
                failed += verdict == "FAIL"
                errors += verdict == "ERROR"
        print(f"SUMMARY {len(cases)} cases; {passed} passed; {failed} failed; {errors} harness errors", flush=True)
        if args.evidence:
            write_evidence(args.evidence, parent, red)
    return min(255, failed + errors)


if __name__ == "__main__":
    raise SystemExit(main())
