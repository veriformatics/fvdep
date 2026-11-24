#!/usr/bin/env python3
"""Blind U6 profile suite. Run against a built dev driver in the vflab PID namespace."""
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

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tests.profile import boundary_cases, record_cases, syntax_cases  # noqa: E402,F401 -- register from this tree
from tests.profile.harness import (  # noqa: E402 -- python -I imports the trusted checkout above
    BASE, BIN, CASES, DEV, HERE, ROOT, SEED, Case, Context, Toolchain, line_rule, need,
)

RUNS = HERE / ".runs"


def coverage_text() -> str:
    ids = [c.id for c in CASES]
    need(ids and len(ids) == len(set(ids)), "empty suite or duplicate case id")
    return "id\tpart\tclause\texpected\n" + "".join(
        f"{c.id}\t{c.part}\t{c.clause}\t{line_rule(c.expected)}\n" for c in CASES
    )


def validate_plan() -> None:
    header, *rows = (HERE / "PLAN.tsv").read_text().splitlines()
    need(header == "clause\tcovers\tcase ids\tstatus", "wrong plan header")
    mapped: set[str] = set()
    for row in rows:
        clause, _, ids, status = row.split("\t")
        need(status == "covered" or status.startswith("register: "), f"unfinished plan row {clause}: {status}")
        selected = set(ids.split()) if ids != "-" else set()
        need(selected or status.startswith("register: "), f"empty coverage for {clause}")
        mapped.update(selected)
    expected = {c.id for c in CASES}
    need(mapped == expected, f"unregistered ids {sorted(mapped - expected)!r}; unmapped ids {sorted(expected - mapped)!r}")
    print(f"PLAN {len(rows)} rows, {len(expected)} mapped cases")


def execute(c: Case, parent: Path, toolchain: Toolchain) -> tuple[str, list[dict[str, Any]]]:
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix=c.id + "-", dir=parent) as work:
        ctx = Context(Path(work), c.id, toolchain)
        try:
            c.run(ctx)
            need(ctx.calls, "case never called a driver")
            verdict, detail = "PASS", ""
        except AssertionError as exc:
            verdict = "FAIL" if ctx.calls else "ERROR"
            detail = line_rule(str(exc))
        except (OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
            verdict, detail = "ERROR", line_rule(f"{type(exc).__name__}: {exc}")
        ctx.calls.append({"case": c.id, "verdict": verdict, "detail": detail,
                          "replay": f"tools/vflab-run bash tests/profile/run.sh --case {c.id}",
                          "seconds": round(time.monotonic() - start, 4)})
    return verdict, ctx.calls


def write_evidence(path: Path, parent: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "".join(json.dumps(row, sort_keys=True, ensure_ascii=True) + "\n" for row in rows)
    path.write_text(text.replace(str(parent), "<run>").replace(str(ROOT), "<repo>")
                    .replace(str(Path.home()), "<home>"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", help="case id prefix; repeatable")
    parser.add_argument("--coverage", action="store_true", help="print registrations without running a binary")
    parser.add_argument("--validate-plan", action="store_true", help="validate the tracked plan against registrations")
    parser.add_argument("--evidence", type=Path, help="write the portable JSONL transcript")
    args = parser.parse_args()
    coverage = coverage_text()
    if args.coverage:
        print(coverage, end="")
        return 0
    need((HERE / "COVERAGE.tsv").read_text() == coverage, "COVERAGE.tsv differs from registered cases")
    if args.validate_plan:
        validate_plan()
        return 0
    jobs = int(os.environ.get("FVDEP_PROFILE_JOBS", "2"))
    need(1 <= jobs <= 8, "FVDEP_PROFILE_JOBS must be an integer in 1..8")
    need(all(p.is_file() and os.access(p, os.X_OK) for p in (BIN, DEV)), "run.sh must build both binaries")
    cases = [c for c in CASES if any(c.id.startswith(p) for p in (args.case or [""]))]
    need(cases, "case filter matched no cases")
    print(f"SEED {SEED}", flush=True)
    RUNS.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="trial-", dir=RUNS) as tmp:
        parent = Path(tmp)
        toolchain = Toolchain.seed(parent)
        evidence: list[dict[str, Any]] = [{"contract": BASE, "seed": SEED, "jobs": jobs,
                                          "fingerprint": toolchain.fingerprint}]
        passed = failed = errors = 0
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for verdict, rows in pool.map(lambda c: execute(c, parent, toolchain), cases):
                evidence.extend(rows)
                item = rows[-1]
                name, detail = item["case"], item["detail"]
                print(f"{verdict} {name}" + (f": {detail}" if detail else ""), flush=True)
                passed += verdict == "PASS"
                failed += verdict == "FAIL"
                errors += verdict == "ERROR"
        print(f"SUMMARY {len(cases)} cases; {passed} passed; {failed} failed; {errors} harness errors", flush=True)
        if args.evidence:
            write_evidence(args.evidence, parent, evidence)
    return min(255, failed + errors)


if __name__ == "__main__":
    raise SystemExit(main())
