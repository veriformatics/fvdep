#!/usr/bin/env python3
"""Grade F's seeded coverage against completed source-defined case groups."""
from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict
from pathlib import Path
import subprocess
import sys

NOTES = {
    "F6-errno": "13 logical operations × Linux errno slots 1–133 + 5 generated positive values; EINTR/EEXIST/ENOENT/busy semantics from F2/F3; no fixed-error stub earns credit without its syscall trace",
    "F6-eintr": "64 vs 65 EINTRs for every retryable step; close once even on EINTR; fresh budget at a new temp + each lock step",
    "F6-budget-reset": "two 64-EINTR runs separated by positive short read/write progress; exact full bytes + acquired descriptor identity",
    "F6-noprogress": "nonempty zero write → noProgress; overreported write refuses before rename; empty write succeeds",
    "F6-crash-absent": "one-byte replacement: before/after cuts at all 8 protocol syscalls; absent/new exact target, leftovers named; process interruption, not power loss",
    "F6-crash-present": "same 16 cuts with old target present; pre-rename old + post-rename new, never partial; leftover temp listed",
    "F6-rename-fail": "errno before vs after physical rename; cleanup + secondary error; B2-6 preserves ENOENT after committed-but-reported-failed rename",
    "F6-durability": "directory open/fsync/close failure after rename; exact primary/path + durability true; B2-5 consumed temp is not unlinked",
    "F6-temps": "1/2/63/64 physically preexisting names using child PID + stdin wait; foreign bytes preserved, temp attempts bounded 0–63",
    "F6-cleanup": "write/sync/close/rename primary × close/unlink secondary combinations; close once before unlink, ordered secondary list, primary preserved",
    "F6-symlink": "target link replaced, victim unchanged; temp link foreign/unfollowed and retained while next temp succeeds",
    "F6-read": "absent/empty/present, read sizes across 1 MiB, short/zero/late error/close error + secondary; virtual streams at 2^30 and 2^30+1 use size/samples (no giant JSON)",
    "F6-lock": "trace-readiness contention, scoped release + process exit + path alias; first refusal metadata only; action once/value/exception propagation",
    "F6-lock-fail": "open/flock errno + close secondary; B2-8 successful act result survives lock-close failure",
    "F6-writer": "closed write/sync/close, finalizer, persistent guard closed flag, forced descriptor reuse, blocking guard ownership + concurrent public write/sync/close",
    "F6-names": "Path/Name predicates + original strings, all modes 0–512 + big bounds, generated Unicode/control/NUL inputs; CLI MODE/N/NAME/state/early-stdin usage; live Unicode/control directory paths",
    "F6-records": "one JSON record per operation; exact B2-2 field/kind/enum/optional rules + unique canonical key order",
    "F6-fs": "replace/read/scoped lock under gate workspace + dedicated owned ZFS directory; actual filesystem kind checked; owned roots removed",
    "F6-sanitizers": "same public shim/guard harness compiled by GCC ASan+UBSan; valid/bounds/lifecycle vectors; runtime-only initialization, detect_leaks=1, no suppression; owned 8193-byte shim-path leak canary required",
    "F6-shim": "all 13 logical syscall kinds: one libc attempt + errno unchanged; flags/mode/count/fd/source/target effects; write offset/count/overflow bounds + unchanged borrowed bytes",
}


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--freeze", action="store_true")
    parser.add_argument("--complete", action="store_true")
    args = parser.parse_args()
    home = Path(__file__).resolve().parent
    coverage_path = (home / "COVERAGE-F.tsv").resolve(strict=True)
    results_path = (home / "RESULTS.F.stubI.tsv").resolve(strict=True)
    listed = subprocess.check_output([sys.executable, "-I", str(home / "suite.py"), "--list"], text=True).splitlines()
    wanted: dict[str, tuple[str, str]] = {}
    groups: dict[str, set[str]] = defaultdict(set)
    for line in listed[1:]:
        case, row, method = line.split("\t")
        assert case not in wanted
        wanted[case] = (row, method)
        groups[row].add(case)
    assert set(groups) == set(NOTES)
    coverage = read_tsv(coverage_path)
    assert len(coverage) == 20 and {r["id"] for r in coverage} == set(NOTES)
    results = read_tsv(results_path)
    assert results and len(results) == len({r["id"] for r in results})
    actual: dict[str, list[dict[str, str]]] = defaultdict(list)
    for r in results:
        assert r["id"] in wanted and (r["row"], r["method"]) == wanted[r["id"]]
        assert r["stubI"] in {"PASS", "FAIL"}
        assert r["command"].endswith("--case " + r["id"])
        assert r["notes"]
        actual[r["row"]].append(r)
    unknown = 0
    done = 0
    for r in coverage:
        observations = actual[r["id"]]
        ids = {v["id"] for v in observations}
        assert ids <= groups[r["id"]]
        if ids != groups[r["id"]]:
            unknown += 1
            assert all(r[key] == "unknown" for key in ["cases", "method", "stubI", "notes"])
            continue
        done += 1
        counts = Counter(v["stubI"] for v in observations)
        values = {"cases": str(len(observations)), "method": "/".join(sorted({v["method"] for v in observations})),
                  "stubI": f"{counts['FAIL']}F/{counts['PASS']}P", "notes": NOTES[r["id"]]}
        if args.freeze:
            r.update(values)
        else:
            assert all(r[k] == v for k, v in values.items()), r["id"]
    if args.complete:
        assert unknown == 0 and len(results) == len(wanted)
    greens = [r["id"] for r in results if r["stubI"] == "PASS"]
    green_path = home / "GREEN.F.stubI.txt"
    if args.freeze:
        with coverage_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=["id", "clause", "cases", "method", "stubI", "notes"], delimiter="\t", lineterminator="\n")
            writer.writeheader(); writer.writerows(coverage)
        green_path.write_text("".join(case + "\n" for case in greens), encoding="utf-8")
    else:
        assert green_path.read_text(encoding="utf-8").splitlines() == greens
    print(f"EVIDENCE PASS groups={done}/20 unknown={unknown} cases={len(results)}/{len(wanted)} FAIL={len(results) - len(greens)} PASS={len(greens)}")
    print("GROUPS " + "; ".join(f"{row}={len(items)}" for row, items in actual.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
