#!/usr/bin/env python3
"""Rebuild/validate T's coverage + green-id evidence from the per-case stub transcript."""
from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict
from pathlib import Path

NOTES = {
    "T1-size": "0/1/65535/65536/65537/65538 bytes; exact-cap valid TOML; multibyte exact cap; cap checked before malformed UTF-8",
    "T1-bom": "BOM alone, before valid TOML, before invalid UTF-8 + repeated BOM",
    "T1-utf8": "all 256 singleton bytes; 160 fixed-seed arbitrary strings; named invalid classes + valid scalar boundaries; byte offsets after multibyte prefixes",
    "T1-textstage": "size > BOM > UTF-8; exact returned UTF-8 text including NUL/noncharacters/interior BOM",
    "T1-syntax": "syntax payload compared with direct Lake first error; read detail must name 1-based line:column",
    "T1-dupkeys": "scalar/escaped alias/table/dotted/inline/redefined/inline extension; independent tomllib negative controls",
    "T1-worst": "four 65536-byte worst shapes + synthetic control-character message; safety cases can stay green on both non-crashing stubs; real path + crash mutant owed",
    "T1-ofLake": "hand-built malformed Name shapes at root/nested; arbitrary raw string keys; each target-facing parse also checks direct Lake key uniqueness/shape + array/scalar preservation against tomllib; table order ignored",
    "T1-readpath": "text failures + valid policy default; synthetic code variants pin internal iff key-shape failure",
    "T3-schema": "missing/integer wrong value/all other TOML kinds; root discriminator precedence",
    "T3-root": "all non-table roots; unknown before missing; unknown key byte order",
    "T3-library": "table/commit kinds; missing/unknown; 39/40/41-byte, uppercase/nonhex/control commits",
    "T3-policy": "absent/empty/default/development; every other kind, unknown key + invalid enum",
    "T3-modules-key": "id grammar + 65536/65537-byte bounds; unordered valid entries sorted; first erroneous key by bytes",
    "T3-evidence": "absent proof; differential; explicit proof + invalid enum + non-string kinds refused",
    "T3-entry-keys": "each required/forbidden field for both kinds; unknown key + entry table kinds",
    "T3-values": "version grammar + 65536/65537-byte bounds; fn/abi; constant syntax + 1024/1025-byte boundaries; kinds",
    "T3-lists": "both lists: every kind/empty; module syntax + 256/257-byte bounds; reserved prefix exactness; element-before-repeat order + first repeat index",
    "T3-adapter": "nonempty argv; empty argv[0] vs empty later; repeated args kept; NUL refusal; 65536/65537 UTF-8 byte bounds",
    "T3-overlap": "first impl-list overlap (not proof-list order); list validity/repeats precede relation",
    "T3-dup-tree": "root/library/policy/modules/entry repeated keys; duplicate before discriminator; least repeated UTF-8 key",
    "T3-order": "mixed failures + table permutations; 96 fixed-seed multi-defect trees; oracle = independent ordered T3/D5 walk",
    "T3-paths": "bare/quoted/empty/unicode/control segments + indices; every schema refusal also checks named detail",
    "T4-layout": "independent encoder + generated 0/1/many modules, both entry kinds + policies; section/key order, blanks, arrays + final LF exact",
    "T4-escapes": "all attainable control escapes + DEL, quote, slash, non-BMP, noncharacters, U+2028/2029 + interior BOM; NUL impossible in well-formed typed fields (keyPath tests it)",
    "T5-roundtrip": "toTree exact + tree round trip + compiled printer/read identity + independently encoded text/read identity; generated files stay within text cap",
    "T6-altspell": "dotted/inline/literal/multiline/comment/whitespace/CRLF/hex + signed integer/key-order variants; inline string-kind mismatch, arrays of tables, float + datetime refusals",
    "U2-projection": "library + declaration sequence exact over the same generated well-formed manifests",
}


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--freeze", action="store_true")
    parser.add_argument("--label", default="stubG")
    args = parser.parse_args()
    home = Path(__file__).resolve().parent
    coverage_path = (home / "COVERAGE-T.tsv").resolve(strict=True)
    result_path = (home / f"RESULTS.T.{args.label}.tsv").resolve(strict=True)
    report = read_tsv(result_path)
    coverage = read_tsv(coverage_path)
    assert len(coverage) == 28
    assert set(NOTES) == {r["id"] for r in coverage}
    assert len(report) == 1854
    assert len(report) == len({r["id"] for r in report})
    assert {r["coverage"] for r in report} == set(NOTES)
    assert all(r[args.label] in {"PASS", "FAIL"} for r in report)
    assert all(r["command"].endswith("--case " + r["id"]) for r in report)
    process_failures = [r["id"] for r in report if any(marker in r["output"] for marker in ['"process_error":', '"timeout":', '"harness_error":'])]
    assert not process_failures, process_failures
    by_row: dict[str, list[dict[str, str]]] = defaultdict(list)
    for r in report:
        by_row[r["coverage"]].append(r)
    for r in coverage:
        cases = by_row[r["id"]]
        counts = Counter(c[args.label] for c in cases)
        values = {"cases": str(len(cases)), "method": "/".join(sorted({c["method"] for c in cases})),
                  "stubG": f"{counts['FAIL']}F/{counts['PASS']}P", "notes": NOTES[r["id"]]}
        if args.freeze:
            r.update(values)
        else:
            for key, value in values.items():
                assert r[key] == value, (r["id"], key, r[key], value)
        assert all(r[k] != "unknown" for k in ["cases", "method", "stubG", "notes"])
    if args.freeze:
        for r in report:
            if not r["notes"]:
                r["notes"] = "-"
        with result_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=list(report[0]), delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(report)
    else:
        assert all(r["notes"] for r in report)
    green = [r["id"] for r in report if r[args.label] == "PASS"]
    green_path = home / f"GREEN.T.{args.label}.txt"
    if args.freeze:
        with coverage_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=["id", "clause", "cases", "method", "stubG", "notes"], delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(coverage)
        green_path.write_text("".join(case + "\n" for case in green), encoding="utf-8")
    else:
        assert green_path.read_text(encoding="utf-8").splitlines() == green
    print(f"EVIDENCE PASS rows={len(coverage)} unknown=0 cases={len(report)} FAIL={len(report) - len(green)} PASS={len(green)} coverage_bytes={coverage_path.stat().st_size} results_bytes={result_path.stat().st_size}")
    print("GREEN_BY_ROW " + "; ".join(f"{row}={sum(c[args.label] == 'PASS' for c in cs)}" for row, cs in by_row.items() if any(c[args.label] == 'PASS' for c in cs)))
    print(f"PROCESS_CONTROL expected_cases=1854 observed_cases={len(report)} process_failures={len(process_failures)}")
    print("FAILURE_REASONS " + str(dict(Counter(r["reason"] for r in report if r[args.label] == "FAIL"))))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
