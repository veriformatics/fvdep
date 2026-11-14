"""Record all stub outcomes + the 26 D clauses without changing batch-1 evidence."""

from __future__ import annotations

import argparse
import csv
import importlib.util
import re
import sys
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .record import compact
else:
    spec = importlib.util.spec_from_file_location("fvdep_codec_record", Path(__file__).with_name("record.py"))
    assert spec is not None and spec.loader is not None
    record = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = record
    spec.loader.exec_module(record)
    compact = vars(record)["compact"]

NOTES = {
    "D1-clip": "Exact byte-boundary oracle; ASCII + 2/3/4-byte scalars and cut offsets; arbitrary scalar strings; input <=cap unchanged.",
    "D2-commit-digest": "40/64-byte lowercase hex; boundaries, uppercase/nonhex/NUL/Unicode; every digest represented independently.",
    "D2-utc": "Independent fixed-shape numeric ranges; 0000/9999, leap second 60 + nonexistent calendar dates accepted.",
    "D2-id-version": "U2 canonical grammar; 65536 accepted; 65537 typed WF=false and byte-level text tooLarge. No out-of-domain ofJson input.",
    "D2-constant-profile": "Constants permit any noncontrol scalar sequence (not T's Lean-name subset); UTF-8 cap 1024; profiles ASCII subset cap 256.",
    "D2-argv": "Program nonempty, later empty allowed, only NUL prohibited; element kind/byte caps + array nonempty path pinned.",
    "D3-layout": "Independent receipt field encoder + literal proof/differential byte goldens; constructor kind controls evidence (ruling 2).",
    "D3-roundtrip": "Generated WF typed receipts -> toJson/ofJson plus independent JSON-value input -> all typed fields observed without toJson.",
    "D3-nullness": "All nullable fields of both kinds; general kind before field nullness; accepted argv alone gets element descent (ruling 4).",
    "D3-decl-argv": "Receipt argv persistence + U2 shaped presence, agreement and changes; argv order/repeats/empty later elements retained.",
    "D4-lock-layout": "Independent schema-1 layout and canonical byte encoder; no LF; no equality between root and receipt library pins (ruling 3).",
    "D4-lock-roundtrip": "0/1/many WF receipts; whitespace-variant bytes + typed roundtrip; all fields observed without tested encoders.",
    "D4-order": "Unsorted/repeated ids, different versions of same id; first offending index after every element's schema walk.",
    "D4-normalize": "Exact stable sorted sequence proves permutation/library preservation; equal ids carry distinct evidence/profile data.",
    "D5-text": "J3 independent oracle: malformed/depth/size/duplicates first; source bytes arbitrary, BOM/UTF-8/suffix mutations.",
    "D5-root-discriminator": "Nonobject roots, schema missing/type/value + receipt evidence missing/type/value; mixed other errors masked correctly.",
    "D5-unknown-missing": "Every receipt object/member deletion + extras, lock root, generated object levels; unknown before missing, byte-key order.",
    "D5-types-values": "Every field x every JSON constructor (both evidence kinds); exact error path/kind/value; all ofJson inputs J1-valid.",
    "D5-precedence": "Discriminator > unknown > missing > recursive key/index values > ordering; nullness before argv descent; seeded combinations.",
    "D5-pointer": "RFC6901 ~ then / escaping, root/empty key/index/Unicode/NUL; exact typed error paths apart from rendered text.",
    "D5-render": "Every kind, root separator omission, missing no value, canonical byte lengths 64/65 incl escapes + multibyte; text/doc wrappers.",
    "D6-envelope-layout": "Independent schema-1 layout + literal golden; every diagnostic slot clipped separately; result preserved.",
    "D6-wellformed": "All exits/error-presence pairs; result depth31/32, unsorted/repeated/overcap values; fetched UTC; raw long diagnostics accepted (ruling 5).",
    "D6-codes": "All 7 commands and all 28 codes exhaustively, including busy; codes also exercised inside emitted envelopes.",
    "D7-valid": "WF receipts/locks/envelopes reprinted/decoded through real J; expected full layout, never merely an ok tag.",
    "D8-checks": "Independent typed-domain checks: valid + invalid syntax/nullness/constructor agreement/order/result; raw diagnostic clipping distinct from WF.",
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("--column", default="stubC")
    parser.add_argument("--command", default="tools/vflab-run bash tests/codec/run.sh")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    lines = args.log.read_text().splitlines()
    summary = [line for line in lines if line.startswith("SUMMARY ")]
    assert len(summary) == 1 and "driver_rc=0 " in summary[0]
    assert not any("Traceback" in line or "driver-error:" in line for line in lines)
    outcomes: dict[str, tuple[bool, str]] = {}
    clauses: dict[str, tuple[str, list[str], list[str]]] = {}
    for line in lines:
        match = re.match(r"^(PASS|FAIL) (\S+)(?: (.*))?$", line)
        if match:
            verdict, id, _ = match.groups()
            assert id not in outcomes
            outcomes[id] = (verdict == "PASS", line)
        match = re.match(r"^CLAUSE (D\S+) (\d+F/\d+P) cases=(\S+) methods=(\S+)$", line)
        if match:
            id, count, cases, methods = match.groups()
            assert id not in clauses
            clauses[id] = (count, cases.split(","), methods.split(","))
    count = re.search(r" cases=(\d+) ", summary[0])
    assert count is not None and int(count.group(1)) == len(outcomes)
    assert set(clauses) == set(NOTES) and len(clauses) == 26
    path = root / "COVERAGE-D.tsv"
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        assert reader.fieldnames is not None
        headers, rows = list(reader.fieldnames), list(reader)
    assert len(rows) == 26 and {row["id"] for row in rows} == set(NOTES)
    if args.column not in headers:
        headers.append(args.column)
    for row in rows:
        count_text, cases, methods = clauses[row["id"]]
        p = sum(outcomes[id][0] for id in cases)
        assert count_text == f"{len(cases) - p}F/{p}P" and all(id.startswith("D.") for id in cases)
        row["cases"] = compact(cases)
        row["method"] = ";".join(methods) + ";differential(independent D oracle)"
        row[args.column] = count_text
        row["notes"] = NOTES[row["id"]]
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, headers, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    with (root / f"RESULTS.{args.column}.tsv").open("w", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(["id", "command", "output"])
        writer.writerows((id, args.command, output) for id, (_, output) in outcomes.items())
    for prefix, name in [("", f"GREEN.{args.column}.txt"), ("D.", f"GREEN.D.{args.column}.txt")]:
        (root / name).write_text("".join(id + "\n" for id, (passed, _) in outcomes.items() if passed and id.startswith(prefix)))
    d_cases = [id for id in outcomes if id.startswith("D.")]
    d_pass = sum(outcomes[id][0] for id in d_cases)
    print(f"RECORDED {args.column} clauses=26 cases={len(outcomes)} D={len(d_cases)} D_PASS={d_pass} D_FAIL={len(d_cases) - d_pass}")
    print(summary[0])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
