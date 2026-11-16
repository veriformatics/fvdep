"""Capture two complete stub runs → case ledger + twelve-family deliverable."""
from __future__ import annotations

import argparse
import collections
from pathlib import Path
from typing import Any

FAMILIES = {
    "F1": ("entry rules + file checks", "C3/C4/C9"),
    "F2": ("identity", "C4; H2/H3"), "F3": ("status + replay + warnings", "C1/C5/C9"),
    "F4": ("compatibility", "C3 V6/C5/C6/C9"), "F5": ("notices + removed", "C3 V8/V9/C6/C9"),
    "F6": ("purity + compare + IO", "C1/C9"), "F7": ("presence + toolchain", "C1/C9"),
    "F8": ("build + load + registry forms", "C1/C2/C9"), "F9": ("CLI + precedence", "C9; interface §1"),
    "F10": ("history", "C7/C9"), "F11": ("decode + schema refusals", "C6/C9; U3 J/D5; directive D1"),
    "F12": ("schema output + registry forms", "C2/C6/C9"),
}


def read(path: Path) -> tuple[dict[str, dict[str, Any]], str, str]:
    text = path.read_text()
    rows = {}
    for line in text.splitlines():
        if line.startswith(("PASS ", "FAIL ")):
            verdict, tail = line.split(" ", 1)
            name, seconds, detail = tail.split("\t", 2)
            if name in rows:
                raise ValueError("duplicate row " + name)
            rows[name] = {"result": verdict, "seconds": seconds, "detail": detail,
                          "red": verdict == "FAIL" and detail.startswith("assert:"),
                          "reached": verdict == "PASS" or detail.startswith("assert:")}
    total = next(line for line in text.splitlines() if line.startswith("TOTAL "))
    accounting = next(line for line in text.splitlines() if line.startswith("vflab-run: Finished"))
    if int(total.split()[1]) != len(rows):
        raise ValueError("partial result log")
    return rows, total, accounting


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("a", type=Path)
    parser.add_argument("b", type=Path)
    parser.add_argument("--families", type=Path, required=True)
    parser.add_argument("--seed-log", type=Path)
    args = parser.parse_args()
    seed_summary = read(args.seed_log)[1] if args.seed_log else "not run"
    a, atotal, accounting_a = read(args.a)
    b, btotal, accounting_b = read(args.b)
    if set(a) != set(b):
        raise ValueError("stub case sets differ")
    source = args.a.read_text()
    coverage = source.split("COVERAGE-BEGIN\n", 1)[1].split("COVERAGE-END\n", 1)[0]
    columns = [line.split("\t") for line in coverage.splitlines()[1:]]
    names = [row[0] for row in columns]
    if len(names) != len(set(names)) or set(names) != set(a):
        raise ValueError("coverage/result case sets differ")
    out = Path(__file__).resolve().parent
    (out / "COVERAGE.tsv").write_text(coverage)
    for label, rows in (("A", a), ("B", b)):
        (out / f"STUB-{label}.tsv").write_text("case\tresult\tseconds\toutput\n" + "".join(
            f"{name}\t{rows[name]['result']}\t{rows[name]['seconds']}\t{rows[name]['detail'] or '-'}\n"
            for name in names))
    groups: dict[str, list[str]] = collections.defaultdict(list)
    for name, _, family, _ in columns:
        groups[family].append(name)
    def stat(rows: dict[str, Any], items: list[str], key: str) -> int:
        if key == "pass":
            return sum(rows[name]["result"] == "PASS" for name in items)
        return sum(bool(rows[name][key]) for name in items)
    credited = [name for name in names if a[name]["red"] or b[name]["red"]]
    uncredited = [name for name in names if name not in credited]
    unreached = [name for name in names if not (a[name]["reached"] or b[name]["reached"])]
    both_green = [name for name in names if a[name]["result"] == b[name]["result"] == "PASS"]
    d4_input = [row for row in columns if row[2] not in ("F10", "F11") and
                (row[2] != "F9" or row[0] == "C9.presentation.lake-progress")]
    d4_direct = [name for name in names if name.startswith("C8.d4.")]
    tuple_direct = [name for name in names if name.startswith(("C3.status.", "C4.compat.")) and
                    not name.endswith(("missing-registry", "unreadable"))]
    table = ["| family | cases | A PASS / target-red | B PASS / target-red | credited | unreached |\n",
             "|---|---:|---:|---:|---:|---:|\n"]
    for family, (description, _) in FAMILIES.items():
        items = groups[family]
        table.append(f"| {family} {description} | {len(items)} | {stat(a, items, 'pass')} / "
                     f"{stat(a, items, 'red')} | {stat(b, items, 'pass')} / {stat(b, items, 'red')} | "
                     f"{sum(name in credited for name in items)} | {sum(name in unreached for name in items)} |\n")
    report = ["# U4 C — blind suite (tester-5)\n\n## Verdict\n\n", *table,
              f"\n{len(names)} cases; {len(credited)} target-red on ≥1 stub; {len(uncredited)} "
              f"uncredited; {len(unreached)} unreached on both. No real-C green claim.\n\n",
              "## Run + layout\n\n",
              "- `tools/vflab-run bash tests/index/run.sh` builds both binaries + the tested "
              "load/write-fault shim, then runs the suite. `FVDEP_INDEX_JOBS` = 3 by default "
              "(1..6 accepted); `FVDEP_INDEX_CASE` selects a substring; `FVDEP_TEST_SEED` overrides "
              "seed `4108190722` (`0xf4de0402`). Remote settings: "
              "`tools/vflab-run env VAR=value bash tests/index/run.sh`.\n",
              "- `fixtures.py`: minimal source-generated libraries for validation/status, copies "
              "of the launch library for closure/purity, independent canonical index layouts + "
              "isolated Git histories. Minimal fixtures test indexing, not RFC/SemVer fidelity.\n",
              "- `reference.py`: independent C6 + D5 walk, amended by directives D1–D3. No product "
              "decoder/schema data imported. J text failures are explicit J1–J3 goldens.\n",
              "- `library_cases.py`, `driver_cases.py`: source-derived predicates; shared fixture "
              "observations avoid duplicate index calls. `suite.py`: single-flight fixture cache "
              "+ bounded fixture-group pool + global subprocess semaphore; each case prints "
              "one timed result; top ten times + totals.\n",
              "- `COVERAGE.tsv`, `STUB-A.tsv`, `STUB-B.tsv`: every case, source, family + actual "
              "output (`-` = empty detail). `record.py A.log B.log --families <path> "
              "--seed-log seed.log` regenerates "
              "the evidence from captured full-run logs (A includes the catalog prelude).\n\n",
              "## Source + limits\n\n",
              "- Source = committed U4 C1–C9, interface §§1–3, library Naming/Registry, U3 J1–J4 "
              "+ D5, directives D1–D4 (D3 rev2). `tests/acceptance/library_fixtures.py` + `test_library.py` "
              "read as fixture-construction references alone. Real C stays unread + unrun.\n",
              "- Exact diagnostics/streams/order pinned where C9 fixes them. Lake progress "
              "content stays free but no raw Cc is allowed (D3 rev2); the suffix of "
              "build/load/replay/IO errors remains free as the contract states. "
              "Refusal cases also check index-byte preservation.\n",
              "- Independent identity oracle = H2 framing + H3 entry tag + stdlib SHA256 over "
              "the minimal fixture's known three-file closure; baseline + every file perturbed. "
              "Metamorphic launch checks: proof exclusion, comment byte, exact importer changes, "
              "unrelated entry, links/aliases/alternate roots.\n",
              "- Decode: every field's missing/extra/wrong-kind classes, syntax/bounds, each wire "
              "status/axiom combination, exact D5 order + pointer escaping, J failures, every "
              "Cc character in pointer/value presentation + the pre-escape 64-byte choice. Generated "
              "round trips/normalization = 48 seeded valid documents each, not exhaustive.\n",
              "- History: root/absent/invalid snapshots, every named violation, HEAD/parent order, "
              "retractions + preserved removal witnesses, divergent merge parents, missing "
              "parent, shallow + non-worktree precedence. Git SHAs enter expected lines from "
              "fixture construction, never product output.\n",
              "- Default width 3 limits simultaneous product/build calls. Cost bound = design "
              "estimate from the brief (≈20 min / ≤20G on real C), not a measurement; real C "
              "was not run. Stub accounting below records measured authoring cost.\n",
              "- A fixture setup/build/timeout failure or an unavailable prerequisite is never "
              "credited. `blocked:` marks an invariant whose required successful index is absent "
              "on that stub. Such a case needs another stub's target assertion or a MAIN mutant.\n",
              "- Full gate, fuzz campaigns + real-C green run intentionally not performed.\n\n",
              "## Verification\n\n",
              "- vflab: both executable builds, C load/write-fault positive controls, pinned Ruff, "
              "Pyrefly (0 diagnostics) + ShellCheck pass. Every non-build-failure library fixture "
              "compiles through its independent Lake preflight (full run + focused repairs/additions).\n",
              "- Initial preflights found test-harness defects: absent empty preview directory, "
              "intentional def-Prop attribution triggering the linter, wrong Lean Unicode escape, "
              "forged-declaration layout/monad lift, reserved `prefix` identifier. All repaired "
              "from compiler diagnostics; those setup failures earn no credit. Final full runs "
              "contain none.\n",
              "- Final grading uses a 20G vflab run cap; measured peaks below. No case skipped "
              f"or xfailed. {len(both_green)} cases green on both + "
              f"{len(uncredited) - len(both_green)} other no-red invariants stay uncredited, named below.\n\n",
              "## Stub runs\n\n",
              "| revision | command | output |\n|---|---|---|\n",
              f"| A `e7af5d9` | `tools/vflab-run bash tests/index/run.sh` (+ catalog prelude) | `{atotal}` |\n",
              f"| B `c281840` | `tools/vflab-run bash tests/index/run.sh` | `{btotal}` |\n\n",
              f"A: `{accounting_a}`\n\nB: `{accounting_b}`\n\n",
              f"Seed/width override (stub B, seed 1, width 2, `C11.property.roundtrip`): `{seed_summary}`. "
              "This grades the harness override, not real-C correctness.\n\n",
              "## Questions for MAIN\n\n",
              "- C9's module-specific V2 duplicate reason is dominated: V1 makes each module "
              "determine its id/version, so a repeated module reaches `listed twice` first. "
              "The suite pins that earlier refusal; it does not claim the dominated line fired.\n",
              "- D1/D2 close the decoder pointer questions: general-kind mismatches retain "
              "`wrong_type`; in-kind rule failures are `bad_value`. D3 fixes last-stage "
              "Unicode Cc escaping (C0 + DEL/C1) + the C6 label/reason control set. No open "
              "contract question.\n",
              "- Cases without a target red need MAIN's predicate-specific mutants; ids below. "
              "A green-on-both or blocked-then-green invariant receives no automatic credit.\n\n",
              "## D4\n\n",
              "Existing expectation changes: none. Existing accepted module lists contain entry "
              "references, not inline records; proof maps already use tuples. D4 adds the direct "
              "inline-record, outside-origin helper + read-order fixtures listed below.\n\n",
              "- `Prod.mk` proof-map graders: " + ", ".join(f"`{name}`" for name in tuple_direct) + ".\n",
              "- Entry-reference-only + reader-order + origin-boundary graders: " +
              ", ".join(f"`{name}`" for name in d4_direct) + ".\n",
              "- Existing positive root-module read-through/let/have/constructor case: "
              "`C12.registry.accepted-forms`. Existing reached-root unreadable helper: "
              "`C8.form.root-helper` + `.unchanged`; the final read slot is "
              "`C8.form.removed` + `.unchanged`.\n\n",
              "Conservative inventory of every registry-command fixture touching these forms "
              "(early-stop guard cases included; this inventory alone claims no reader coverage): "
              + ", ".join(f"`{row[0]}`" for row in d4_input) + ".\n\n",
              "## Credit gaps\n\n",
              "Both green: " + (", ".join(f"`{name}`" for name in both_green) or "none") + ".\n\n",
              "All uncredited: " + (", ".join(f"`{name}`" for name in uncredited) or "none") + ".\n\n",
              "Unreached on both: " + (", ".join(f"`{name}`" for name in unreached) or "none") + ".\n\n",
              "## Per-case verdicts\n\n| case | A | B | credit |\n|---|---|---|---|\n"]
    for name in names:
        credit = "stub-red" if name in credited else "unreached" if name in unreached else "mutant owed"
        report.append(f"| `{name}` | {a[name]['result']} | {b[name]['result']} | {credit} |\n")
    (out / "REPORT.md").write_text("".join(report))
    family_file = ["# tester-5 batch 2 — case families\n\n",
                   "| family | contract clauses | cases | red on stub A (e7af5d9) | red on stub B (c281840) | green on both (ids in REPORT) |\n",
                   "|---|---|---:|---:|---:|---|\n"]
    for family, (description, clauses) in FAMILIES.items():
        items = groups[family]
        family_file.append(f"| {family} {description} | {clauses} | {len(items)} | "
                           f"{stat(a, items, 'red')} | {stat(b, items, 'red')} | "
                           f"{sum(name in both_green for name in items)}; REPORT.md |\n")
    family_file.append(f"\nSummary: {len(names)} cases; {len(credited)} target-red; "
                       f"{len(uncredited)} mutant credit owed; {len(unreached)} unreached. "
                       "V2's module-specific duplicate line is precedence-dominated; its earlier "
                       "listed-twice refusal is pinned. Real C unrun.\n")
    args.families.write_text("".join(family_file))
    print(f"RECORDED {len(names)} cases; target-red={len(credited)} uncredited={len(uncredited)} "
          f"unreached={len(unreached)}")


if __name__ == "__main__":
    main()
