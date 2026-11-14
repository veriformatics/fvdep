"""Regenerate the batch-1 report from the two captured vflab stdout/stderr logs."""
from __future__ import annotations

import argparse
import collections
from pathlib import Path


def read_run(path: Path) -> tuple[dict[str, tuple[str, str, str]], str, str]:
    text = path.read_text()
    rows = {}
    for line in text.splitlines():
        if line.startswith(("PASS ", "FAIL ")):
            result, rest = line.split(" ", 1)
            name, seconds, detail = rest.split("\t", 2)
            if name in rows:
                raise ValueError(f"duplicate result: {name}")
            rows[name] = (result, seconds, detail)
    totals = next(line for line in text.splitlines() if line.startswith("TOTAL "))
    accounting = next(line for line in text.splitlines() if line.startswith(
        "vflab-run: Finished with result:"))
    if int(totals.split()[1]) != len(rows):
        raise ValueError("partial result log")
    return rows, totals, accounting


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("a", type=Path)
    parser.add_argument("b", type=Path)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--seed-log", type=Path)
    args = parser.parse_args()
    a, atotal, accounting_a = read_run(args.a)
    b, btotal, accounting_b = read_run(args.b)
    if list(a) != list(b):
        raise ValueError("stub case lists differ")
    out = args.out.resolve()
    source = args.a.read_text()
    coverage = source.split("COVERAGE-BEGIN\n", 1)[1].split("COVERAGE-END\n", 1)[0]
    names = [row.split("\t")[0] for row in coverage.splitlines()[1:]]
    if names != list(a):
        raise ValueError("coverage/result order mismatch")
    (out / "COVERAGE.tsv").write_text(coverage)
    for label, rows in (("A", a), ("B", b)):
        data = "case\tresult\tseconds\toutput\n" + "".join(
            f"{name}\t{result}\t{seconds}\t{detail or '-'}\n"
            for name, (result, seconds, detail) in rows.items())
        (out / f"STUB-{label}.tsv").write_text(data)
    group_names = ["A.b64", "A.semver", "B.value", "B.request", "B.reply", "B.lines", "B.sig", "B.cli"]
    groups = collections.defaultdict(list)
    for name in a:
        groups[".".join(name.split(".")[:2])].append(name)
    both_green = [name for name in a if a[name][0] == b[name][0] == "PASS"]
    targeted = [name for name in a if name not in both_green]
    seed_summary = "not run"
    if args.seed_log:
        _, seed_summary, _ = read_run(args.seed_log)
    rows = ["# U4 batch 1 — tester-5\n\n## Verdict\n\n",
            "| surface | cases | A PASS / FAIL | B PASS / FAIL | red on ≥1 stub |\n",
            "|---|---:|---:|---:|---:|\n"]
    for group in group_names:
        cases = groups[group]
        ap = sum(a[name][0] == "PASS" for name in cases)
        bp = sum(b[name][0] == "PASS" for name in cases)
        red = sum(a[name][0] == "FAIL" or b[name][0] == "FAIL" for name in cases)
        rows.append(f"| {group} | {len(cases)} | {ap} / {len(cases) - ap} | "
                    f"{bp} / {len(cases) - bp} | {red} |\n")
    rows.extend([
        f"\n{len(a)} cases; {len(targeted)} red on ≥1 stub; {len(both_green)} green on both "
        "(uncredited pending product mutants). Expected real-implementation reds = none. "
        "Real B remains unread + unrun; this is a prediction, not a green claim.\n\n",
        "## Run + layout\n\n",
        "- Canonical suite command (inside this worktree): "
        "`tools/vflab-run bash tests/library/run.sh`. A adds a `--list` prelude for the "
        "coverage catalog + the static checks below; B runs the canonical command alone.\n",
        "- Seed = `4108190721` (`0xf4de0401`). Exploration: "
        "`tools/vflab-run env FVDEP_TEST_SEED=123 bash tests/library/run.sh`. "
        "`FVDEP_LIBRARY_CASE` (inside the remote command) selects a case substring.\n",
        "- `LibraryHarness.lean` + `Driver.lean`: direct calls to the six launch specs, `render`, "
        "protocol APIs + `sigOf`. Independent test transport = length-prefixed values inside "
        "hex lines; no product codec transports its own test inputs/results.\n",
        "- `reference.py`: independent RFC4648 bit-stream encoder + strict decoder, SemVer "
        "ASCII grammar + whole-type first-difference comparator, B2 layouts + J4 printer. "
        "No product definitions imported; stdlib base64/SemVer packages unused.\n",
        "- `suite.py`: cases + fixed-seed properties; each PASS/FAIL line names its case, "
        "duration + failure detail. Slowest 10 cases printed; nonzero exit counts failures "
        "(saturated at 255). CLI tests compare raw stdout + exit codes.\n",
        "- `COVERAGE.tsv`: every case → source clause + domain. `STUB-A.tsv`, `STUB-B.tsv`: "
        "complete per-case outputs + seconds. Per-case result/credit table below.\n",
        "- `record.py A.log B.log --seed-log seed.log`: idempotent regeneration of these four "
        "evidence files.\n\n",
        "## Independent domains\n\n",
        "- RFC4648 §10 vectors, all 256 one-byte + 65,536 two-byte inputs for both encoders "
        "+ decoder round trips. This is exhaustive at lengths 1/2, not at longer lengths. "
        "Longer lengths = 136 seeded samples (0..129, 255/256/257, 1023/1024/1025). "
        "Per alphabet: all 108 nonzero filling-bit tails, all 272 padding-position masks at "
        "4/8 characters, every ASCII character at every position in one quartet (512), "
        "named non-ASCII/control/alphabet refusals + seeded mutated canonical texts.\n",
        "- SemVer §§2/9/10 grammar witnesses/refusals incl. 256-digit numerics; all 64 §11 "
        "chain pairs; invalid whole-type alnum/build witnesses. Generated: 256 Valid values "
        "+ 320 whole-type triples, plus 64 build-only comparisons. Properties: render "
        "round trip, swap, trans, eqIff, independent precedence, build ignored.\n",
        "- B2: all seven value classes; ±(2^53−1), next integers as decimal strings, "
        "canonical decimal refusals, UTF16 0/65535/65536 + surrogates as code units, "
        "Version exact keys + tags. Text byte caps checked with ASCII/multibyte/non-BMP. "
        "160 seeded typed values grade encode/decode layouts.\n",
        "- B3: valid/invalid JSON requests, arity/op/kind/key refusals, J1/J2 string/depth/"
        "number/UTF8/surrogate bounds, canonical reply bytes + LF, arbitrary-byte LF "
        "framing (128 seeded streams). Replies above the request cap remain whole.\n",
        "- B1 sigOf: six launch function-type shapes, every table type with plain/optional "
        "result, multiargument arrows, non-encodable types + dependent/higher-order shapes.\n",
        "- B5 CLI: six targets, EOF, empty line, CRLF, final fragment, failure recovery, "
        "usage/target refusals, stdin preservation, 65536-character decode request → "
        "98304-character hex result (both alphabets; byte-for-byte whole stdout).\n\n",
        "## Checks + captured runs\n\n",
        "| check | result |\n|---|---|\n",
        "| vflab Lean harness build | PASS; 36 targets |\n",
        "| Ruff (pinned) on tests/library | PASS |\n",
        "| Pyrefly (pinned, warning severity) on tests/library | PASS; 0 diagnostics |\n",
        "| ShellCheck (pinned) on tests/library/run.sh | PASS |\n",
        f"| Seed override `1`, `A.semver.property` | `{seed_summary}` |\n",
        "| Lean source layout | lines ≤100 characters |\n",
        "| LSP hover on Driver.lean | no server for .lean; build diagnostics used |\n",
        "| Full gate | NOT RUN (brief) |\n",
        "| Real B implementation | NOT RUN (blindness) |\n\n",
        "Static command: `tools/vflab-run bash -c '.tools/bin/ruff check --config ruff.toml "
        "--output-format concise tests/library; .tools/bin/pyrefly check --config pyrefly.toml "
        "--output-format=min-text --min-severity=warn tests/library; "
        ".tools/bin/shellcheck tests/library/run.sh'` (final run uses `set -e`). "
        "The first two static attempts found test-code typing errors/warning; fixed before "
        "these final runs.\n\n",
        "| product revision | summary | suite rc | setup/build failures |\n",
        "|---|---|---:|---|\n",
        f"| stub A `b7c271a` | `{atotal}` | {min(sum(r[0] == 'FAIL' for r in a.values()), 255)} "
        "| none |\n",
        f"| stub B `f84b956` | `{btotal}` | {min(sum(r[0] == 'FAIL' for r in b.values()), 255)} "
        "| none |\n\n",
        f"A accounting: `{accounting_a}`\n\nB accounting: `{accounting_b}`\n\n",
        "Seed-check command: `tools/vflab-run env FVDEP_TEST_SEED=1 "
        "FVDEP_LIBRARY_CASE=A.semver.property bash tests/library/run.sh` → rc 0.\n\n",
        "## Questions for MAIN + credit limits\n\n",
        "- A's launch definitions are real + byte-identical across the prescribed stubs. "
        "Their green tests need product-mutant firing evidence. The write allowlist "
        "excluded library-source mutations; MAIN's B6 campaign can supply it.\n",
        "- Cases green on both stubs stay visible + uncredited (table below). A red counts "
        "only when it reaches its target assertion. `B.cli.unknown-stdin-unread` uses a "
        "finite pipe: exit 2 + an exact marker left unread. Earlier live-pipe experiments "
        "timed out on both stubs (uncredited); the final fixture reaches behavioral "
        "assertions without a timeout. No timeout contributes credit.\n",
        "- No contract/API defect identified. Not covered here: conformance trial A8, "
        "registry/index C, proof faithfulness, fuzz campaigns, real B green run. MAIN owns "
        "those parts. No target test skipped or xfailed.\n\n",
        "## Per-case results\n\n",
        "Command per row = the canonical suite command above, with the row's case selected "
        "by `FVDEP_LIBRARY_CASE`. Full stdout line = result + case + seconds + detail in "
        "the corresponding TSV (`-` = empty detail). `red` below means a stub red, "
        "not automatic mutant credit.\n\n",
        "| case | A | B | stub detection |\n|---|---|---|---|\n",
    ])
    for name in a:
        verdict = "uncredited" if name in both_green else "red"
        rows.append(f"| `{name}` | {a[name][0]} | {b[name][0]} | {verdict} |\n")
    (out / "REPORT.md").write_text("".join(rows))
    print(f"Recorded {len(a)} cases; {len(targeted)} stub reds; {len(both_green)} both green")


if __name__ == "__main__":
    main()
