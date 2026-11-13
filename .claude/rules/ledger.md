---
paths:
  - "tool/Main.lean"
  - "tool/FvdepCore.lean"
  - "tool/FvdepCore/**"
  - "tool/FvdepIO.lean"
  - "tool/FvdepIO/**"
  - "tool/FvdepLedger.lean"
  - "tool/FvdepLedger/**"
  - "tool/LedgerMain.lean"
  - "tool/FvdepLedgerFixtures.lean"
  - "tool/FvdepLedgerFixtures/**"
  - "tests/ledger/**"
  - "docs/verification.md"
---

# Coverage ledger (contract `docs/contracts/U2-core.md` L1–L9)

- Stage `coverage` (shard `lean`, fast gate too) = `fvdep-ledger --check ../docs/verification.md` (in `tool/`): binds each claim about fvdep's own code to a theorem about the executed function on its shipped call path: every owned definition `main` reaches lies in some row's subject closure; each claim = a `Prop` definition in `tool/FvdepLedger/Rows.lean` (`*Claims` namespaces) whose theorem's type equals it as a term (alpha-equivalence; defeq is not enough); axioms ⊆ {propext, Classical.choice, Quot.sound}; `leanchecker` replays every owned module (a `debug.skipKernelTC` forgery passes `#print axioms`).
- Stage `ledger-suite` (shard `lean`, fast gate too) = `bash tests/ledger/run.sh`: cases in parallel (`FVDEP_LEDGER_JOBS`, default nproc; `FVDEP_LEDGER_ONLY=<id>` = one case). The fast gate reuses a green verdict while its input closure (checker, fixtures, driver, Lake configs, toolchain pins: `ledger_suite_key` in `tools/gate.sh`) is byte-identical; the full gate always runs it.
- An edit to a row, statement, theorem or any definition inside a covered closure → `bash tools/ledger-doc.sh` regenerates `docs/verification.md` (pretty-printed statements + `Expr.hash` = drift detection); findings print one line each, `ledger: <component|root>: <code>: <detail>`.
- New theorem → its statement via `tools/ledger-stmts.py` (JSON on stdin, docstring at its top): the theorem header's own text, so it elaborates to the same term under the same `open`s; wrap lines over 100 columns by hand. A pattern lambda `fun (a, b) => …` inside a type creates a per-declaration `match_` constant ⇒ statement ≠ theorem type: write `fun x => … x.1 x.2`.
- `main` = `fun a => interpreter (plan a)` exactly, never a row subject. An empty path needs `noCaller` = an open Tasks unit (`- [ ] U<n> `) or `support` (subject inside the closure of a row with a valid path; whether its claims serve that row = the faithfulness review's call).
- Planted inputs = `tests/ledger/` (blind suite, tester-2): fixture modules `tool/FvdepLedgerFixtures/` (generated: `tests/ledger/generate.py` + `regenerate.sh` rebuild them byte-identically; layout = the generator's + lean-fmt's, outside `lean-style`'s line rules), cases `cases.tsv` + 8 seeded byte mutations of the doc; each breach → rc 1 naming its code, clean controls → rc 0, usage + load failures → rc 2. Its firing record = red on the accept-all stub checker (5fab964, branch `wt/tester-2`). A checker change reruns it; an expected value changes only on evidence that the case errs against the contract. Probes: `coverage` (one doc byte off → `ledger: root: doc:`), `ledger-suite` (a flipped expected rc → `FAIL T5`).
- Closed theorems count after an astra statement-faithfulness review (`.claude/rules/tiers.md`).
