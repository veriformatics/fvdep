# Gate

- Gate = `tools/gate.sh` from any cwd, run direct (one awk step, < 1 s). Steps: `spec-lint` = `.agent/spec-lint` on `.agent/spec.md` (template `Session flow` shape check, gate from IMPLEMENT on). Fast gate = the same command. IMPLEMENT's gate unit extends or replaces this script + records it here; no CI workflow yet ⇒ the full gate runs locally.
- Output: `<step> rc=N <s>s` per step, `gate rc=N <s>s` last; one row per step → `.gate/ledger.tsv` (gitignored; columns in `tools/gate.sh` header). Red → set its `class` cell (product | gate | flake | planted) before a rerun counts.
- `prototype/fvdep/` = outside the gate today; a change reaching it → its `Artifacts` smoke (`tour.sh` + probes).
