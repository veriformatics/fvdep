---
paths:
  - "tests/**"
  - "tool/Tests.lean"
  - "tool/Tests/**"
  - "docs/contracts/**"
---

# Test form (adapts CLAUDE.md `Engineering` → `Tests/verification`)

- A contract predicate proved as a closed Lean theorem about the shipped function covers every input ⇒ that proof = its property test (a generated test of it cannot fail); a predicate without a closed proof → a property-based test, seed fixed + printed (`FVDEP_TEST_SEED` overrides for exploration).
- Proofs leave out what they do not model ⇒ tests still cover IO, FFI glue, the compiled C, the sandbox + external tools, and resources (time, memory, process cleanup). Byte-level readers (lockfiles, JSON, TOML) + native C get a coverage-guided fuzz target (sanitizers on for C); campaigns run in the campaign tier, the gate replays the committed corpus + every crash input.
- `lake test` (in `tool/`) = the Lean driver: one PASS/FAIL line per case, the slowest case, exit = failures. `tests/cli/smoke.sh <binary>` = the built binary's streams + exit codes. The blind acceptance suite (`tests/acceptance/`, branch `wt/tester-1`) merges unit by unit as tests turn green; its expected values change only on evidence that a test errs against the contract.
