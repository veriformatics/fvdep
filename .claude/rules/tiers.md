---
paths:
  - "docs/contracts/**"
  - ".agent/review.md"
---

# Assurance tiers (CLAUDE.md `Engineering`, as applied here)

- kernel = judgment-bearing code + specs (verdicts, statements, policy, exit mappings, gate predicates, lock transitions, readers the classifier trusts) → `consultant` on the contract before code, `tester` suite from it, full adversarial battery; a proof-only part (closed theorems about the shipped function) → an independent statement-faithfulness review (astra lane) of each definition + theorem before credit.
- data = producers a downstream check re-verifies (metadata revalidated by digests or `lake build`, presentation) → one structural validator + a live spot-check; defects fix forward.
- docs = consistency pass.
- Each unit's contract (`docs/contracts/U<n>-*.md`) declares the tier of every part; a judgment-bearing part inside glue (an exit-code mapping, a gate verdict) is kernel.
