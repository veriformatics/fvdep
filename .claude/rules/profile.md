---
paths:
  - "tool/FvdepCore/Profile/**"
  - "tool/FvdepIO/Parse.lean"
  - "tool/FvdepIO/Profile.lean"
  - "tool/FvdepAudit/Profile/**"
  - "tool/FvdepDev/Witness.lean"
  - "tool/FvdepDev/Differential.lean"
  - "tests/profile/**"
  - "docs/profile-freeze.txt"
---

# Implementation profile v1 (contract `docs/contracts/U6-profile.md`)

- Tree layouts = Lean 4.35's, read from real parses: `fvdep-dev profile tree <file>` dumps them, `fvdep-dev profile differential` (stage `profile-witness`) pins the child's trees + grammar order to the frontend's ⇒ a hand-built `Tree` in `lake test` copies a dumped layout (a fixture of another shape tests nothing Lean produces). Every tree-shape read is exact + a miss = `shape` (K0').
- The specs (`FvdepAudit.Profile.{Walk,Stage,Barrier}.Spec`, `FvdepAudit.Profile.Spec`) = the rules' normative text; the code equals them by the C2 claims (`walkFirst` … `judgeExact`, `.claude/rules/ledger.md`) ⇒ a rule change edits spec + code + proof together. Shared spec text = the layout readers (`shapeOk`, `headerParts`, `keywordSlot`, `importParts`, `modifierSlot`, `identAt`), `generated`, `least`, `intake`, `grammars`, `outcomeOf`, `dotted`, `cutDetail`; one data fact read by `decide`: `anchors_well` (anchor paths non-empty, a wildcard only last).
- A table or anchor edit → a witness for each new target in `tests/profile/witness/*.lean` (stage `profile-witness`: every target accepted + compiled on the same bytes; an entry no compiling code produces leaves the table, an optional anchor becomes required) + the freeze re-recorded (`fvdep-ledger --freeze-print`, `.claude/rules/ledger.md`); once v1 is frozen (U6's close) a rule or datum change = a new `profileId` + requalification.
- The child ends a batch as infrastructure only for faults of its own (a failed load, a signal, a cap of the step) ⇒ every consumer-caused failure is decided as a finding before the effect that would crash on it: a clean header's toolchain imports are read present (`FvdepIO.Parse.presence`: Lean's `modToFilePath` under the sysroot) before any grammar loads (contract U6 I1; `lake test` + `header.import.Std.NoSuch`).
- Lean runs `main` on a `lean_run_main` thread (1 GiB by default) ⇒ a stack test sizes it with `LEAN_STACK_SIZE_KB`; `ulimit -s` binds only the initial thread.
