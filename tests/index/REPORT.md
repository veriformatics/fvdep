# U4 C — blind suite (tester-5)

## Verdict

| family | cases | A PASS / target-red | B PASS / target-red | credited | unreached |
|---|---:|---:|---:|---:|---:|
| F1 entry rules + file checks | 74 | 37 / 37 | 0 / 74 | 74 | 0 |
| F2 identity | 8 | 1 / 1 | 2 / 6 | 6 | 0 |
| F3 status + replay + warnings | 22 | 0 / 12 | 4 / 18 | 21 | 0 |
| F4 compatibility | 8 | 0 / 4 | 2 / 6 | 7 | 0 |
| F5 notices + removed | 32 | 15 / 15 | 0 / 32 | 32 | 0 |
| F6 purity + compare + IO | 12 | 0 / 4 | 10 / 2 | 4 | 0 |
| F7 presence + toolchain | 10 | 5 / 5 | 0 / 10 | 10 | 0 |
| F8 build + load + registry forms | 26 | 12 / 14 | 0 / 26 | 26 | 0 |
| F9 CLI + precedence | 8 | 6 / 2 | 8 / 0 | 2 | 0 |
| F10 history | 27 | 0 / 27 | 9 / 18 | 27 | 0 |
| F11 decode + schema refusals | 465 | 1 / 464 | 1 / 464 | 465 | 0 |
| F12 schema output + registry forms | 9 | 2 / 4 | 1 / 8 | 8 | 0 |

701 cases; 682 target-red on ≥1 stub; 19 uncredited; 0 unreached on both. No real-C green claim.

## Run + layout

- `tools/vflab-run bash tests/index/run.sh` builds both binaries + the tested load/write-fault shim, then runs the suite. `FVDEP_INDEX_JOBS` = 3 by default (1..6 accepted); `FVDEP_INDEX_CASE` selects a substring; `FVDEP_TEST_SEED` overrides seed `4108190722` (`0xf4de0402`). Remote settings: `tools/vflab-run env VAR=value bash tests/index/run.sh`.
- `fixtures.py`: minimal source-generated libraries for validation/status, copies of the launch library for closure/purity, independent canonical index layouts + isolated Git histories. Minimal fixtures test indexing, not RFC/SemVer fidelity.
- `reference.py`: independent C6 + D5 walk, amended by directives D1–D3. No product decoder/schema data imported. J text failures are explicit J1–J3 goldens.
- `library_cases.py`, `driver_cases.py`: source-derived predicates; shared fixture observations avoid duplicate index calls. `suite.py`: single-flight fixture cache + bounded fixture-group pool + global subprocess semaphore; each case prints one timed result; top ten times + totals.
- `COVERAGE.tsv`, `STUB-A.tsv`, `STUB-B.tsv`: every case, source, family + actual output (`-` = empty detail). `record.py A.log B.log --families <path> --seed-log seed.log` regenerates the evidence from captured full-run logs (A includes the catalog prelude).

## Source + limits

- Source = committed U4 C1–C9, interface §§1–3, library Naming/Registry, U3 J1–J4 + D5, directives D1–D4 (D3 rev2). `tests/acceptance/library_fixtures.py` + `test_library.py` read as fixture-construction references alone. Real C stays unread + unrun.
- Exact diagnostics/streams/order pinned where C9 fixes them. Lake progress content stays free but no raw Cc is allowed (D3 rev2); the suffix of build/load/replay/IO errors remains free as the contract states. Refusal cases also check index-byte preservation.
- Independent identity oracle = H2 framing + H3 entry tag + stdlib SHA256 over the minimal fixture's known three-file closure; baseline + every file perturbed. Metamorphic launch checks: proof exclusion, comment byte, exact importer changes, unrelated entry, links/aliases/alternate roots.
- Decode: every field's missing/extra/wrong-kind classes, syntax/bounds, each wire status/axiom combination, exact D5 order + pointer escaping, J failures, every Cc character in pointer/value presentation + the pre-escape 64-byte choice. Generated round trips/normalization = 48 seeded valid documents each, not exhaustive.
- History: root/absent/invalid snapshots, every named violation, HEAD/parent order, retractions + preserved removal witnesses, divergent merge parents, missing parent, shallow + non-worktree precedence. Git SHAs enter expected lines from fixture construction, never product output.
- Default width 3 limits simultaneous product/build calls. Cost bound = design estimate from the brief (≈20 min / ≤20G on real C), not a measurement; real C was not run. Stub accounting below records measured authoring cost.
- A fixture setup/build/timeout failure or an unavailable prerequisite is never credited. `blocked:` marks an invariant whose required successful index is absent on that stub. Such a case needs another stub's target assertion or a MAIN mutant.
- Full gate, fuzz campaigns + real-C green run intentionally not performed.

## Verification

- vflab: both executable builds, C load/write-fault positive controls, pinned Ruff, Pyrefly (0 diagnostics) + ShellCheck pass. Every non-build-failure library fixture compiles through its independent Lake preflight (full run + focused repairs/additions).
- Initial preflights found test-harness defects: absent empty preview directory, intentional def-Prop attribution triggering the linter, wrong Lean Unicode escape, forged-declaration layout/monad lift, reserved `prefix` identifier. All repaired from compiler diagnostics; those setup failures earn no credit. Final full runs contain none.
- Final grading uses a 20G vflab run cap; measured peaks below. No case skipped or xfailed. 6 cases green on both + 13 other no-red invariants stay uncredited, named below.

## Stub runs

| revision | command | output |
|---|---|---|
| A `65f5d58` (main; run at its pre-rewrite `e7af5d9`, `.agent/archive/sha-map.tsv`) | `tools/vflab-run bash tests/index/run.sh` (+ catalog prelude) | `TOTAL 701 PASS 79 FAIL 622` |
| B `c281840` (`wip/u4c-red`, old history) | `tools/vflab-run bash tests/index/run.sh` | `TOTAL 701 PASS 37 FAIL 664` |

A: `vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=255/EXCEPTION; Service runtime: 4.258s; CPU time consumed: 9.093s; Memory peak: 128.1M (swap: 0B)`

B: `vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=255/EXCEPTION; Service runtime: 4.131s; CPU time consumed: 9.292s; Memory peak: 122.2M (swap: 0B)`

Seed/width override (stub B, seed 1, width 2, `C11.property.roundtrip`): `TOTAL 1 PASS 1 FAIL 0`. This grades the harness override, not real-C correctness.

## Questions for MAIN

- C9's module-specific V2 duplicate reason is dominated: V1 makes each module determine its id/version, so a repeated module reaches `listed twice` first. The suite pins that earlier refusal; it does not claim the dominated line fired.
- D1/D2 close the decoder pointer questions: general-kind mismatches retain `wrong_type`; in-kind rule failures are `bad_value`. D3 fixes last-stage Unicode Cc escaping (C0 + DEL/C1) + the C6 label/reason control set. No open contract question.
- Cases without a target red need MAIN's predicate-specific mutants; ids below. A green-on-both or blocked-then-green invariant receives no automatic credit.

## D4

Existing expectation changes: none. Existing accepted module lists contain entry references, not inline records; proof maps already use tuples. D4 adds the direct inline-record, outside-origin helper + read-order fixtures listed below.

- `Prod.mk` proof-map graders: `C3.status.proven`, `C3.status.sorry`, `C3.status.custom`, `C3.status.unmapped`, `C3.status.twice`, `C3.status.not-theorem`, `C3.status.outside`, `C3.status.wrong-statement`, `C4.compat.proven`, `C4.compat.wrong`, `C4.compat.unmapped`, `C4.compat.ignored`.
- Entry-reference-only + reader-order + origin-boundary graders: `C8.d4.inline-entry`, `C8.d4.inline-entry.unchanged`, `C8.d4.outside-helper`, `C8.d4.outside-helper.unchanged`, `C8.d4.order-modules`, `C8.d4.order-modules.unchanged`, `C8.d4.order-profiles`, `C8.d4.order-profiles.unchanged`, `C8.d4.order-notices`, `C8.d4.order-notices.unchanged`.
- Existing positive root-module read-through/let/have/constructor case: `C12.registry.accepted-forms`. Existing reached-root unreadable helper: `C8.form.root-helper` + `.unchanged`; the final read slot is `C8.form.removed` + `.unchanged`.

Conservative inventory of every registry-command fixture touching these forms (early-stop guard cases included; this inventory alone claims no reader coverage): `C1.v1.id`, `C1.v1.id.unchanged`, `C1.v1.version`, `C1.v1.version.unchanged`, `C1.v1.module`, `C1.v1.module.unchanged`, `C1.v1.id-control-00`, `C1.v1.id-control-00.unchanged`, `C1.v1.id-control-0a`, `C1.v1.id-control-0a.unchanged`, `C1.v1.id-control-85`, `C1.v1.id-control-85.unchanged`, `C1.v1.version-control`, `C1.v1.version-control.unchanged`, `C1.v1.order`, `C1.v1.order.unchanged`, `C1.v2.repeated-id`, `C1.v2.repeated-id.unchanged`, `C1.v2.unlisted`, `C1.v2.unlisted.unchanged`, `C1.v3.foreign-spec`, `C1.v3.foreign-spec.unchanged`, `C1.v3.theorem-spec`, `C1.v3.theorem-spec.unchanged`, `C1.v3.type`, `C1.v3.type.unchanged`, `C1.v3.partial`, `C1.v3.partial.unchanged`, `C1.v3.unsafe`, `C1.v3.unsafe.unchanged`, `C1.v3.implemented_by`, `C1.v3.implemented_by.unchanged`, `C1.v3.extern`, `C1.v3.extern.unchanged`, `C1.v3.opaque`, `C1.v3.opaque.unchanged`, `C1.v3.noncomputable`, `C1.v3.noncomputable.unchanged`, `C1.v3.abi-root`, `C1.v3.abi-root.unchanged`, `C1.v4.not-prop`, `C1.v4.not-prop.unchanged`, `C1.v4.theorem`, `C1.v4.theorem.unchanged`, `C1.v4.foreign`, `C1.v4.foreign.unchanged`, `C1.v4.repeat`, `C1.v4.repeat.unchanged`, `C1.v5.module`, `C1.v5.module.unchanged`, `C1.v5.type`, `C1.v5.type.unchanged`, `C1.v6.unlisted`, `C1.v6.unlisted.unchanged`, `C1.v6.same`, `C1.v6.same.unchanged`, `C1.v6.bad`, `C1.v6.bad.unchanged`, `C1.v6.type`, `C1.v6.type.unchanged`, `C1.v7.holds`, `C1.v7.holds.unchanged`, `C1.v7.imports`, `C1.v7.imports.unchanged`, `C1.c4.link`, `C1.c4.link.unchanged`, `C1.c4.alias`, `C1.c4.alias.unchanged`, `C1.entry-order.first`, `C1.entry-order.first.unchanged`, `C1.entry-order.reversed`, `C1.entry-order.reversed.unchanged`, `C1.v10.profiles`, `C1.v10.profiles.unchanged`, `C7.absent.lean-toolchain`, `C7.absent.lean-toolchain.unchanged`, `C7.absent.Fvdep-Registry.lean`, `C7.absent.Fvdep-Registry.lean.unchanged`, `C7.presence-before-toolchain`, `C7.presence-before-toolchain.unchanged`, `C7.toolchain-control`, `C7.toolchain-control.unchanged`, `C7.toolchain-before-build`, `C7.toolchain-before-build.unchanged`, `C8.build`, `C8.form.modules`, `C8.form.modules.unchanged`, `C8.form.notices`, `C8.form.notices.unchanged`, `C8.form.removed`, `C8.form.removed.unchanged`, `C8.form.root-helper`, `C8.form.root-helper.unchanged`, `C8.form.entry`, `C8.form.entry.unchanged`, `C8.d4.inline-entry`, `C8.d4.inline-entry.unchanged`, `C8.d4.outside-helper`, `C8.d4.outside-helper.unchanged`, `C8.d4.order-modules`, `C8.d4.order-modules.unchanged`, `C8.d4.order-profiles`, `C8.d4.order-profiles.unchanged`, `C8.d4.order-notices`, `C8.d4.order-notices.unchanged`, `C8.form.type-layout`, `C8.form.type-layout.unchanged`, `C8.form.profile-elements`, `C8.form.profile-elements.unchanged`, `C8.load`, `C3.status.proven`, `C3.warning.proven`, `C3.status.sorry`, `C3.warning.sorry`, `C3.status.custom`, `C3.warning.custom`, `C3.status.missing-registry`, `C3.warning.missing-registry`, `C3.status.unreadable`, `C3.warning.unreadable`, `C3.status.unmapped`, `C3.warning.unmapped`, `C3.status.twice`, `C3.warning.twice`, `C3.status.not-theorem`, `C3.warning.not-theorem`, `C3.status.outside`, `C3.warning.outside`, `C3.status.wrong-statement`, `C3.warning.wrong-statement`, `C3.warning.registry-order`, `C3.replay.forged`, `C4.compat.proven`, `C4.warning.proven`, `C4.compat.wrong`, `C4.warning.wrong`, `C4.compat.unmapped`, `C4.warning.unmapped`, `C4.compat.ignored`, `C4.warning.ignored`, `C5.notice.unknown`, `C5.notice.unknown.unchanged`, `C5.notice.replacement`, `C5.notice.replacement.unchanged`, `C5.notice.reason.empty`, `C5.notice.reason.empty.unchanged`, `C5.notice.reason.control`, `C5.notice.reason.control.unchanged`, `C5.notice.reason.del`, `C5.notice.reason.del.unchanged`, `C5.notice.reason.nel`, `C5.notice.reason.nel.unchanged`, `C5.notice.reason.large`, `C5.notice.reason.large.unchanged`, `C5.notice.reason.multibyte-large`, `C5.notice.reason.multibyte-large.unchanged`, `C5.removed.listed`, `C5.removed.listed.unchanged`, `C5.removed.duplicate`, `C5.removed.duplicate.unchanged`, `C5.removed.kind`, `C5.removed.kind.unchanged`, `C5.removed.digest`, `C5.removed.digest.unchanged`, `C5.removed.lastCommit`, `C5.removed.lastCommit.unchanged`, `C5.removed.toolchain`, `C5.removed.toolchain.unchanged`, `C5.removed.notice`, `C5.removed.notice.unchanged`, `C5.logs.order`, `C5.notice.cap`, `C2.identity.reference-frames`, `C2.identity.comment`, `C2.identity.proof`, `C2.identity.shared`, `C2.identity.closure-boundary`, `C2.identity.unrelated`, `C12.schema.new-version-after-index`, `C2.identity.alternate-root`, `C2.identity.alternate-root.unchanged`, `C6.purity.idempotent`, `C6.purity.check-readonly`, `C6.purity.drift-readonly`, `C6.purity.environment-artifact`, `C6.purity.absolute-path`, `C6.purity.check-current`, `C6.purity.check-drift`, `C6.purity.check-absent`, `C6.no-writer-lock`, `C6.concurrent`, `C6.io.read`, `C6.io.write`, `C9.presentation.lake-progress`, `C12.schema.launch`, `C12.bound.obligation-name`, `C12.bound.axiom-name`, `C12.bound.removed-toolchain-cc`, `C12.bound.removed-toolchain-long`, `C12.schema.empty`, `C12.schema.numeric-order`, `C12.registry.accepted-forms`.

## Credit gaps

Both green: `C9.usage.0`, `C9.usage.1`, `C9.usage.2`, `C9.usage.3`, `C9.usage.4`, `C9.usage.5`.

All uncredited: `C3.status.proven`, `C4.compat.ignored`, `C2.identity.proof`, `C2.identity.unrelated`, `C6.purity.idempotent`, `C6.purity.check-readonly`, `C6.purity.drift-readonly`, `C6.purity.environment-artifact`, `C6.purity.absolute-path`, `C6.purity.check-current`, `C6.purity.check-drift`, `C6.purity.check-absent`, `C9.usage.0`, `C9.usage.1`, `C9.usage.2`, `C9.usage.3`, `C9.usage.4`, `C9.usage.5`, `C12.schema.launch`.

Unreached on both: none.

## Per-case verdicts

| case | A | B | credit |
|---|---|---|---|
| `C1.v1.id` | FAIL | FAIL | stub-red |
| `C1.v1.id.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.version` | FAIL | FAIL | stub-red |
| `C1.v1.version.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.module` | FAIL | FAIL | stub-red |
| `C1.v1.module.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.id-control-00` | FAIL | FAIL | stub-red |
| `C1.v1.id-control-00.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.id-control-0a` | FAIL | FAIL | stub-red |
| `C1.v1.id-control-0a.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.id-control-85` | FAIL | FAIL | stub-red |
| `C1.v1.id-control-85.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.version-control` | FAIL | FAIL | stub-red |
| `C1.v1.version-control.unchanged` | PASS | FAIL | stub-red |
| `C1.v1.order` | FAIL | FAIL | stub-red |
| `C1.v1.order.unchanged` | PASS | FAIL | stub-red |
| `C1.v2.repeated-id` | FAIL | FAIL | stub-red |
| `C1.v2.repeated-id.unchanged` | PASS | FAIL | stub-red |
| `C1.v2.unlisted` | FAIL | FAIL | stub-red |
| `C1.v2.unlisted.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.foreign-spec` | FAIL | FAIL | stub-red |
| `C1.v3.foreign-spec.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.theorem-spec` | FAIL | FAIL | stub-red |
| `C1.v3.theorem-spec.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.type` | FAIL | FAIL | stub-red |
| `C1.v3.type.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.partial` | FAIL | FAIL | stub-red |
| `C1.v3.partial.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.unsafe` | FAIL | FAIL | stub-red |
| `C1.v3.unsafe.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.implemented_by` | FAIL | FAIL | stub-red |
| `C1.v3.implemented_by.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.extern` | FAIL | FAIL | stub-red |
| `C1.v3.extern.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.opaque` | FAIL | FAIL | stub-red |
| `C1.v3.opaque.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.noncomputable` | FAIL | FAIL | stub-red |
| `C1.v3.noncomputable.unchanged` | PASS | FAIL | stub-red |
| `C1.v3.abi-root` | FAIL | FAIL | stub-red |
| `C1.v3.abi-root.unchanged` | PASS | FAIL | stub-red |
| `C1.v4.not-prop` | FAIL | FAIL | stub-red |
| `C1.v4.not-prop.unchanged` | PASS | FAIL | stub-red |
| `C1.v4.theorem` | FAIL | FAIL | stub-red |
| `C1.v4.theorem.unchanged` | PASS | FAIL | stub-red |
| `C1.v4.foreign` | FAIL | FAIL | stub-red |
| `C1.v4.foreign.unchanged` | PASS | FAIL | stub-red |
| `C1.v4.repeat` | FAIL | FAIL | stub-red |
| `C1.v4.repeat.unchanged` | PASS | FAIL | stub-red |
| `C1.v5.module` | FAIL | FAIL | stub-red |
| `C1.v5.module.unchanged` | PASS | FAIL | stub-red |
| `C1.v5.type` | FAIL | FAIL | stub-red |
| `C1.v5.type.unchanged` | PASS | FAIL | stub-red |
| `C1.v6.unlisted` | FAIL | FAIL | stub-red |
| `C1.v6.unlisted.unchanged` | PASS | FAIL | stub-red |
| `C1.v6.same` | FAIL | FAIL | stub-red |
| `C1.v6.same.unchanged` | PASS | FAIL | stub-red |
| `C1.v6.bad` | FAIL | FAIL | stub-red |
| `C1.v6.bad.unchanged` | PASS | FAIL | stub-red |
| `C1.v6.type` | FAIL | FAIL | stub-red |
| `C1.v6.type.unchanged` | PASS | FAIL | stub-red |
| `C1.v7.holds` | FAIL | FAIL | stub-red |
| `C1.v7.holds.unchanged` | PASS | FAIL | stub-red |
| `C1.v7.imports` | FAIL | FAIL | stub-red |
| `C1.v7.imports.unchanged` | PASS | FAIL | stub-red |
| `C1.c4.link` | FAIL | FAIL | stub-red |
| `C1.c4.link.unchanged` | PASS | FAIL | stub-red |
| `C1.c4.alias` | FAIL | FAIL | stub-red |
| `C1.c4.alias.unchanged` | PASS | FAIL | stub-red |
| `C1.entry-order.first` | FAIL | FAIL | stub-red |
| `C1.entry-order.first.unchanged` | PASS | FAIL | stub-red |
| `C1.entry-order.reversed` | FAIL | FAIL | stub-red |
| `C1.entry-order.reversed.unchanged` | PASS | FAIL | stub-red |
| `C1.v10.profiles` | FAIL | FAIL | stub-red |
| `C1.v10.profiles.unchanged` | PASS | FAIL | stub-red |
| `C7.absent.lean-toolchain` | FAIL | FAIL | stub-red |
| `C7.absent.lean-toolchain.unchanged` | PASS | FAIL | stub-red |
| `C7.absent.Fvdep-Registry.lean` | FAIL | FAIL | stub-red |
| `C7.absent.Fvdep-Registry.lean.unchanged` | PASS | FAIL | stub-red |
| `C7.presence-before-toolchain` | FAIL | FAIL | stub-red |
| `C7.presence-before-toolchain.unchanged` | PASS | FAIL | stub-red |
| `C7.toolchain-control` | FAIL | FAIL | stub-red |
| `C7.toolchain-control.unchanged` | PASS | FAIL | stub-red |
| `C7.toolchain-before-build` | FAIL | FAIL | stub-red |
| `C7.toolchain-before-build.unchanged` | PASS | FAIL | stub-red |
| `C8.build` | FAIL | FAIL | stub-red |
| `C8.form.modules` | FAIL | FAIL | stub-red |
| `C8.form.modules.unchanged` | PASS | FAIL | stub-red |
| `C8.form.notices` | FAIL | FAIL | stub-red |
| `C8.form.notices.unchanged` | PASS | FAIL | stub-red |
| `C8.form.removed` | FAIL | FAIL | stub-red |
| `C8.form.removed.unchanged` | PASS | FAIL | stub-red |
| `C8.form.root-helper` | FAIL | FAIL | stub-red |
| `C8.form.root-helper.unchanged` | PASS | FAIL | stub-red |
| `C8.form.entry` | FAIL | FAIL | stub-red |
| `C8.form.entry.unchanged` | PASS | FAIL | stub-red |
| `C8.d4.inline-entry` | FAIL | FAIL | stub-red |
| `C8.d4.inline-entry.unchanged` | PASS | FAIL | stub-red |
| `C8.d4.outside-helper` | FAIL | FAIL | stub-red |
| `C8.d4.outside-helper.unchanged` | PASS | FAIL | stub-red |
| `C8.d4.order-modules` | FAIL | FAIL | stub-red |
| `C8.d4.order-modules.unchanged` | PASS | FAIL | stub-red |
| `C8.d4.order-profiles` | FAIL | FAIL | stub-red |
| `C8.d4.order-profiles.unchanged` | PASS | FAIL | stub-red |
| `C8.d4.order-notices` | FAIL | FAIL | stub-red |
| `C8.d4.order-notices.unchanged` | PASS | FAIL | stub-red |
| `C8.form.type-layout` | FAIL | FAIL | stub-red |
| `C8.form.type-layout.unchanged` | PASS | FAIL | stub-red |
| `C8.form.profile-elements` | FAIL | FAIL | stub-red |
| `C8.form.profile-elements.unchanged` | PASS | FAIL | stub-red |
| `C8.load` | FAIL | FAIL | stub-red |
| `C3.status.proven` | FAIL | PASS | mutant owed |
| `C3.warning.proven` | FAIL | PASS | stub-red |
| `C3.status.sorry` | FAIL | FAIL | stub-red |
| `C3.warning.sorry` | FAIL | PASS | stub-red |
| `C3.status.custom` | FAIL | FAIL | stub-red |
| `C3.warning.custom` | FAIL | PASS | stub-red |
| `C3.status.missing-registry` | FAIL | FAIL | stub-red |
| `C3.warning.missing-registry` | FAIL | FAIL | stub-red |
| `C3.status.unreadable` | FAIL | FAIL | stub-red |
| `C3.warning.unreadable` | FAIL | FAIL | stub-red |
| `C3.status.unmapped` | FAIL | FAIL | stub-red |
| `C3.warning.unmapped` | FAIL | FAIL | stub-red |
| `C3.status.twice` | FAIL | FAIL | stub-red |
| `C3.warning.twice` | FAIL | FAIL | stub-red |
| `C3.status.not-theorem` | FAIL | FAIL | stub-red |
| `C3.warning.not-theorem` | FAIL | FAIL | stub-red |
| `C3.status.outside` | FAIL | FAIL | stub-red |
| `C3.warning.outside` | FAIL | FAIL | stub-red |
| `C3.status.wrong-statement` | FAIL | FAIL | stub-red |
| `C3.warning.wrong-statement` | FAIL | FAIL | stub-red |
| `C3.warning.registry-order` | FAIL | FAIL | stub-red |
| `C3.replay.forged` | FAIL | FAIL | stub-red |
| `C4.compat.proven` | FAIL | FAIL | stub-red |
| `C4.warning.proven` | FAIL | PASS | stub-red |
| `C4.compat.wrong` | FAIL | FAIL | stub-red |
| `C4.warning.wrong` | FAIL | FAIL | stub-red |
| `C4.compat.unmapped` | FAIL | FAIL | stub-red |
| `C4.warning.unmapped` | FAIL | FAIL | stub-red |
| `C4.compat.ignored` | FAIL | PASS | mutant owed |
| `C4.warning.ignored` | FAIL | FAIL | stub-red |
| `C5.notice.unknown` | FAIL | FAIL | stub-red |
| `C5.notice.unknown.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.replacement` | FAIL | FAIL | stub-red |
| `C5.notice.replacement.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.reason.empty` | FAIL | FAIL | stub-red |
| `C5.notice.reason.empty.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.reason.control` | FAIL | FAIL | stub-red |
| `C5.notice.reason.control.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.reason.del` | FAIL | FAIL | stub-red |
| `C5.notice.reason.del.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.reason.nel` | FAIL | FAIL | stub-red |
| `C5.notice.reason.nel.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.reason.large` | FAIL | FAIL | stub-red |
| `C5.notice.reason.large.unchanged` | PASS | FAIL | stub-red |
| `C5.notice.reason.multibyte-large` | FAIL | FAIL | stub-red |
| `C5.notice.reason.multibyte-large.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.listed` | FAIL | FAIL | stub-red |
| `C5.removed.listed.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.duplicate` | FAIL | FAIL | stub-red |
| `C5.removed.duplicate.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.kind` | FAIL | FAIL | stub-red |
| `C5.removed.kind.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.digest` | FAIL | FAIL | stub-red |
| `C5.removed.digest.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.lastCommit` | FAIL | FAIL | stub-red |
| `C5.removed.lastCommit.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.toolchain` | FAIL | FAIL | stub-red |
| `C5.removed.toolchain.unchanged` | PASS | FAIL | stub-red |
| `C5.removed.notice` | FAIL | FAIL | stub-red |
| `C5.removed.notice.unchanged` | PASS | FAIL | stub-red |
| `C5.logs.order` | FAIL | FAIL | stub-red |
| `C5.notice.cap` | FAIL | FAIL | stub-red |
| `C2.identity.reference-frames` | FAIL | FAIL | stub-red |
| `C2.identity.comment` | FAIL | FAIL | stub-red |
| `C2.identity.proof` | FAIL | PASS | mutant owed |
| `C2.identity.shared` | FAIL | FAIL | stub-red |
| `C2.identity.closure-boundary` | FAIL | FAIL | stub-red |
| `C2.identity.unrelated` | FAIL | PASS | mutant owed |
| `C12.schema.new-version-after-index` | FAIL | FAIL | stub-red |
| `C2.identity.alternate-root` | FAIL | FAIL | stub-red |
| `C2.identity.alternate-root.unchanged` | PASS | FAIL | stub-red |
| `C6.purity.idempotent` | FAIL | PASS | mutant owed |
| `C6.purity.check-readonly` | FAIL | PASS | mutant owed |
| `C6.purity.drift-readonly` | FAIL | PASS | mutant owed |
| `C6.purity.environment-artifact` | FAIL | PASS | mutant owed |
| `C6.purity.absolute-path` | FAIL | PASS | mutant owed |
| `C6.purity.check-current` | FAIL | PASS | mutant owed |
| `C6.purity.check-drift` | FAIL | PASS | mutant owed |
| `C6.purity.check-absent` | FAIL | PASS | mutant owed |
| `C6.no-writer-lock` | FAIL | PASS | stub-red |
| `C6.concurrent` | FAIL | PASS | stub-red |
| `C6.io.read` | FAIL | FAIL | stub-red |
| `C6.io.write` | FAIL | FAIL | stub-red |
| `C9.help` | FAIL | PASS | stub-red |
| `C9.usage.0` | PASS | PASS | mutant owed |
| `C9.usage.1` | PASS | PASS | mutant owed |
| `C9.usage.2` | PASS | PASS | mutant owed |
| `C9.usage.3` | PASS | PASS | mutant owed |
| `C9.usage.4` | PASS | PASS | mutant owed |
| `C9.usage.5` | PASS | PASS | mutant owed |
| `C9.presentation.lake-progress` | FAIL | PASS | stub-red |
| `C12.schema.launch` | FAIL | PASS | mutant owed |
| `C12.bound.obligation-name` | PASS | FAIL | stub-red |
| `C12.bound.axiom-name` | PASS | FAIL | stub-red |
| `C12.bound.removed-toolchain-cc` | FAIL | FAIL | stub-red |
| `C12.bound.removed-toolchain-long` | FAIL | FAIL | stub-red |
| `C12.schema.empty` | FAIL | FAIL | stub-red |
| `C12.schema.numeric-order` | FAIL | FAIL | stub-red |
| `C12.registry.accepted-forms` | FAIL | FAIL | stub-red |
| `C11.roundtrip.full` | FAIL | FAIL | stub-red |
| `C11.roundtrip.empty` | FAIL | FAIL | stub-red |
| `C11.roundtrip.noncanonical` | FAIL | FAIL | stub-red |
| `C11.root-kind.0` | FAIL | FAIL | stub-red |
| `C11.root-kind.1` | FAIL | FAIL | stub-red |
| `C11.root-kind.2` | FAIL | FAIL | stub-red |
| `C11.root-kind.3` | FAIL | FAIL | stub-red |
| `C11.root-kind.4` | FAIL | FAIL | stub-red |
| `C11.schema.missing` | FAIL | FAIL | stub-red |
| `C11.schema.zero` | FAIL | FAIL | stub-red |
| `C11.schema.two` | FAIL | FAIL | stub-red |
| `C11.schema.string` | FAIL | FAIL | stub-red |
| `C11.schema.bool` | FAIL | FAIL | stub-red |
| `C11.schema.null` | FAIL | FAIL | stub-red |
| `C11.missing.root.schema` | FAIL | FAIL | stub-red |
| `C11.missing.root.toolchain` | FAIL | FAIL | stub-red |
| `C11.missing.root.operations` | FAIL | FAIL | stub-red |
| `C11.missing.root.notices` | FAIL | FAIL | stub-red |
| `C11.missing.root.removed` | FAIL | FAIL | stub-red |
| `C11.unknown.root` | FAIL | FAIL | stub-red |
| `C11.kind.root.schema.0` | FAIL | FAIL | stub-red |
| `C11.kind.root.schema.1` | FAIL | FAIL | stub-red |
| `C11.kind.root.schema.2` | FAIL | FAIL | stub-red |
| `C11.kind.root.schema.3` | FAIL | FAIL | stub-red |
| `C11.kind.root.schema.4` | FAIL | FAIL | stub-red |
| `C11.kind.root.toolchain.0` | FAIL | FAIL | stub-red |
| `C11.kind.root.toolchain.1` | FAIL | FAIL | stub-red |
| `C11.kind.root.toolchain.2` | FAIL | FAIL | stub-red |
| `C11.kind.root.toolchain.3` | FAIL | FAIL | stub-red |
| `C11.kind.root.toolchain.4` | FAIL | FAIL | stub-red |
| `C11.kind.root.operations.0` | FAIL | FAIL | stub-red |
| `C11.kind.root.operations.1` | FAIL | FAIL | stub-red |
| `C11.kind.root.operations.2` | FAIL | FAIL | stub-red |
| `C11.kind.root.operations.3` | FAIL | FAIL | stub-red |
| `C11.kind.root.operations.4` | FAIL | FAIL | stub-red |
| `C11.kind.root.notices.0` | FAIL | FAIL | stub-red |
| `C11.kind.root.notices.1` | FAIL | FAIL | stub-red |
| `C11.kind.root.notices.2` | FAIL | FAIL | stub-red |
| `C11.kind.root.notices.3` | FAIL | FAIL | stub-red |
| `C11.kind.root.notices.4` | FAIL | FAIL | stub-red |
| `C11.kind.root.removed.0` | FAIL | FAIL | stub-red |
| `C11.kind.root.removed.1` | FAIL | FAIL | stub-red |
| `C11.kind.root.removed.2` | FAIL | FAIL | stub-red |
| `C11.kind.root.removed.3` | FAIL | FAIL | stub-red |
| `C11.kind.root.removed.4` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0.id` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0.version` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0.digest` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0.compat` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0.obligations` | FAIL | FAIL | stub-red |
| `C11.unknown.operations-0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.id.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.id.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.id.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.id.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.id.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.version.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.version.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.version.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.version.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.version.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.digest.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.digest.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.digest.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.digest.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.digest.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.compat.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.compat.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.compat.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.compat.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.obligations.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.obligations.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.obligations.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.obligations.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0.obligations.4` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0-obligations-0.name` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0-obligations-0.status` | FAIL | FAIL | stub-red |
| `C11.missing.operations-0-obligations-0.axioms` | FAIL | FAIL | stub-red |
| `C11.unknown.operations-0-obligations-0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.name.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.name.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.name.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.name.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.name.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.status.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.status.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.status.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.status.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.status.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.axioms.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.axioms.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.axioms.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.axioms.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-0-obligations-0.axioms.4` | FAIL | FAIL | stub-red |
| `C11.missing.operations-1-compat.axioms` | FAIL | FAIL | stub-red |
| `C11.missing.operations-1-compat.status` | FAIL | FAIL | stub-red |
| `C11.missing.operations-1-compat.version` | FAIL | FAIL | stub-red |
| `C11.unknown.operations-1-compat` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.axioms.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.axioms.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.axioms.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.axioms.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.axioms.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.status.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.status.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.status.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.status.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.status.4` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.version.0` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.version.1` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.version.2` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.version.3` | FAIL | FAIL | stub-red |
| `C11.kind.operations-1-compat.version.4` | FAIL | FAIL | stub-red |
| `C11.missing.notices-0.id` | FAIL | FAIL | stub-red |
| `C11.missing.notices-0.version` | FAIL | FAIL | stub-red |
| `C11.missing.notices-0.reason` | FAIL | FAIL | stub-red |
| `C11.missing.notices-0.replacement` | FAIL | FAIL | stub-red |
| `C11.unknown.notices-0` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.id.0` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.id.1` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.id.2` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.id.3` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.id.4` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.version.0` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.version.1` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.version.2` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.version.3` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.version.4` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.reason.0` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.reason.1` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.reason.2` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.reason.3` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.reason.4` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.replacement.0` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.replacement.1` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.replacement.2` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.replacement.3` | FAIL | FAIL | stub-red |
| `C11.kind.notices-0.replacement.4` | FAIL | FAIL | stub-red |
| `C11.missing.removed-0.id` | FAIL | FAIL | stub-red |
| `C11.missing.removed-0.version` | FAIL | FAIL | stub-red |
| `C11.missing.removed-0.kind` | FAIL | FAIL | stub-red |
| `C11.missing.removed-0.digest` | FAIL | FAIL | stub-red |
| `C11.missing.removed-0.toolchain` | FAIL | FAIL | stub-red |
| `C11.missing.removed-0.last_commit` | FAIL | FAIL | stub-red |
| `C11.unknown.removed-0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.id.0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.id.1` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.id.2` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.id.3` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.id.4` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.version.0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.version.1` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.version.2` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.version.3` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.version.4` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.kind.0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.kind.1` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.kind.2` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.kind.3` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.kind.4` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.digest.0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.digest.1` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.digest.2` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.digest.3` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.digest.4` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.toolchain.0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.toolchain.1` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.toolchain.2` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.toolchain.3` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.toolchain.4` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.last_commit.0` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.last_commit.1` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.last_commit.2` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.last_commit.3` | FAIL | FAIL | stub-red |
| `C11.kind.removed-0.last_commit.4` | FAIL | FAIL | stub-red |
| `C11.bad.id.0` | FAIL | FAIL | stub-red |
| `C11.bad.id.1` | FAIL | FAIL | stub-red |
| `C11.bad.id.2` | FAIL | FAIL | stub-red |
| `C11.bad.id.3` | FAIL | FAIL | stub-red |
| `C11.bad.id.4` | FAIL | FAIL | stub-red |
| `C11.bad.id.5` | FAIL | FAIL | stub-red |
| `C11.bad.version.0` | FAIL | FAIL | stub-red |
| `C11.bad.version.1` | FAIL | FAIL | stub-red |
| `C11.bad.version.2` | FAIL | FAIL | stub-red |
| `C11.bad.version.3` | FAIL | FAIL | stub-red |
| `C11.bad.version.4` | FAIL | FAIL | stub-red |
| `C11.bad.version.5` | FAIL | FAIL | stub-red |
| `C11.bad.version.6` | FAIL | FAIL | stub-red |
| `C11.bad.digest.0` | FAIL | FAIL | stub-red |
| `C11.bad.digest.1` | FAIL | FAIL | stub-red |
| `C11.bad.digest.2` | FAIL | FAIL | stub-red |
| `C11.bad.digest.3` | FAIL | FAIL | stub-red |
| `C11.bad.digest.4` | FAIL | FAIL | stub-red |
| `C11.version.cap` | FAIL | FAIL | stub-red |
| `C11.id.cap-valid` | FAIL | FAIL | stub-red |
| `C11.text.id-over-cap` | FAIL | FAIL | stub-red |
| `C11.text.version-over-cap` | FAIL | FAIL | stub-red |
| `C11.key.cap` | FAIL | FAIL | stub-red |
| `C11.text.key-over-cap` | FAIL | FAIL | stub-red |
| `C11.bad.obligation.name.empty` | FAIL | FAIL | stub-red |
| `C11.bad.obligation.name.nul` | FAIL | FAIL | stub-red |
| `C11.bad.obligation.name.del` | FAIL | FAIL | stub-red |
| `C11.bad.obligation.name.over` | FAIL | FAIL | stub-red |
| `C11.bad.obligation.name.utf8-over` | FAIL | FAIL | stub-red |
| `C11.accept.obligation.name.cap` | FAIL | FAIL | stub-red |
| `C11.accept.obligation.name.utf8-cap` | FAIL | FAIL | stub-red |
| `C11.toolchain.empty` | FAIL | FAIL | stub-red |
| `C11.toolchain.control` | FAIL | FAIL | stub-red |
| `C11.toolchain.over` | FAIL | FAIL | stub-red |
| `C11.toolchain.cap` | FAIL | FAIL | stub-red |
| `C11.reason.empty` | FAIL | FAIL | stub-red |
| `C11.reason.control` | FAIL | FAIL | stub-red |
| `C11.reason.del` | FAIL | FAIL | stub-red |
| `C11.reason.cap` | FAIL | FAIL | stub-red |
| `C11.removed.commit.upper` | FAIL | FAIL | stub-red |
| `C11.removed.commit.short` | FAIL | FAIL | stub-red |
| `C11.removed.commit.long` | FAIL | FAIL | stub-red |
| `C11.removed.kind` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.0` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.1` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.2` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.3` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.4` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.5` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.6` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.7` | FAIL | FAIL | stub-red |
| `C11.status.obligation.proven.8` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.0` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.1` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.2` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.3` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.4` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.5` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.6` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.7` | FAIL | FAIL | stub-red |
| `C11.status.obligation.open.8` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.0` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.1` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.2` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.3` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.4` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.5` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.6` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.7` | FAIL | FAIL | stub-red |
| `C11.status.obligation.trusts.8` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.0` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.1` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.2` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.3` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.4` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.5` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.6` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.7` | FAIL | FAIL | stub-red |
| `C11.status.obligation.unknown.8` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.0` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.1` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.2` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.3` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.4` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.5` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.6` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.7` | FAIL | FAIL | stub-red |
| `C11.status.compat.proven.8` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.0` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.1` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.2` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.3` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.4` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.5` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.6` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.7` | FAIL | FAIL | stub-red |
| `C11.status.compat.open.8` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.0` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.1` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.2` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.3` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.4` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.5` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.6` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.7` | FAIL | FAIL | stub-red |
| `C11.status.compat.trusts.8` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.0` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.1` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.2` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.3` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.4` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.5` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.6` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.7` | FAIL | FAIL | stub-red |
| `C11.status.compat.unknown.8` | FAIL | FAIL | stub-red |
| `C11.operations.reversed` | FAIL | FAIL | stub-red |
| `C11.operations.duplicate` | FAIL | FAIL | stub-red |
| `C11.obligations.duplicate` | FAIL | FAIL | stub-red |
| `C11.relation.notice-membership` | FAIL | FAIL | stub-red |
| `C11.relation.replacement` | FAIL | FAIL | stub-red |
| `C11.relation.removed-listed` | FAIL | FAIL | stub-red |
| `C11.relation.removed-duplicate` | FAIL | FAIL | stub-red |
| `C11.relation.removed-no-notice` | FAIL | FAIL | stub-red |
| `C11.order.discriminator` | FAIL | FAIL | stub-red |
| `C11.order.unknown-before-missing` | FAIL | FAIL | stub-red |
| `C11.order.missing-before-value` | FAIL | FAIL | stub-red |
| `C11.order.member-bytes` | FAIL | FAIL | stub-red |
| `C11.order.element-before-order` | FAIL | FAIL | stub-red |
| `C11.order.walk-before-relation` | FAIL | FAIL | stub-red |
| `C11.text.empty` | FAIL | FAIL | stub-red |
| `C11.text.syntax` | FAIL | FAIL | stub-red |
| `C11.text.fraction` | FAIL | FAIL | stub-red |
| `C11.text.exponent` | FAIL | FAIL | stub-red |
| `C11.text.negative-zero` | FAIL | FAIL | stub-red |
| `C11.text.big-int` | FAIL | FAIL | stub-red |
| `C11.text.bom` | FAIL | FAIL | stub-red |
| `C11.text.trailing` | FAIL | FAIL | stub-red |
| `C11.text.surrogate` | FAIL | FAIL | stub-red |
| `C11.text.utf8` | FAIL | FAIL | stub-red |
| `C11.text.depth` | FAIL | FAIL | stub-red |
| `C11.text.depth-priority` | FAIL | FAIL | stub-red |
| `C11.text.string-cap` | FAIL | FAIL | stub-red |
| `C11.text.duplicate` | FAIL | FAIL | stub-red |
| `C11.text.duplicate-escaped` | FAIL | FAIL | stub-red |
| `C11.text.duplicate-nested` | FAIL | FAIL | stub-red |
| `C11.presentation.key.00` | FAIL | FAIL | stub-red |
| `C11.presentation.value.00` | FAIL | FAIL | stub-red |
| `C11.presentation.key.01` | FAIL | FAIL | stub-red |
| `C11.presentation.value.01` | FAIL | FAIL | stub-red |
| `C11.presentation.key.02` | FAIL | FAIL | stub-red |
| `C11.presentation.value.02` | FAIL | FAIL | stub-red |
| `C11.presentation.key.03` | FAIL | FAIL | stub-red |
| `C11.presentation.value.03` | FAIL | FAIL | stub-red |
| `C11.presentation.key.04` | FAIL | FAIL | stub-red |
| `C11.presentation.value.04` | FAIL | FAIL | stub-red |
| `C11.presentation.key.05` | FAIL | FAIL | stub-red |
| `C11.presentation.value.05` | FAIL | FAIL | stub-red |
| `C11.presentation.key.06` | FAIL | FAIL | stub-red |
| `C11.presentation.value.06` | FAIL | FAIL | stub-red |
| `C11.presentation.key.07` | FAIL | FAIL | stub-red |
| `C11.presentation.value.07` | FAIL | FAIL | stub-red |
| `C11.presentation.key.08` | FAIL | FAIL | stub-red |
| `C11.presentation.value.08` | FAIL | FAIL | stub-red |
| `C11.presentation.key.09` | FAIL | FAIL | stub-red |
| `C11.presentation.value.09` | FAIL | FAIL | stub-red |
| `C11.presentation.key.0a` | FAIL | FAIL | stub-red |
| `C11.presentation.value.0a` | FAIL | FAIL | stub-red |
| `C11.presentation.key.0b` | FAIL | FAIL | stub-red |
| `C11.presentation.value.0b` | FAIL | FAIL | stub-red |
| `C11.presentation.key.0c` | FAIL | FAIL | stub-red |
| `C11.presentation.value.0c` | FAIL | FAIL | stub-red |
| `C11.presentation.key.0d` | FAIL | FAIL | stub-red |
| `C11.presentation.value.0d` | FAIL | FAIL | stub-red |
| `C11.presentation.key.0e` | FAIL | FAIL | stub-red |
| `C11.presentation.value.0e` | FAIL | FAIL | stub-red |
| `C11.presentation.key.0f` | FAIL | FAIL | stub-red |
| `C11.presentation.value.0f` | FAIL | FAIL | stub-red |
| `C11.presentation.key.10` | FAIL | FAIL | stub-red |
| `C11.presentation.value.10` | FAIL | FAIL | stub-red |
| `C11.presentation.key.11` | FAIL | FAIL | stub-red |
| `C11.presentation.value.11` | FAIL | FAIL | stub-red |
| `C11.presentation.key.12` | FAIL | FAIL | stub-red |
| `C11.presentation.value.12` | FAIL | FAIL | stub-red |
| `C11.presentation.key.13` | FAIL | FAIL | stub-red |
| `C11.presentation.value.13` | FAIL | FAIL | stub-red |
| `C11.presentation.key.14` | FAIL | FAIL | stub-red |
| `C11.presentation.value.14` | FAIL | FAIL | stub-red |
| `C11.presentation.key.15` | FAIL | FAIL | stub-red |
| `C11.presentation.value.15` | FAIL | FAIL | stub-red |
| `C11.presentation.key.16` | FAIL | FAIL | stub-red |
| `C11.presentation.value.16` | FAIL | FAIL | stub-red |
| `C11.presentation.key.17` | FAIL | FAIL | stub-red |
| `C11.presentation.value.17` | FAIL | FAIL | stub-red |
| `C11.presentation.key.18` | FAIL | FAIL | stub-red |
| `C11.presentation.value.18` | FAIL | FAIL | stub-red |
| `C11.presentation.key.19` | FAIL | FAIL | stub-red |
| `C11.presentation.value.19` | FAIL | FAIL | stub-red |
| `C11.presentation.key.1a` | FAIL | FAIL | stub-red |
| `C11.presentation.value.1a` | FAIL | FAIL | stub-red |
| `C11.presentation.key.1b` | FAIL | FAIL | stub-red |
| `C11.presentation.value.1b` | FAIL | FAIL | stub-red |
| `C11.presentation.key.1c` | FAIL | FAIL | stub-red |
| `C11.presentation.value.1c` | FAIL | FAIL | stub-red |
| `C11.presentation.key.1d` | FAIL | FAIL | stub-red |
| `C11.presentation.value.1d` | FAIL | FAIL | stub-red |
| `C11.presentation.key.1e` | FAIL | FAIL | stub-red |
| `C11.presentation.value.1e` | FAIL | FAIL | stub-red |
| `C11.presentation.key.1f` | FAIL | FAIL | stub-red |
| `C11.presentation.value.1f` | FAIL | FAIL | stub-red |
| `C11.presentation.key.7f` | FAIL | FAIL | stub-red |
| `C11.presentation.value.7f` | FAIL | FAIL | stub-red |
| `C11.presentation.key.80` | FAIL | FAIL | stub-red |
| `C11.presentation.value.80` | FAIL | FAIL | stub-red |
| `C11.presentation.key.81` | FAIL | FAIL | stub-red |
| `C11.presentation.value.81` | FAIL | FAIL | stub-red |
| `C11.presentation.key.82` | FAIL | FAIL | stub-red |
| `C11.presentation.value.82` | FAIL | FAIL | stub-red |
| `C11.presentation.key.83` | FAIL | FAIL | stub-red |
| `C11.presentation.value.83` | FAIL | FAIL | stub-red |
| `C11.presentation.key.84` | FAIL | FAIL | stub-red |
| `C11.presentation.value.84` | FAIL | FAIL | stub-red |
| `C11.presentation.key.85` | FAIL | FAIL | stub-red |
| `C11.presentation.value.85` | FAIL | FAIL | stub-red |
| `C11.presentation.key.86` | FAIL | FAIL | stub-red |
| `C11.presentation.value.86` | FAIL | FAIL | stub-red |
| `C11.presentation.key.87` | FAIL | FAIL | stub-red |
| `C11.presentation.value.87` | FAIL | FAIL | stub-red |
| `C11.presentation.key.88` | FAIL | FAIL | stub-red |
| `C11.presentation.value.88` | FAIL | FAIL | stub-red |
| `C11.presentation.key.89` | FAIL | FAIL | stub-red |
| `C11.presentation.value.89` | FAIL | FAIL | stub-red |
| `C11.presentation.key.8a` | FAIL | FAIL | stub-red |
| `C11.presentation.value.8a` | FAIL | FAIL | stub-red |
| `C11.presentation.key.8b` | FAIL | FAIL | stub-red |
| `C11.presentation.value.8b` | FAIL | FAIL | stub-red |
| `C11.presentation.key.8c` | FAIL | FAIL | stub-red |
| `C11.presentation.value.8c` | FAIL | FAIL | stub-red |
| `C11.presentation.key.8d` | FAIL | FAIL | stub-red |
| `C11.presentation.value.8d` | FAIL | FAIL | stub-red |
| `C11.presentation.key.8e` | FAIL | FAIL | stub-red |
| `C11.presentation.value.8e` | FAIL | FAIL | stub-red |
| `C11.presentation.key.8f` | FAIL | FAIL | stub-red |
| `C11.presentation.value.8f` | FAIL | FAIL | stub-red |
| `C11.presentation.key.90` | FAIL | FAIL | stub-red |
| `C11.presentation.value.90` | FAIL | FAIL | stub-red |
| `C11.presentation.key.91` | FAIL | FAIL | stub-red |
| `C11.presentation.value.91` | FAIL | FAIL | stub-red |
| `C11.presentation.key.92` | FAIL | FAIL | stub-red |
| `C11.presentation.value.92` | FAIL | FAIL | stub-red |
| `C11.presentation.key.93` | FAIL | FAIL | stub-red |
| `C11.presentation.value.93` | FAIL | FAIL | stub-red |
| `C11.presentation.key.94` | FAIL | FAIL | stub-red |
| `C11.presentation.value.94` | FAIL | FAIL | stub-red |
| `C11.presentation.key.95` | FAIL | FAIL | stub-red |
| `C11.presentation.value.95` | FAIL | FAIL | stub-red |
| `C11.presentation.key.96` | FAIL | FAIL | stub-red |
| `C11.presentation.value.96` | FAIL | FAIL | stub-red |
| `C11.presentation.key.97` | FAIL | FAIL | stub-red |
| `C11.presentation.value.97` | FAIL | FAIL | stub-red |
| `C11.presentation.key.98` | FAIL | FAIL | stub-red |
| `C11.presentation.value.98` | FAIL | FAIL | stub-red |
| `C11.presentation.key.99` | FAIL | FAIL | stub-red |
| `C11.presentation.value.99` | FAIL | FAIL | stub-red |
| `C11.presentation.key.9a` | FAIL | FAIL | stub-red |
| `C11.presentation.value.9a` | FAIL | FAIL | stub-red |
| `C11.presentation.key.9b` | FAIL | FAIL | stub-red |
| `C11.presentation.value.9b` | FAIL | FAIL | stub-red |
| `C11.presentation.key.9c` | FAIL | FAIL | stub-red |
| `C11.presentation.value.9c` | FAIL | FAIL | stub-red |
| `C11.presentation.key.9d` | FAIL | FAIL | stub-red |
| `C11.presentation.value.9d` | FAIL | FAIL | stub-red |
| `C11.presentation.key.9e` | FAIL | FAIL | stub-red |
| `C11.presentation.value.9e` | FAIL | FAIL | stub-red |
| `C11.presentation.key.9f` | FAIL | FAIL | stub-red |
| `C11.presentation.value.9f` | FAIL | FAIL | stub-red |
| `C11.presentation.value-choice.63` | FAIL | FAIL | stub-red |
| `C11.presentation.value-choice.64` | FAIL | FAIL | stub-red |
| `C11.presentation.value-choice.65` | FAIL | FAIL | stub-red |
| `C11.presentation.literal-backslash-n` | FAIL | FAIL | stub-red |
| `C11.presentation.non-cc-separators` | FAIL | FAIL | stub-red |
| `C11.presentation.duplicate.lf` | FAIL | FAIL | stub-red |
| `C11.presentation.duplicate.del` | FAIL | FAIL | stub-red |
| `C11.presentation.duplicate.nel` | FAIL | FAIL | stub-red |
| `C11.c1-control.name` | FAIL | FAIL | stub-red |
| `C11.c1-control.reason` | FAIL | FAIL | stub-red |
| `C11.c1-control.toolchain` | FAIL | FAIL | stub-red |
| `C11.c1-control.axiom` | FAIL | FAIL | stub-red |
| `C11.property.roundtrip` | FAIL | PASS | stub-red |
| `C11.property.normalize` | FAIL | FAIL | stub-red |
| `C11.usage-unreadable` | PASS | FAIL | stub-red |
| `C10.root-absent` | FAIL | PASS | stub-red |
| `C10.root-index` | FAIL | PASS | stub-red |
| `C10.parent-absent` | FAIL | PASS | stub-red |
| `C10.working-malformed` | FAIL | FAIL | stub-red |
| `C10.working-absent` | FAIL | FAIL | stub-red |
| `C10.changed` | FAIL | FAIL | stub-red |
| `C10.vanished` | FAIL | FAIL | stub-red |
| `C10.removed-good` | FAIL | PASS | stub-red |
| `C10.removed-same-toolchain` | FAIL | FAIL | stub-red |
| `C10.removed-wrong-last` | FAIL | FAIL | stub-red |
| `C10.removed-digest-first` | FAIL | FAIL | stub-red |
| `C10.committed-removal` | FAIL | PASS | stub-red |
| `C10.preserved-removal` | FAIL | PASS | stub-red |
| `C10.head-then-parent` | FAIL | FAIL | stub-red |
| `C10.notice-edited` | FAIL | FAIL | stub-red |
| `C10.notice-appended` | FAIL | PASS | stub-red |
| `C10.removed-edited` | FAIL | FAIL | stub-red |
| `C10.removed-vanished` | FAIL | FAIL | stub-red |
| `C10.baseline-undecodable` | FAIL | FAIL | stub-red |
| `C10.shallow-precedence` | FAIL | FAIL | stub-red |
| `C10.parent-unreadable` | FAIL | FAIL | stub-red |
| `C10.not-worktree` | FAIL | FAIL | stub-red |
| `C10.presentation.control-path` | FAIL | FAIL | stub-red |
| `C10.parents-notices-diverge` | FAIL | FAIL | stub-red |
| `C10.parents-removed-diverge` | FAIL | FAIL | stub-red |
| `C10.removal-witness-preserved-across-parent` | FAIL | PASS | stub-red |
| `C10.explicit-dir` | FAIL | PASS | stub-red |
