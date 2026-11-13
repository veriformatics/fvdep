import Lake

open Lake DSL

/-- The library consumers require by git: contracts, published profiles + models, the C ABI shapes,
the registry + notices (`Fvdep`), and previews (`FvdepPreview`, never imported by `Fvdep`: gate
stage `preview`). Library modules import Init, Std + the library alone (gate stage `imports`), so a
consumer's build of a pinned snapshot stays toolchain-only. The tool lives in `tool/`. -/
package fvdep where
  version := v!"0.1.0"
  description :=
  "Formal specifications of popular dependencies with machine-checked proofs, package " ++
    "profiles and C-ABI shapes."
  keywords := #["formal-verification", "lean", "dependencies", "specifications"]
  license := "Apache-2.0 WITH LLVM-exception"
  licenseFiles := #["LICENSE"]
  -- Lints ride the build (warnings are errors): a separate `lake lint --linters` build would
  -- rebuild every module twice per gate run (measured: 4 → 4 → 4 rebuilt modules).
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.dupNamespace, true⟩, ⟨`linter.extra.unnecessarySeqFocus, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.extra.unusedDecidableInType, true⟩,
    ⟨`linter.redundantVisibility, true⟩]

@[default_target] lean_lib Fvdep

lean_lib FvdepPreview
