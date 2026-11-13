import Lake

open Lake DSL

/-- The `fvdep` tool: proven pure core (`FvdepCore`) + thin IO interpreter (`FvdepIO`), requiring
the library by path. Shipped modules import Init, Std, Lean, Lake + fvdep's own libraries alone
(gate stage `imports`); tests may import more. -/
package fvdeptool where
  version := v!"0.1.0"
  description := "The fvdep command-line tool: checks Lean implementations against fvdep specs."
  license := "Apache-2.0"
  testDriver := "«fvdep-tests»"
  -- Lints ride the build (warnings are errors): a separate `lake lint --linters` build would
  -- rebuild every module twice per gate run (measured: 4 → 4 → 4 rebuilt modules).
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩,
    ⟨`linter.extra.dupNamespace, true⟩, ⟨`linter.extra.unnecessarySeqFocus, true⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.extra.unusedDecidableInType, true⟩,
    ⟨`linter.redundantVisibility, true⟩]

require fvdep from ".."

lean_lib FvdepCore

lean_lib FvdepIO

/-- Target name ≠ `fvdep`: the `require` above already declares that name. -/
@[default_target] lean_exe «fvdep-cli» where
  root := `Main
  exeName := "fvdep"

lean_exe «fvdep-tests» where root := `Tests
