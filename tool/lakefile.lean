import Lake

open Lake DSL

/-- The `fvdep` tool: proven pure core (`FvdepCore`) + thin IO interpreter (`FvdepIO`), requiring
the library by path. Shipped modules import Init, Std, Lean, Lake + fvdep's own libraries alone
(gate stage `imports`); tests may import more. -/
package fvdeptool where
  version := v!"0.1.0"
  description := "The fvdep command-line tool: checks Lean implementations against fvdep specs."
  license := "Apache-2.0 WITH LLVM-exception"
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

/-- `Main` (the exe root) belongs here too: lib modules (the ledger's rows) import it, and Lake
tracks an import only into a library's modules. -/
lean_lib FvdepIO where roots := #[`FvdepIO, `Main]

/-- Target name ≠ `fvdep`: the `require` above already declares that name. -/
@[default_target] lean_exe «fvdep-cli» where
  root := `Main
  exeName := "fvdep"

lean_exe «fvdep-tests» where root := `Tests

/-- Coverage ledger + its checker (gate stage `coverage`; contract U2 L1–L8): a gate tool, never
shipped (`Main` imports none of it). -/
lean_lib FvdepLedger

lean_exe «fvdep-ledger» where
  root := `LedgerMain
  supportInterpreter := true

/-- Planted ledger breaches + clean controls (contract U2 L9; `tests/ledger/run.sh`). `sorry` +
forged fixtures build on purpose ⇒ warnings stay warnings in this library alone. -/
lean_lib FvdepLedgerFixtures where
  globs := #[.andSubmodules `FvdepLedgerFixtures]
  leanOptions := #[⟨`warningAsError, false⟩]
