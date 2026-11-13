import FvdepLedger.Types
import Lean

/-! Contract-only fixture: Unsafe. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Unsafe

unsafe def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

unsafe def main (args : List String) : Nat := interpret (plan args)

open Lean Elab Term Meta in
set_option debug.skipKernelTC true in
run_elab
  do
    let listTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``String)
    withLocalDeclD `args listTy fun args => do
        let call := mkApp (mkConst `FvdepLedgerFixtures.Unsafe.plan) args
        let prop ← mkForallFVars #[args] (← mkEq call call)
        let value ← mkLambdaFVars #[args] (← mkEqRefl call)
        addDecl
            (.defnDecl
              { name := `FvdepLedgerFixtures.Unsafe.statement
                levelParams := []
                type := mkSort Level.zero
                value := prop
                hints := .abbrev
                safety := .safe })
        addDecl
            (.thmDecl
              { name := `FvdepLedgerFixtures.Unsafe.proof
                levelParams := []
                type := prop
                value := value })

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Unsafe.main
    interpreter := `FvdepLedgerFixtures.Unsafe.interpret
    plan := `FvdepLedgerFixtures.Unsafe.plan
    libs := [`FvdepLedgerFixtures.Unsafe]
    rows :=
      [{  component := `FvdepLedgerFixtures.Unsafe
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Unsafe.statement, `FvdepLedgerFixtures.Unsafe.proof)]
          subject := `FvdepLedgerFixtures.Unsafe.plan
          path := [`FvdepLedgerFixtures.Unsafe.main, `FvdepLedgerFixtures.Unsafe.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Unsafe
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Unsafe.interpret
          path := [`FvdepLedgerFixtures.Unsafe.main, `FvdepLedgerFixtures.Unsafe.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Unsafe
