import FvdepLedger.Types
import Lean

/-! Contract-only fixture: NestedUnsafe. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NestedUnsafe

unsafe def hidden (n : Nat) : Nat := n

open Lean Elab Term Meta in
set_option debug.skipKernelTC true in
run_elab
  do
    let listTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``String)
    let fnTy ← mkArrow listTy (mkConst ``Nat)
    withLocalDeclD `args listTy fun args => do
        let len := mkApp2 (mkConst ``List.length [Level.zero]) (mkConst ``String) args
        let hidden := mkApp (mkConst `FvdepLedgerFixtures.NestedUnsafe.hidden) len
        let helperValue ← mkLambdaFVars #[args] hidden
        addAndCompile
            (.defnDecl
              { name := `FvdepLedgerFixtures.NestedUnsafe.helper
                levelParams := []
                type := fnTy
                value := helperValue
                hints := .abbrev
                safety := .safe })
        let helper := mkApp (mkConst `FvdepLedgerFixtures.NestedUnsafe.helper) args
        let planValue ← mkLambdaFVars #[args] helper
        addAndCompile
            (.defnDecl
              { name := `FvdepLedgerFixtures.NestedUnsafe.plan
                levelParams := []
                type := fnTy
                value := planValue
                hints := .abbrev
                safety := .safe })

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = plan args

theorem proof : ∀ args : List String, plan args = plan args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NestedUnsafe.main
    interpreter := `FvdepLedgerFixtures.NestedUnsafe.interpret
    plan := `FvdepLedgerFixtures.NestedUnsafe.plan
    libs := [`FvdepLedgerFixtures.NestedUnsafe]
    rows :=
      [{  component := `FvdepLedgerFixtures.NestedUnsafe
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NestedUnsafe.statement, `FvdepLedgerFixtures.NestedUnsafe.proof)]
          subject := `FvdepLedgerFixtures.NestedUnsafe.plan
          path := [`FvdepLedgerFixtures.NestedUnsafe.main, `FvdepLedgerFixtures.NestedUnsafe.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NestedUnsafe
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NestedUnsafe.interpret
          path :=
            [`FvdepLedgerFixtures.NestedUnsafe.main, `FvdepLedgerFixtures.NestedUnsafe.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NestedUnsafe
