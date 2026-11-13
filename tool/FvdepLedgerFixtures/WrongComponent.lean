import FvdepLedger.Types

/-! Contract-only fixture: WrongComponent. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.WrongComponent

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.WrongComponent.main
    interpreter := `FvdepLedgerFixtures.WrongComponent.interpret
    plan := `FvdepLedgerFixtures.WrongComponent.plan
    libs := [`FvdepLedgerFixtures.WrongComponent]
    rows :=
      [{  component := `FvdepLedger.Types
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.WrongComponent.statement,
                `FvdepLedgerFixtures.WrongComponent.proof)]
          subject := `FvdepLedgerFixtures.WrongComponent.plan
          path :=
            [`FvdepLedgerFixtures.WrongComponent.main, `FvdepLedgerFixtures.WrongComponent.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.WrongComponent
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.WrongComponent.interpret
          path :=
            [`FvdepLedgerFixtures.WrongComponent.main,
              `FvdepLedgerFixtures.WrongComponent.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.WrongComponent
