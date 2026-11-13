import FvdepLedger.Types

/-! Contract-only fixture: StdChoice. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.StdChoice

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  exact Classical.choice ⟨Eq.refl (plan args)⟩

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.StdChoice.main
    interpreter := `FvdepLedgerFixtures.StdChoice.interpret
    plan := `FvdepLedgerFixtures.StdChoice.plan
    libs := [`FvdepLedgerFixtures.StdChoice]
    rows :=
      [{  component := `FvdepLedgerFixtures.StdChoice
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.StdChoice.statement, `FvdepLedgerFixtures.StdChoice.proof)]
          subject := `FvdepLedgerFixtures.StdChoice.plan
          path := [`FvdepLedgerFixtures.StdChoice.main, `FvdepLedgerFixtures.StdChoice.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.StdChoice
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.StdChoice.interpret
          path := [`FvdepLedgerFixtures.StdChoice.main, `FvdepLedgerFixtures.StdChoice.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.StdChoice
