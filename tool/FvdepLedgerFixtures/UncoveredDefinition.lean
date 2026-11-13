import FvdepLedger.Types

/-! Contract-only fixture: UncoveredDefinition. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UncoveredDefinition

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.UncoveredDefinition.main
    interpreter := `FvdepLedgerFixtures.UncoveredDefinition.interpret
    plan := `FvdepLedgerFixtures.UncoveredDefinition.plan
    libs := [`FvdepLedgerFixtures.UncoveredDefinition]
    rows :=
      [{  component := `FvdepLedgerFixtures.UncoveredDefinition
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UncoveredDefinition.statement,
                `FvdepLedgerFixtures.UncoveredDefinition.proof)]
          subject := `FvdepLedgerFixtures.UncoveredDefinition.plan
          path :=
            [`FvdepLedgerFixtures.UncoveredDefinition.main,
              `FvdepLedgerFixtures.UncoveredDefinition.plan]
          noCaller := ""
          residue := []
          unproven := [] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.UncoveredDefinition
