import FvdepLedger.Types

/-! Contract-only fixture: StatementNotDefinition. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.StatementNotDefinition

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

theorem statement : True := True.intro

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.StatementNotDefinition.main
    interpreter := `FvdepLedgerFixtures.StatementNotDefinition.interpret
    plan := `FvdepLedgerFixtures.StatementNotDefinition.plan
    libs := [`FvdepLedgerFixtures.StatementNotDefinition]
    rows :=
      [{  component := `FvdepLedgerFixtures.StatementNotDefinition
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.StatementNotDefinition.statement,
                `FvdepLedgerFixtures.StatementNotDefinition.proof)]
          subject := `FvdepLedgerFixtures.StatementNotDefinition.plan
          path :=
            [`FvdepLedgerFixtures.StatementNotDefinition.main,
              `FvdepLedgerFixtures.StatementNotDefinition.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.StatementNotDefinition
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.StatementNotDefinition.interpret
          path :=
            [`FvdepLedgerFixtures.StatementNotDefinition.main,
              `FvdepLedgerFixtures.StatementNotDefinition.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.StatementNotDefinition
