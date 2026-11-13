import FvdepLedger.Types

/-! Contract-only fixture: MissingStatement. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MissingStatement

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MissingStatement.main
    interpreter := `FvdepLedgerFixtures.MissingStatement.interpret
    plan := `FvdepLedgerFixtures.MissingStatement.plan
    libs := [`FvdepLedgerFixtures.MissingStatement]
    rows :=
      [{  component := `FvdepLedgerFixtures.MissingStatement
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MissingStatement.absentStatement,
                `FvdepLedgerFixtures.MissingStatement.proof)]
          subject := `FvdepLedgerFixtures.MissingStatement.plan
          path :=
            [`FvdepLedgerFixtures.MissingStatement.main, `FvdepLedgerFixtures.MissingStatement.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MissingStatement
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MissingStatement.interpret
          path :=
            [`FvdepLedgerFixtures.MissingStatement.main,
              `FvdepLedgerFixtures.MissingStatement.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MissingStatement
