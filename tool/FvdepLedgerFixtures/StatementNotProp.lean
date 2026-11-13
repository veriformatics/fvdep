import FvdepLedger.Types

/-! Contract-only fixture: StatementNotProp. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.StatementNotProp

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Nat := 7

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.StatementNotProp.main
    interpreter := `FvdepLedgerFixtures.StatementNotProp.interpret
    plan := `FvdepLedgerFixtures.StatementNotProp.plan
    libs := [`FvdepLedgerFixtures.StatementNotProp]
    rows :=
      [{  component := `FvdepLedgerFixtures.StatementNotProp
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.StatementNotProp.statement,
                `FvdepLedgerFixtures.StatementNotProp.proof)]
          subject := `FvdepLedgerFixtures.StatementNotProp.plan
          path :=
            [`FvdepLedgerFixtures.StatementNotProp.main, `FvdepLedgerFixtures.StatementNotProp.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.StatementNotProp
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.StatementNotProp.interpret
          path :=
            [`FvdepLedgerFixtures.StatementNotProp.main,
              `FvdepLedgerFixtures.StatementNotProp.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.StatementNotProp
