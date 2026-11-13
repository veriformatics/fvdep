import FvdepLedger.Types

/-! Contract-only fixture: NotTheorem. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NotTheorem

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

def proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NotTheorem.main
    interpreter := `FvdepLedgerFixtures.NotTheorem.interpret
    plan := `FvdepLedgerFixtures.NotTheorem.plan
    libs := [`FvdepLedgerFixtures.NotTheorem]
    rows :=
      [{  component := `FvdepLedgerFixtures.NotTheorem
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NotTheorem.statement, `FvdepLedgerFixtures.NotTheorem.proof)]
          subject := `FvdepLedgerFixtures.NotTheorem.plan
          path := [`FvdepLedgerFixtures.NotTheorem.main, `FvdepLedgerFixtures.NotTheorem.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NotTheorem
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NotTheorem.interpret
          path := [`FvdepLedgerFixtures.NotTheorem.main, `FvdepLedgerFixtures.NotTheorem.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NotTheorem
