import FvdepLedger.Types

/-! Contract-only fixture: MissingTheorem. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MissingTheorem

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MissingTheorem.main
    interpreter := `FvdepLedgerFixtures.MissingTheorem.interpret
    plan := `FvdepLedgerFixtures.MissingTheorem.plan
    libs := [`FvdepLedgerFixtures.MissingTheorem]
    rows :=
      [{  component := `FvdepLedgerFixtures.MissingTheorem
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MissingTheorem.statement,
                `FvdepLedgerFixtures.MissingTheorem.absentTheorem)]
          subject := `FvdepLedgerFixtures.MissingTheorem.plan
          path :=
            [`FvdepLedgerFixtures.MissingTheorem.main, `FvdepLedgerFixtures.MissingTheorem.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MissingTheorem
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MissingTheorem.interpret
          path :=
            [`FvdepLedgerFixtures.MissingTheorem.main,
              `FvdepLedgerFixtures.MissingTheorem.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MissingTheorem
