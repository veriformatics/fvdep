import FvdepLedger.Types

/-! Contract-only fixture: MissingRuling. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MissingRuling

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MissingRuling.main
    interpreter := `FvdepLedgerFixtures.MissingRuling.interpret
    plan := `FvdepLedgerFixtures.MissingRuling.plan
    libs := [`FvdepLedgerFixtures.MissingRuling]
    rows :=
      [{  component := `FvdepLedgerFixtures.MissingRuling
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MissingRuling.statement,
                `FvdepLedgerFixtures.MissingRuling.proof)]
          subject := `FvdepLedgerFixtures.MissingRuling.plan
          path := [`FvdepLedgerFixtures.MissingRuling.main, `FvdepLedgerFixtures.MissingRuling.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MissingRuling
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MissingRuling.interpret
          path :=
            [`FvdepLedgerFixtures.MissingRuling.main, `FvdepLedgerFixtures.MissingRuling.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "This ruling does not occur in the spec fixture."
          boundary := [] }] }

end FvdepLedgerFixtures.MissingRuling
