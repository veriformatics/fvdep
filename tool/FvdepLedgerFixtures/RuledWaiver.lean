import FvdepLedger.Types

/-! Contract-only fixture: RuledWaiver. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.RuledWaiver

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.RuledWaiver.main
    interpreter := `FvdepLedgerFixtures.RuledWaiver.interpret
    plan := `FvdepLedgerFixtures.RuledWaiver.plan
    libs := [`FvdepLedgerFixtures.RuledWaiver]
    rows :=
      [{  component := `FvdepLedgerFixtures.RuledWaiver
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.RuledWaiver.plan
          path := [`FvdepLedgerFixtures.RuledWaiver.main, `FvdepLedgerFixtures.RuledWaiver.plan]
          noCaller := ""
          residue := []
          unproven := ["runtime"] },
        { component := `FvdepLedgerFixtures.RuledWaiver
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.RuledWaiver.interpret
          path :=
            [`FvdepLedgerFixtures.RuledWaiver.main, `FvdepLedgerFixtures.RuledWaiver.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.RuledWaiver
