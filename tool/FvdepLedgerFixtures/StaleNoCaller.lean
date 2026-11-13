import FvdepLedger.Types

/-! Contract-only fixture: StaleNoCaller. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.StaleNoCaller

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.StaleNoCaller.main
    interpreter := `FvdepLedgerFixtures.StaleNoCaller.interpret
    plan := `FvdepLedgerFixtures.StaleNoCaller.plan
    libs := [`FvdepLedgerFixtures.StaleNoCaller]
    rows :=
      [{  component := `FvdepLedgerFixtures.StaleNoCaller
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.StaleNoCaller.statement,
                `FvdepLedgerFixtures.StaleNoCaller.proof)]
          subject := `FvdepLedgerFixtures.StaleNoCaller.plan
          path := []
          noCaller := "U8"
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.StaleNoCaller
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.StaleNoCaller.interpret
          path :=
            [`FvdepLedgerFixtures.StaleNoCaller.main, `FvdepLedgerFixtures.StaleNoCaller.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.StaleNoCaller
