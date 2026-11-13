import FvdepLedger.Types

/-! Contract-only fixture: PathStart. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.PathStart

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.PathStart.main
    interpreter := `FvdepLedgerFixtures.PathStart.interpret
    plan := `FvdepLedgerFixtures.PathStart.plan
    libs := [`FvdepLedgerFixtures.PathStart]
    rows :=
      [{  component := `FvdepLedgerFixtures.PathStart
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.PathStart.statement, `FvdepLedgerFixtures.PathStart.proof)]
          subject := `FvdepLedgerFixtures.PathStart.plan
          path := [`FvdepLedgerFixtures.PathStart.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.PathStart
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.PathStart.interpret
          path := [`FvdepLedgerFixtures.PathStart.main, `FvdepLedgerFixtures.PathStart.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.PathStart
