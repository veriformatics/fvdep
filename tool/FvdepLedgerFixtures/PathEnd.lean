import FvdepLedger.Types

/-! Contract-only fixture: PathEnd. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.PathEnd

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.PathEnd.main
    interpreter := `FvdepLedgerFixtures.PathEnd.interpret
    plan := `FvdepLedgerFixtures.PathEnd.plan
    libs := [`FvdepLedgerFixtures.PathEnd]
    rows :=
      [{  component := `FvdepLedgerFixtures.PathEnd
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.PathEnd.statement, `FvdepLedgerFixtures.PathEnd.proof)]
          subject := `FvdepLedgerFixtures.PathEnd.plan
          path := [`FvdepLedgerFixtures.PathEnd.main, `FvdepLedgerFixtures.PathEnd.interpret]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.PathEnd
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.PathEnd.interpret
          path := [`FvdepLedgerFixtures.PathEnd.main, `FvdepLedgerFixtures.PathEnd.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.PathEnd
