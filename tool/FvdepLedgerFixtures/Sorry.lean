import FvdepLedger.Types

/-! Contract-only fixture: Sorry. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Sorry

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by sorry

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Sorry.main
    interpreter := `FvdepLedgerFixtures.Sorry.interpret
    plan := `FvdepLedgerFixtures.Sorry.plan
    libs := [`FvdepLedgerFixtures.Sorry]
    rows :=
      [{  component := `FvdepLedgerFixtures.Sorry
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Sorry.statement, `FvdepLedgerFixtures.Sorry.proof)]
          subject := `FvdepLedgerFixtures.Sorry.plan
          path := [`FvdepLedgerFixtures.Sorry.main, `FvdepLedgerFixtures.Sorry.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Sorry
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Sorry.interpret
          path := [`FvdepLedgerFixtures.Sorry.main, `FvdepLedgerFixtures.Sorry.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Sorry
