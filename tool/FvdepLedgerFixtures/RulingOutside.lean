import FvdepLedger.Types

/-! Contract-only fixture: RulingOutside. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.RulingOutside

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.RulingOutside.main
    interpreter := `FvdepLedgerFixtures.RulingOutside.interpret
    plan := `FvdepLedgerFixtures.RulingOutside.plan
    libs := [`FvdepLedgerFixtures.RulingOutside]
    rows :=
      [{  component := `FvdepLedgerFixtures.RulingOutside
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.RulingOutside.statement,
                `FvdepLedgerFixtures.RulingOutside.proof)]
          subject := `FvdepLedgerFixtures.RulingOutside.plan
          path := [`FvdepLedgerFixtures.RulingOutside.main, `FvdepLedgerFixtures.RulingOutside.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.RulingOutside
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.RulingOutside.interpret
          path :=
            [`FvdepLedgerFixtures.RulingOutside.main, `FvdepLedgerFixtures.RulingOutside.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.RulingOutside
