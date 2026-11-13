import FvdepLedger.Types

/-! Contract-only fixture: BrokenRoot. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.BrokenRoot

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args + 1)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.BrokenRoot.main
    interpreter := `FvdepLedgerFixtures.BrokenRoot.interpret
    plan := `FvdepLedgerFixtures.BrokenRoot.plan
    libs := [`FvdepLedgerFixtures.BrokenRoot]
    rows :=
      [{  component := `FvdepLedgerFixtures.BrokenRoot
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.BrokenRoot.statement, `FvdepLedgerFixtures.BrokenRoot.proof)]
          subject := `FvdepLedgerFixtures.BrokenRoot.plan
          path := [`FvdepLedgerFixtures.BrokenRoot.main, `FvdepLedgerFixtures.BrokenRoot.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.BrokenRoot
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.BrokenRoot.interpret
          path := [`FvdepLedgerFixtures.BrokenRoot.main, `FvdepLedgerFixtures.BrokenRoot.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.BrokenRoot
