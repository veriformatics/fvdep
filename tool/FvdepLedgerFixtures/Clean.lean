import FvdepLedger.Types

/-! Contract-only fixture: Clean. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Clean

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Clean.main
    interpreter := `FvdepLedgerFixtures.Clean.interpret
    plan := `FvdepLedgerFixtures.Clean.plan
    libs := [`FvdepLedgerFixtures.Clean]
    rows :=
      [{  component := `FvdepLedgerFixtures.Clean
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Clean.statement, `FvdepLedgerFixtures.Clean.proof)]
          subject := `FvdepLedgerFixtures.Clean.plan
          path := [`FvdepLedgerFixtures.Clean.main, `FvdepLedgerFixtures.Clean.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Clean
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Clean.interpret
          path := [`FvdepLedgerFixtures.Clean.main, `FvdepLedgerFixtures.Clean.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Clean
