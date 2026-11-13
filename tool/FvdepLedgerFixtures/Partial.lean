import FvdepLedger.Types

/-! Contract-only fixture: Partial. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Partial

partial def plan (args : List String) : Nat := if args.isEmpty then 0 else plan args.tail

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = plan args

theorem proof : ∀ args : List String, plan args = plan args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Partial.main
    interpreter := `FvdepLedgerFixtures.Partial.interpret
    plan := `FvdepLedgerFixtures.Partial.plan
    libs := [`FvdepLedgerFixtures.Partial]
    rows :=
      [{  component := `FvdepLedgerFixtures.Partial
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Partial.statement, `FvdepLedgerFixtures.Partial.proof)]
          subject := `FvdepLedgerFixtures.Partial.plan
          path := [`FvdepLedgerFixtures.Partial.main, `FvdepLedgerFixtures.Partial.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Partial
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Partial.interpret
          path := [`FvdepLedgerFixtures.Partial.main, `FvdepLedgerFixtures.Partial.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Partial
