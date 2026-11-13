import FvdepLedger.Types

/-! Contract-only fixture: Opaque. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Opaque

opaque plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = plan args

theorem proof : ∀ args : List String, plan args = plan args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Opaque.main
    interpreter := `FvdepLedgerFixtures.Opaque.interpret
    plan := `FvdepLedgerFixtures.Opaque.plan
    libs := [`FvdepLedgerFixtures.Opaque]
    rows :=
      [{  component := `FvdepLedgerFixtures.Opaque
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Opaque.statement, `FvdepLedgerFixtures.Opaque.proof)]
          subject := `FvdepLedgerFixtures.Opaque.plan
          path := [`FvdepLedgerFixtures.Opaque.main, `FvdepLedgerFixtures.Opaque.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Opaque
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Opaque.interpret
          path := [`FvdepLedgerFixtures.Opaque.main, `FvdepLedgerFixtures.Opaque.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Opaque
