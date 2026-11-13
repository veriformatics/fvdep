import FvdepLedger.Types

/-! Contract-only fixture: NestedOpaque. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NestedOpaque

opaque hidden (n : Nat) : Nat := n

def helper (args : List String) : Nat := hidden args.length

def plan (args : List String) : Nat := helper args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = helper args

theorem proof : ∀ args : List String, plan args = helper args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NestedOpaque.main
    interpreter := `FvdepLedgerFixtures.NestedOpaque.interpret
    plan := `FvdepLedgerFixtures.NestedOpaque.plan
    libs := [`FvdepLedgerFixtures.NestedOpaque]
    rows :=
      [{  component := `FvdepLedgerFixtures.NestedOpaque
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NestedOpaque.statement, `FvdepLedgerFixtures.NestedOpaque.proof)]
          subject := `FvdepLedgerFixtures.NestedOpaque.plan
          path := [`FvdepLedgerFixtures.NestedOpaque.main, `FvdepLedgerFixtures.NestedOpaque.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NestedOpaque
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NestedOpaque.interpret
          path :=
            [`FvdepLedgerFixtures.NestedOpaque.main, `FvdepLedgerFixtures.NestedOpaque.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NestedOpaque
