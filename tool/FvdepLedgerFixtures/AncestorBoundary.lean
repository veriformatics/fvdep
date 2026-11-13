import FvdepLedger.Types

/-! Contract-only fixture: AncestorBoundary. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.AncestorBoundary

opaque step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = step args.length

theorem proof : ∀ args : List String, plan args = step args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.AncestorBoundary.main
    interpreter := `FvdepLedgerFixtures.AncestorBoundary.interpret
    plan := `FvdepLedgerFixtures.AncestorBoundary.plan
    libs := [`FvdepLedgerFixtures.AncestorBoundary]
    rows :=
      [{  component := `FvdepLedgerFixtures.AncestorBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.AncestorBoundary.statement,
                `FvdepLedgerFixtures.AncestorBoundary.proof)]
          subject := `FvdepLedgerFixtures.AncestorBoundary.plan
          path :=
            [`FvdepLedgerFixtures.AncestorBoundary.main, `FvdepLedgerFixtures.AncestorBoundary.plan]
          noCaller := ""
          residue := ["runtime"]
          unproven := [] },
        { component := `FvdepLedgerFixtures.AncestorBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.AncestorBoundary.interpret
          path :=
            [`FvdepLedgerFixtures.AncestorBoundary.main,
              `FvdepLedgerFixtures.AncestorBoundary.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [`FvdepLedgerFixtures.AncestorBoundary.plan] }] }

end FvdepLedgerFixtures.AncestorBoundary
