import FvdepLedger.Types

/-! Contract-only fixture: UncitedBoundary. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UncitedBoundary

opaque step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = step args.length

theorem proof : ∀ args : List String, plan args = step args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.UncitedBoundary.main
    interpreter := `FvdepLedgerFixtures.UncitedBoundary.interpret
    plan := `FvdepLedgerFixtures.UncitedBoundary.plan
    libs := [`FvdepLedgerFixtures.UncitedBoundary]
    rows :=
      [{  component := `FvdepLedgerFixtures.UncitedBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UncitedBoundary.statement,
                `FvdepLedgerFixtures.UncitedBoundary.proof)]
          subject := `FvdepLedgerFixtures.UncitedBoundary.plan
          path :=
            [`FvdepLedgerFixtures.UncitedBoundary.main, `FvdepLedgerFixtures.UncitedBoundary.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.UncitedBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UncitedBoundary.interpret
          path :=
            [`FvdepLedgerFixtures.UncitedBoundary.main,
              `FvdepLedgerFixtures.UncitedBoundary.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [`FvdepLedgerFixtures.UncitedBoundary.step] }] }

end FvdepLedgerFixtures.UncitedBoundary
