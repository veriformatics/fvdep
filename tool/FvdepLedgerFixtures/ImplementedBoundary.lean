import FvdepLedger.Types

/-! Contract-only fixture: ImplementedBoundary. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.ImplementedBoundary

def replacement (n : Nat) : Nat := n + 1

@[implemented_by replacement]
def step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = step args.length

theorem proof : ∀ args : List String, plan args = step args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.ImplementedBoundary.main
    interpreter := `FvdepLedgerFixtures.ImplementedBoundary.interpret
    plan := `FvdepLedgerFixtures.ImplementedBoundary.plan
    libs := [`FvdepLedgerFixtures.ImplementedBoundary]
    rows :=
      [{  component := `FvdepLedgerFixtures.ImplementedBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.ImplementedBoundary.statement,
                `FvdepLedgerFixtures.ImplementedBoundary.proof)]
          subject := `FvdepLedgerFixtures.ImplementedBoundary.plan
          path :=
            [`FvdepLedgerFixtures.ImplementedBoundary.main,
              `FvdepLedgerFixtures.ImplementedBoundary.plan]
          noCaller := ""
          residue := ["runtime"]
          unproven := [] },
        { component := `FvdepLedgerFixtures.ImplementedBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.ImplementedBoundary.interpret
          path :=
            [`FvdepLedgerFixtures.ImplementedBoundary.main,
              `FvdepLedgerFixtures.ImplementedBoundary.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [`FvdepLedgerFixtures.ImplementedBoundary.step] }] }

end FvdepLedgerFixtures.ImplementedBoundary
