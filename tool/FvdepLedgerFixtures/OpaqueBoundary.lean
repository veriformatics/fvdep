import FvdepLedger.Types

/-! Contract-only fixture: OpaqueBoundary. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.OpaqueBoundary

opaque step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = step args.length

theorem proof : ∀ args : List String, plan args = step args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.OpaqueBoundary.main
    interpreter := `FvdepLedgerFixtures.OpaqueBoundary.interpret
    plan := `FvdepLedgerFixtures.OpaqueBoundary.plan
    libs := [`FvdepLedgerFixtures.OpaqueBoundary]
    rows :=
      [{  component := `FvdepLedgerFixtures.OpaqueBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.OpaqueBoundary.statement,
                `FvdepLedgerFixtures.OpaqueBoundary.proof)]
          subject := `FvdepLedgerFixtures.OpaqueBoundary.plan
          path :=
            [`FvdepLedgerFixtures.OpaqueBoundary.main, `FvdepLedgerFixtures.OpaqueBoundary.plan]
          noCaller := ""
          residue := ["runtime"]
          unproven := [] },
        { component := `FvdepLedgerFixtures.OpaqueBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.OpaqueBoundary.interpret
          path :=
            [`FvdepLedgerFixtures.OpaqueBoundary.main,
              `FvdepLedgerFixtures.OpaqueBoundary.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [`FvdepLedgerFixtures.OpaqueBoundary.step] }] }

end FvdepLedgerFixtures.OpaqueBoundary
