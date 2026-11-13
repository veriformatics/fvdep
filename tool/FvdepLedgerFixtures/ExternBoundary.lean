import FvdepLedger.Types

/-! Contract-only fixture: ExternBoundary. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.ExternBoundary

@[extern "fvdep_ledger_fixture_step"]
def step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = step args.length

theorem proof : ∀ args : List String, plan args = step args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.ExternBoundary.main
    interpreter := `FvdepLedgerFixtures.ExternBoundary.interpret
    plan := `FvdepLedgerFixtures.ExternBoundary.plan
    libs := [`FvdepLedgerFixtures.ExternBoundary]
    rows :=
      [{  component := `FvdepLedgerFixtures.ExternBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.ExternBoundary.statement,
                `FvdepLedgerFixtures.ExternBoundary.proof)]
          subject := `FvdepLedgerFixtures.ExternBoundary.plan
          path :=
            [`FvdepLedgerFixtures.ExternBoundary.main, `FvdepLedgerFixtures.ExternBoundary.plan]
          noCaller := ""
          residue := ["runtime"]
          unproven := [] },
        { component := `FvdepLedgerFixtures.ExternBoundary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.ExternBoundary.interpret
          path :=
            [`FvdepLedgerFixtures.ExternBoundary.main,
              `FvdepLedgerFixtures.ExternBoundary.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [`FvdepLedgerFixtures.ExternBoundary.step] }] }

end FvdepLedgerFixtures.ExternBoundary
