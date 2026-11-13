import FvdepLedger.Types

/-! Contract-only fixture: NestedImplementedBy. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NestedImplementedBy

def replacement (n : Nat) : Nat := n + 1

@[implemented_by replacement]
def step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NestedImplementedBy.main
    interpreter := `FvdepLedgerFixtures.NestedImplementedBy.interpret
    plan := `FvdepLedgerFixtures.NestedImplementedBy.plan
    libs := [`FvdepLedgerFixtures.NestedImplementedBy]
    rows :=
      [{  component := `FvdepLedgerFixtures.NestedImplementedBy
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NestedImplementedBy.statement,
                `FvdepLedgerFixtures.NestedImplementedBy.proof)]
          subject := `FvdepLedgerFixtures.NestedImplementedBy.plan
          path :=
            [`FvdepLedgerFixtures.NestedImplementedBy.main,
              `FvdepLedgerFixtures.NestedImplementedBy.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NestedImplementedBy
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NestedImplementedBy.interpret
          path :=
            [`FvdepLedgerFixtures.NestedImplementedBy.main,
              `FvdepLedgerFixtures.NestedImplementedBy.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NestedImplementedBy
