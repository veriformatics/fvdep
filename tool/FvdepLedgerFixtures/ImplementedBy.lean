import FvdepLedger.Types

/-! Contract-only fixture: ImplementedBy. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.ImplementedBy

def replacement (args : List String) : Nat := args.length + 1

@[implemented_by replacement]
def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.ImplementedBy.main
    interpreter := `FvdepLedgerFixtures.ImplementedBy.interpret
    plan := `FvdepLedgerFixtures.ImplementedBy.plan
    libs := [`FvdepLedgerFixtures.ImplementedBy]
    rows :=
      [{  component := `FvdepLedgerFixtures.ImplementedBy
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.ImplementedBy.statement,
                `FvdepLedgerFixtures.ImplementedBy.proof)]
          subject := `FvdepLedgerFixtures.ImplementedBy.plan
          path := [`FvdepLedgerFixtures.ImplementedBy.main, `FvdepLedgerFixtures.ImplementedBy.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.ImplementedBy
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.ImplementedBy.interpret
          path :=
            [`FvdepLedgerFixtures.ImplementedBy.main, `FvdepLedgerFixtures.ImplementedBy.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.ImplementedBy
