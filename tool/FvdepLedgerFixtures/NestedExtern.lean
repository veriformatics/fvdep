import FvdepLedger.Types

/-! Contract-only fixture: NestedExtern. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NestedExtern

@[extern "fvdep_ledger_fixture_step"]
def step (n : Nat) : Nat := n

def plan (args : List String) : Nat := step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NestedExtern.main
    interpreter := `FvdepLedgerFixtures.NestedExtern.interpret
    plan := `FvdepLedgerFixtures.NestedExtern.plan
    libs := [`FvdepLedgerFixtures.NestedExtern]
    rows :=
      [{  component := `FvdepLedgerFixtures.NestedExtern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NestedExtern.statement, `FvdepLedgerFixtures.NestedExtern.proof)]
          subject := `FvdepLedgerFixtures.NestedExtern.plan
          path := [`FvdepLedgerFixtures.NestedExtern.main, `FvdepLedgerFixtures.NestedExtern.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NestedExtern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NestedExtern.interpret
          path :=
            [`FvdepLedgerFixtures.NestedExtern.main, `FvdepLedgerFixtures.NestedExtern.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NestedExtern
