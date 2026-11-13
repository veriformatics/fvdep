import FvdepLedger.Types

/-! Contract-only fixture: Extern. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Extern

@[extern "fvdep_ledger_fixture_plan"]
def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Extern.main
    interpreter := `FvdepLedgerFixtures.Extern.interpret
    plan := `FvdepLedgerFixtures.Extern.plan
    libs := [`FvdepLedgerFixtures.Extern]
    rows :=
      [{  component := `FvdepLedgerFixtures.Extern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Extern.statement, `FvdepLedgerFixtures.Extern.proof)]
          subject := `FvdepLedgerFixtures.Extern.plan
          path := [`FvdepLedgerFixtures.Extern.main, `FvdepLedgerFixtures.Extern.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Extern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Extern.interpret
          path := [`FvdepLedgerFixtures.Extern.main, `FvdepLedgerFixtures.Extern.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Extern
