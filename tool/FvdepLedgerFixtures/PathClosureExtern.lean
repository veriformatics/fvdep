import FvdepLedger.Types

/-! Contract-only fixture: PathClosureExtern. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.PathClosureExtern

def subject (args : List String) : Nat := args.length

@[extern "fvdep_ledger_fixture_bridge"]
def bridge (args : List String) : Nat := subject args

def plan (args : List String) : Nat := bridge args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = subject args

theorem proof : ∀ args : List String, plan args = subject args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.PathClosureExtern.main
    interpreter := `FvdepLedgerFixtures.PathClosureExtern.interpret
    plan := `FvdepLedgerFixtures.PathClosureExtern.plan
    libs := [`FvdepLedgerFixtures.PathClosureExtern]
    rows :=
      [{  component := `FvdepLedgerFixtures.PathClosureExtern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.PathClosureExtern.plan
          path :=
            [`FvdepLedgerFixtures.PathClosureExtern.main,
              `FvdepLedgerFixtures.PathClosureExtern.plan]
          noCaller := ""
          residue := []
          unproven := ["runtime"] },
        { component := `FvdepLedgerFixtures.PathClosureExtern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.PathClosureExtern.statement,
                `FvdepLedgerFixtures.PathClosureExtern.proof)]
          subject := `FvdepLedgerFixtures.PathClosureExtern.subject
          path :=
            [`FvdepLedgerFixtures.PathClosureExtern.main,
              `FvdepLedgerFixtures.PathClosureExtern.plan,
              `FvdepLedgerFixtures.PathClosureExtern.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.PathClosureExtern
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.PathClosureExtern.interpret
          path :=
            [`FvdepLedgerFixtures.PathClosureExtern.main,
              `FvdepLedgerFixtures.PathClosureExtern.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.PathClosureExtern
