import FvdepLedger.Types

/-! Contract-only fixture: InterpreterExempt. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.InterpreterExempt

def plan (args : List String) : Nat := args.length

@[extern "fvdep_ledger_fixture_interpret"]
def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.InterpreterExempt.main
    interpreter := `FvdepLedgerFixtures.InterpreterExempt.interpret
    plan := `FvdepLedgerFixtures.InterpreterExempt.plan
    libs := [`FvdepLedgerFixtures.InterpreterExempt]
    rows :=
      [{  component := `FvdepLedgerFixtures.InterpreterExempt
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.InterpreterExempt.statement,
                `FvdepLedgerFixtures.InterpreterExempt.proof)]
          subject := `FvdepLedgerFixtures.InterpreterExempt.plan
          path :=
            [`FvdepLedgerFixtures.InterpreterExempt.main,
              `FvdepLedgerFixtures.InterpreterExempt.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.InterpreterExempt
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.InterpreterExempt.interpret
          path :=
            [`FvdepLedgerFixtures.InterpreterExempt.main,
              `FvdepLedgerFixtures.InterpreterExempt.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.InterpreterExempt
