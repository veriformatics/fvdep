import FvdepLedger.Types

/-! Contract-only fixture: Nonliteral. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Nonliteral

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Nonliteral.main
    interpreter := `FvdepLedgerFixtures.Nonliteral.interpret
    plan := `FvdepLedgerFixtures.Nonliteral.plan
    libs := [`FvdepLedgerFixtures.Nonliteral]
    rows :=
      [{  component := `FvdepLedgerFixtures.Nonliteral
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.Nonliteral.statement, `FvdepLedgerFixtures.Nonliteral.proof)]
          subject := `FvdepLedgerFixtures.Nonliteral.plan
          path := [`FvdepLedgerFixtures.Nonliteral.main, `FvdepLedgerFixtures.Nonliteral.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Nonliteral
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Nonliteral.interpret
          path := [`FvdepLedgerFixtures.Nonliteral.main, `FvdepLedgerFixtures.Nonliteral.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

opaque hiddenLedger : FvdepLedger.Ledger := ledger

end FvdepLedgerFixtures.Nonliteral
