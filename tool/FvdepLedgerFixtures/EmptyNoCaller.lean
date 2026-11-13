import FvdepLedger.Types

/-! Contract-only fixture: EmptyNoCaller. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.EmptyNoCaller

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.EmptyNoCaller.main
    interpreter := `FvdepLedgerFixtures.EmptyNoCaller.interpret
    plan := `FvdepLedgerFixtures.EmptyNoCaller.plan
    libs := [`FvdepLedgerFixtures.EmptyNoCaller]
    rows :=
      [{  component := `FvdepLedgerFixtures.EmptyNoCaller
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.EmptyNoCaller.statement,
                `FvdepLedgerFixtures.EmptyNoCaller.proof)]
          subject := `FvdepLedgerFixtures.EmptyNoCaller.plan
          path := []
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.EmptyNoCaller
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.EmptyNoCaller.interpret
          path :=
            [`FvdepLedgerFixtures.EmptyNoCaller.main, `FvdepLedgerFixtures.EmptyNoCaller.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.EmptyNoCaller
