import FvdepLedger.Types

/-! Contract-only fixture: UnknownUnproven. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UnknownUnproven

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.UnknownUnproven.main
    interpreter := `FvdepLedgerFixtures.UnknownUnproven.interpret
    plan := `FvdepLedgerFixtures.UnknownUnproven.plan
    libs := [`FvdepLedgerFixtures.UnknownUnproven]
    rows :=
      [{  component := `FvdepLedgerFixtures.UnknownUnproven
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UnknownUnproven.plan
          path :=
            [`FvdepLedgerFixtures.UnknownUnproven.main, `FvdepLedgerFixtures.UnknownUnproven.plan]
          noCaller := ""
          residue := []
          unproven := ["absent"] },
        { component := `FvdepLedgerFixtures.UnknownUnproven
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UnknownUnproven.interpret
          path :=
            [`FvdepLedgerFixtures.UnknownUnproven.main,
              `FvdepLedgerFixtures.UnknownUnproven.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.UnknownUnproven
