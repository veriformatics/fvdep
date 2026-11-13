import FvdepLedger.Types

/-! Contract-only fixture: UnknownResidue. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UnknownResidue

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.UnknownResidue.main
    interpreter := `FvdepLedgerFixtures.UnknownResidue.interpret
    plan := `FvdepLedgerFixtures.UnknownResidue.plan
    libs := [`FvdepLedgerFixtures.UnknownResidue]
    rows :=
      [{  component := `FvdepLedgerFixtures.UnknownResidue
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UnknownResidue.statement,
                `FvdepLedgerFixtures.UnknownResidue.proof)]
          subject := `FvdepLedgerFixtures.UnknownResidue.plan
          path :=
            [`FvdepLedgerFixtures.UnknownResidue.main, `FvdepLedgerFixtures.UnknownResidue.plan]
          noCaller := ""
          residue := ["absent"]
          unproven := [] },
        { component := `FvdepLedgerFixtures.UnknownResidue
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UnknownResidue.interpret
          path :=
            [`FvdepLedgerFixtures.UnknownResidue.main,
              `FvdepLedgerFixtures.UnknownResidue.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.UnknownResidue
