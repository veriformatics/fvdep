import FvdepLedger.Types

/-! Contract-only fixture: MissingSubject. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MissingSubject

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MissingSubject.main
    interpreter := `FvdepLedgerFixtures.MissingSubject.interpret
    plan := `FvdepLedgerFixtures.MissingSubject.plan
    libs := [`FvdepLedgerFixtures.MissingSubject]
    rows :=
      [{  component := `FvdepLedgerFixtures.MissingSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MissingSubject.statement,
                `FvdepLedgerFixtures.MissingSubject.proof)]
          subject := `FvdepLedgerFixtures.MissingSubject.absentSubject
          path :=
            [`FvdepLedgerFixtures.MissingSubject.main, `FvdepLedgerFixtures.MissingSubject.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MissingSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MissingSubject.interpret
          path :=
            [`FvdepLedgerFixtures.MissingSubject.main,
              `FvdepLedgerFixtures.MissingSubject.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MissingSubject
