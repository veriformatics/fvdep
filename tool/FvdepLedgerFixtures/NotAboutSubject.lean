import FvdepLedger.Types

/-! Contract-only fixture: NotAboutSubject. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NotAboutSubject

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := True

theorem proof : True := True.intro

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NotAboutSubject.main
    interpreter := `FvdepLedgerFixtures.NotAboutSubject.interpret
    plan := `FvdepLedgerFixtures.NotAboutSubject.plan
    libs := [`FvdepLedgerFixtures.NotAboutSubject]
    rows :=
      [{  component := `FvdepLedgerFixtures.NotAboutSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NotAboutSubject.statement,
                `FvdepLedgerFixtures.NotAboutSubject.proof)]
          subject := `FvdepLedgerFixtures.NotAboutSubject.plan
          path :=
            [`FvdepLedgerFixtures.NotAboutSubject.main, `FvdepLedgerFixtures.NotAboutSubject.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NotAboutSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NotAboutSubject.interpret
          path :=
            [`FvdepLedgerFixtures.NotAboutSubject.main,
              `FvdepLedgerFixtures.NotAboutSubject.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NotAboutSubject
