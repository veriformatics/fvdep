import FvdepLedger.Types

/-! Contract-only fixture: RootSubject. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.RootSubject

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

def rootStatement : Prop := ∀ args : List String, main args = interpret (plan args)

theorem rootProof : ∀ args : List String, main args = interpret (plan args) := by
  intro args
  rfl

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.RootSubject.main
    interpreter := `FvdepLedgerFixtures.RootSubject.interpret
    plan := `FvdepLedgerFixtures.RootSubject.plan
    libs := [`FvdepLedgerFixtures.RootSubject]
    rows :=
      [{  component := `FvdepLedgerFixtures.RootSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.RootSubject.statement, `FvdepLedgerFixtures.RootSubject.proof)]
          subject := `FvdepLedgerFixtures.RootSubject.plan
          path := [`FvdepLedgerFixtures.RootSubject.main, `FvdepLedgerFixtures.RootSubject.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.RootSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.RootSubject.rootStatement,
                `FvdepLedgerFixtures.RootSubject.rootProof)]
          subject := `FvdepLedgerFixtures.RootSubject.main
          path := [`FvdepLedgerFixtures.RootSubject.main]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.RootSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.RootSubject.interpret
          path :=
            [`FvdepLedgerFixtures.RootSubject.main, `FvdepLedgerFixtures.RootSubject.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.RootSubject
