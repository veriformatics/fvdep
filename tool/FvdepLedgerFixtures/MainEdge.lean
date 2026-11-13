import FvdepLedger.Types

/-! Contract-only fixture: MainEdge. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MainEdge

def subject (args : List String) : Nat := args.length

def subjectStatement : Prop := ∀ args : List String, subject args = args.length

theorem subjectProof : ∀ args : List String, subject args = args.length := by
  intro args
  rfl

def plan (args : List String) : Nat := subject args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = subject args

theorem proof : ∀ args : List String, plan args = subject args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MainEdge.main
    interpreter := `FvdepLedgerFixtures.MainEdge.interpret
    plan := `FvdepLedgerFixtures.MainEdge.plan
    libs := [`FvdepLedgerFixtures.MainEdge]
    rows :=
      [{  component := `FvdepLedgerFixtures.MainEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.MainEdge.statement, `FvdepLedgerFixtures.MainEdge.proof)]
          subject := `FvdepLedgerFixtures.MainEdge.plan
          path := [`FvdepLedgerFixtures.MainEdge.main, `FvdepLedgerFixtures.MainEdge.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MainEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.MainEdge.statement, `FvdepLedgerFixtures.MainEdge.proof)]
          subject := `FvdepLedgerFixtures.MainEdge.subject
          path := [`FvdepLedgerFixtures.MainEdge.main, `FvdepLedgerFixtures.MainEdge.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MainEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MainEdge.interpret
          path := [`FvdepLedgerFixtures.MainEdge.main, `FvdepLedgerFixtures.MainEdge.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MainEdge
