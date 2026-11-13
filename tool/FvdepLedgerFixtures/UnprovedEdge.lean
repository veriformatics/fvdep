import FvdepLedger.Types

/-! Contract-only fixture: UnprovedEdge. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UnprovedEdge

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
  { main := `FvdepLedgerFixtures.UnprovedEdge.main
    interpreter := `FvdepLedgerFixtures.UnprovedEdge.interpret
    plan := `FvdepLedgerFixtures.UnprovedEdge.plan
    libs := [`FvdepLedgerFixtures.UnprovedEdge]
    rows :=
      [{  component := `FvdepLedgerFixtures.UnprovedEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UnprovedEdge.statement, `FvdepLedgerFixtures.UnprovedEdge.proof)]
          subject := `FvdepLedgerFixtures.UnprovedEdge.plan
          path := [`FvdepLedgerFixtures.UnprovedEdge.main, `FvdepLedgerFixtures.UnprovedEdge.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.UnprovedEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UnprovedEdge.subjectStatement,
                `FvdepLedgerFixtures.UnprovedEdge.subjectProof)]
          subject := `FvdepLedgerFixtures.UnprovedEdge.subject
          path :=
            [`FvdepLedgerFixtures.UnprovedEdge.main, `FvdepLedgerFixtures.UnprovedEdge.plan,
              `FvdepLedgerFixtures.UnprovedEdge.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.UnprovedEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UnprovedEdge.interpret
          path :=
            [`FvdepLedgerFixtures.UnprovedEdge.main, `FvdepLedgerFixtures.UnprovedEdge.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.UnprovedEdge
