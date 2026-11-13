import FvdepLedger.Types

/-! Contract-only fixture: Bypass. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Bypass

def subject (args : List String) : Nat := args.length

def other (args : List String) : Nat := args.length + 1

def subjectStatement : Prop := ∀ args : List String, subject args = args.length

theorem subjectProof : ∀ args : List String, subject args = args.length := by
  intro args
  rfl

def plan (args : List String) : Nat := other args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = other args

theorem proof : ∀ args : List String, plan args = other args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Bypass.main
    interpreter := `FvdepLedgerFixtures.Bypass.interpret
    plan := `FvdepLedgerFixtures.Bypass.plan
    libs := [`FvdepLedgerFixtures.Bypass]
    rows :=
      [{  component := `FvdepLedgerFixtures.Bypass
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Bypass.statement, `FvdepLedgerFixtures.Bypass.proof)]
          subject := `FvdepLedgerFixtures.Bypass.plan
          path := [`FvdepLedgerFixtures.Bypass.main, `FvdepLedgerFixtures.Bypass.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Bypass
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.Bypass.subjectStatement,
                `FvdepLedgerFixtures.Bypass.subjectProof)]
          subject := `FvdepLedgerFixtures.Bypass.subject
          path :=
            [`FvdepLedgerFixtures.Bypass.main, `FvdepLedgerFixtures.Bypass.plan,
              `FvdepLedgerFixtures.Bypass.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Bypass
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Bypass.interpret
          path := [`FvdepLedgerFixtures.Bypass.main, `FvdepLedgerFixtures.Bypass.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Bypass
