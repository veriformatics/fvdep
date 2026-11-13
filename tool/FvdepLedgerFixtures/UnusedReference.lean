import FvdepLedger.Types

/-! Contract-only fixture: UnusedReference. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UnusedReference

def subject (args : List String) : Nat := args.length

def plan (args : List String) : Nat :=
  let _ := subject args
  0

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = subject args

theorem proof : ∀ args : List String, plan args = 0 := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.UnusedReference.main
    interpreter := `FvdepLedgerFixtures.UnusedReference.interpret
    plan := `FvdepLedgerFixtures.UnusedReference.plan
    libs := [`FvdepLedgerFixtures.UnusedReference]
    rows :=
      [{  component := `FvdepLedgerFixtures.UnusedReference
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UnusedReference.statement,
                `FvdepLedgerFixtures.UnusedReference.proof)]
          subject := `FvdepLedgerFixtures.UnusedReference.plan
          path :=
            [`FvdepLedgerFixtures.UnusedReference.main, `FvdepLedgerFixtures.UnusedReference.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.UnusedReference
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UnusedReference.statement,
                `FvdepLedgerFixtures.UnusedReference.proof)]
          subject := `FvdepLedgerFixtures.UnusedReference.subject
          path :=
            [`FvdepLedgerFixtures.UnusedReference.main, `FvdepLedgerFixtures.UnusedReference.plan,
              `FvdepLedgerFixtures.UnusedReference.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.UnusedReference
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UnusedReference.interpret
          path :=
            [`FvdepLedgerFixtures.UnusedReference.main,
              `FvdepLedgerFixtures.UnusedReference.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.UnusedReference
