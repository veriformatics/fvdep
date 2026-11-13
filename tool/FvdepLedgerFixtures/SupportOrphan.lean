import FvdepLedger.Types

/-! Contract-only fixture: SupportOrphan. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.SupportOrphan

def helper (args : List String) : Nat := args.length

def helperStatement : Prop := ∀ args : List String, helper args = args.length

theorem helperProof : ∀ args : List String, helper args = args.length := by
  intro args
  rfl

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.SupportOrphan.main
    interpreter := `FvdepLedgerFixtures.SupportOrphan.interpret
    plan := `FvdepLedgerFixtures.SupportOrphan.plan
    libs := [`FvdepLedgerFixtures.SupportOrphan]
    rows :=
      [{  component := `FvdepLedgerFixtures.SupportOrphan
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportOrphan.statement,
                `FvdepLedgerFixtures.SupportOrphan.proof)]
          subject := `FvdepLedgerFixtures.SupportOrphan.plan
          path := [`FvdepLedgerFixtures.SupportOrphan.main, `FvdepLedgerFixtures.SupportOrphan.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportOrphan
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportOrphan.helperStatement,
                `FvdepLedgerFixtures.SupportOrphan.helperProof)]
          subject := `FvdepLedgerFixtures.SupportOrphan.helper
          path := []
          noCaller := "support"
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportOrphan
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.SupportOrphan.interpret
          path :=
            [`FvdepLedgerFixtures.SupportOrphan.main, `FvdepLedgerFixtures.SupportOrphan.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.SupportOrphan
