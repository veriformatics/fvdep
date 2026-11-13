import FvdepLedger.Types

/-! Contract-only fixture: Support. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Support

def helper (args : List String) : Nat := args.length

def helperStatement : Prop := ∀ args : List String, helper args = args.length

theorem helperProof : ∀ args : List String, helper args = args.length := by
  intro args
  rfl

def plan (args : List String) : Nat := helper args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  exact helperProof args

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Support.main
    interpreter := `FvdepLedgerFixtures.Support.interpret
    plan := `FvdepLedgerFixtures.Support.plan
    libs := [`FvdepLedgerFixtures.Support]
    rows :=
      [{  component := `FvdepLedgerFixtures.Support
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Support.statement, `FvdepLedgerFixtures.Support.proof)]
          subject := `FvdepLedgerFixtures.Support.plan
          path := [`FvdepLedgerFixtures.Support.main, `FvdepLedgerFixtures.Support.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Support
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.Support.helperStatement,
                `FvdepLedgerFixtures.Support.helperProof)]
          subject := `FvdepLedgerFixtures.Support.helper
          path := []
          noCaller := "support"
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Support
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Support.interpret
          path := [`FvdepLedgerFixtures.Support.main, `FvdepLedgerFixtures.Support.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Support
