import FvdepLedger.Types

/-! Contract-only fixture: SupportUnusedProof. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.SupportUnusedProof

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
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.SupportUnusedProof.main
    interpreter := `FvdepLedgerFixtures.SupportUnusedProof.interpret
    plan := `FvdepLedgerFixtures.SupportUnusedProof.plan
    libs := [`FvdepLedgerFixtures.SupportUnusedProof]
    rows :=
      [{  component := `FvdepLedgerFixtures.SupportUnusedProof
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportUnusedProof.statement,
                `FvdepLedgerFixtures.SupportUnusedProof.proof)]
          subject := `FvdepLedgerFixtures.SupportUnusedProof.plan
          path :=
            [`FvdepLedgerFixtures.SupportUnusedProof.main,
              `FvdepLedgerFixtures.SupportUnusedProof.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportUnusedProof
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportUnusedProof.helperStatement,
                `FvdepLedgerFixtures.SupportUnusedProof.helperProof)]
          subject := `FvdepLedgerFixtures.SupportUnusedProof.helper
          path := []
          noCaller := "support"
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportUnusedProof
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.SupportUnusedProof.interpret
          path :=
            [`FvdepLedgerFixtures.SupportUnusedProof.main,
              `FvdepLedgerFixtures.SupportUnusedProof.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.SupportUnusedProof
