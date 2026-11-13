import FvdepLedger.Types

/-! Contract-only fixture: SupportBadPath. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.SupportBadPath

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
  { main := `FvdepLedgerFixtures.SupportBadPath.main
    interpreter := `FvdepLedgerFixtures.SupportBadPath.interpret
    plan := `FvdepLedgerFixtures.SupportBadPath.plan
    libs := [`FvdepLedgerFixtures.SupportBadPath]
    rows :=
      [{  component := `FvdepLedgerFixtures.SupportBadPath
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportBadPath.statement,
                `FvdepLedgerFixtures.SupportBadPath.proof)]
          subject := `FvdepLedgerFixtures.SupportBadPath.plan
          path := [`FvdepLedgerFixtures.SupportBadPath.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportBadPath
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportBadPath.helperStatement,
                `FvdepLedgerFixtures.SupportBadPath.helperProof)]
          subject := `FvdepLedgerFixtures.SupportBadPath.helper
          path := []
          noCaller := "support"
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportBadPath
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.SupportBadPath.interpret
          path :=
            [`FvdepLedgerFixtures.SupportBadPath.main,
              `FvdepLedgerFixtures.SupportBadPath.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.SupportBadPath
