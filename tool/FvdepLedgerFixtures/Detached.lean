import FvdepLedger.Types

/-! Contract-only fixture: Detached. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Detached

def parked (args : List String) : Nat := args.length

def parkedStatement : Prop := ∀ args : List String, parked args = args.length

theorem parkedProof : ∀ args : List String, parked args = args.length := by
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
  { main := `FvdepLedgerFixtures.Detached.main
    interpreter := `FvdepLedgerFixtures.Detached.interpret
    plan := `FvdepLedgerFixtures.Detached.plan
    libs := [`FvdepLedgerFixtures.Detached]
    rows :=
      [{  component := `FvdepLedgerFixtures.Detached
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Detached.statement, `FvdepLedgerFixtures.Detached.proof)]
          subject := `FvdepLedgerFixtures.Detached.plan
          path := [`FvdepLedgerFixtures.Detached.main, `FvdepLedgerFixtures.Detached.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Detached
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.Detached.parkedStatement,
                `FvdepLedgerFixtures.Detached.parkedProof)]
          subject := `FvdepLedgerFixtures.Detached.parked
          path := []
          noCaller := "U8"
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Detached
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Detached.interpret
          path := [`FvdepLedgerFixtures.Detached.main, `FvdepLedgerFixtures.Detached.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Detached
