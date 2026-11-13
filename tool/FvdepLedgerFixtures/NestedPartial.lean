import FvdepLedger.Types

/-! Contract-only fixture: NestedPartial. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.NestedPartial

partial def hidden (n : Nat) : Nat := if n == 0 then 0 else hidden (n - 1)

def helper (args : List String) : Nat := hidden args.length

def plan (args : List String) : Nat := helper args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = helper args

theorem proof : ∀ args : List String, plan args = helper args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.NestedPartial.main
    interpreter := `FvdepLedgerFixtures.NestedPartial.interpret
    plan := `FvdepLedgerFixtures.NestedPartial.plan
    libs := [`FvdepLedgerFixtures.NestedPartial]
    rows :=
      [{  component := `FvdepLedgerFixtures.NestedPartial
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.NestedPartial.statement,
                `FvdepLedgerFixtures.NestedPartial.proof)]
          subject := `FvdepLedgerFixtures.NestedPartial.plan
          path := [`FvdepLedgerFixtures.NestedPartial.main, `FvdepLedgerFixtures.NestedPartial.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.NestedPartial
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.NestedPartial.interpret
          path :=
            [`FvdepLedgerFixtures.NestedPartial.main, `FvdepLedgerFixtures.NestedPartial.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.NestedPartial
