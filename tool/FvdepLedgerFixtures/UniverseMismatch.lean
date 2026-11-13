import FvdepLedger.Types

/-! Contract-only fixture: UniverseMismatch. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.UniverseMismatch

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement.{u} : Prop := ∀ (α : Type u) (x : α), x = x ∧ plan [] = 0

theorem proof : ∀ (α : Type) (x : α), x = x ∧ plan [] = 0 := by
  intro α x
  exact ⟨rfl, rfl⟩

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.UniverseMismatch.main
    interpreter := `FvdepLedgerFixtures.UniverseMismatch.interpret
    plan := `FvdepLedgerFixtures.UniverseMismatch.plan
    libs := [`FvdepLedgerFixtures.UniverseMismatch]
    rows :=
      [{  component := `FvdepLedgerFixtures.UniverseMismatch
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.UniverseMismatch.statement,
                `FvdepLedgerFixtures.UniverseMismatch.proof)]
          subject := `FvdepLedgerFixtures.UniverseMismatch.plan
          path :=
            [`FvdepLedgerFixtures.UniverseMismatch.main, `FvdepLedgerFixtures.UniverseMismatch.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.UniverseMismatch
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.UniverseMismatch.interpret
          path :=
            [`FvdepLedgerFixtures.UniverseMismatch.main,
              `FvdepLedgerFixtures.UniverseMismatch.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.UniverseMismatch
