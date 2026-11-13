import FvdepLedger.Types
import FvdepLedgerFixtures.ForgedImport

/-! Contract-only fixture: ForgedUnusedImport. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.ForgedUnusedImport

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.ForgedUnusedImport.main
    interpreter := `FvdepLedgerFixtures.ForgedUnusedImport.interpret
    plan := `FvdepLedgerFixtures.ForgedUnusedImport.plan
    libs := [`FvdepLedgerFixtures.ForgedUnusedImport]
    rows :=
      [{  component := `FvdepLedgerFixtures.ForgedUnusedImport
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.ForgedUnusedImport.statement,
                `FvdepLedgerFixtures.ForgedUnusedImport.proof)]
          subject := `FvdepLedgerFixtures.ForgedUnusedImport.plan
          path :=
            [`FvdepLedgerFixtures.ForgedUnusedImport.main,
              `FvdepLedgerFixtures.ForgedUnusedImport.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.ForgedUnusedImport
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.ForgedUnusedImport.interpret
          path :=
            [`FvdepLedgerFixtures.ForgedUnusedImport.main,
              `FvdepLedgerFixtures.ForgedUnusedImport.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.ForgedUnusedImport
