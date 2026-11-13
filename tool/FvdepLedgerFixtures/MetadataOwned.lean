import FvdepLedger.Types
import FvdepLedgerFixtures.MetadataImport

/-! Contract-only fixture: MetadataOwned. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MetadataOwned

def plan (args : List String) : Nat := LooksForeign.step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MetadataOwned.main
    interpreter := `FvdepLedgerFixtures.MetadataOwned.interpret
    plan := `FvdepLedgerFixtures.MetadataOwned.plan
    libs := [`FvdepLedgerFixtures.MetadataOwned]
    rows :=
      [{  component := `FvdepLedgerFixtures.MetadataOwned
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MetadataOwned.statement,
                `FvdepLedgerFixtures.MetadataOwned.proof)]
          subject := `FvdepLedgerFixtures.MetadataOwned.plan
          path := [`FvdepLedgerFixtures.MetadataOwned.main, `FvdepLedgerFixtures.MetadataOwned.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MetadataOwned
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MetadataOwned.interpret
          path :=
            [`FvdepLedgerFixtures.MetadataOwned.main, `FvdepLedgerFixtures.MetadataOwned.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MetadataOwned
