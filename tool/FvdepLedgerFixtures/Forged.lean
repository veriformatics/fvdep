import FvdepLedger.Types
import FvdepLedgerFixtures.ForgedImport

/-! Contract-only fixture: Forged. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.Forged

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length :=
  False.elim FvdepLedgerFixtures.ForgedImport.falseProof

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.Forged.main
    interpreter := `FvdepLedgerFixtures.Forged.interpret
    plan := `FvdepLedgerFixtures.Forged.plan
    libs := [`FvdepLedgerFixtures.Forged]
    rows :=
      [{  component := `FvdepLedgerFixtures.Forged
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := [(`FvdepLedgerFixtures.Forged.statement, `FvdepLedgerFixtures.Forged.proof)]
          subject := `FvdepLedgerFixtures.Forged.plan
          path := [`FvdepLedgerFixtures.Forged.main, `FvdepLedgerFixtures.Forged.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.Forged
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.Forged.interpret
          path := [`FvdepLedgerFixtures.Forged.main, `FvdepLedgerFixtures.Forged.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.Forged
