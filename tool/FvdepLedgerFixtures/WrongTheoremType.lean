import FvdepLedger.Types

/-! Contract-only fixture: WrongTheoremType. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.WrongTheoremType

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = plan args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.WrongTheoremType.main
    interpreter := `FvdepLedgerFixtures.WrongTheoremType.interpret
    plan := `FvdepLedgerFixtures.WrongTheoremType.plan
    libs := [`FvdepLedgerFixtures.WrongTheoremType]
    rows :=
      [{  component := `FvdepLedgerFixtures.WrongTheoremType
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.WrongTheoremType.statement,
                `FvdepLedgerFixtures.WrongTheoremType.proof)]
          subject := `FvdepLedgerFixtures.WrongTheoremType.plan
          path :=
            [`FvdepLedgerFixtures.WrongTheoremType.main, `FvdepLedgerFixtures.WrongTheoremType.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.WrongTheoremType
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.WrongTheoremType.interpret
          path :=
            [`FvdepLedgerFixtures.WrongTheoremType.main,
              `FvdepLedgerFixtures.WrongTheoremType.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.WrongTheoremType
