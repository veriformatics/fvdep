import FvdepLedger.Types
import FvdepLedgerFixtures.MissingModuleImport

/-! Contract-only fixture: MissingReachableModule. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MissingReachableModule

def plan (args : List String) : Nat := FvdepLedgerFixtures.MissingModuleImport.step args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MissingReachableModule.main
    interpreter := `FvdepLedgerFixtures.MissingReachableModule.interpret
    plan := `FvdepLedgerFixtures.MissingReachableModule.plan
    libs := [`FvdepLedgerFixtures.MissingReachableModule]
    rows :=
      [{  component := `FvdepLedgerFixtures.MissingReachableModule
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MissingReachableModule.statement,
                `FvdepLedgerFixtures.MissingReachableModule.proof)]
          subject := `FvdepLedgerFixtures.MissingReachableModule.plan
          path :=
            [`FvdepLedgerFixtures.MissingReachableModule.main,
              `FvdepLedgerFixtures.MissingReachableModule.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MissingReachableModule
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MissingReachableModule.interpret
          path :=
            [`FvdepLedgerFixtures.MissingReachableModule.main,
              `FvdepLedgerFixtures.MissingReachableModule.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MissingReachableModule
