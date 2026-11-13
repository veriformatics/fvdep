import FvdepLedger.Types
import FvdepLedgerFixtures.UnusedLib.Child

/-! Contract-only fixture: MissingUnusedLibrary. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MissingUnusedLibrary

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MissingUnusedLibrary.main
    interpreter := `FvdepLedgerFixtures.MissingUnusedLibrary.interpret
    plan := `FvdepLedgerFixtures.MissingUnusedLibrary.plan
    libs := [`FvdepLedgerFixtures.MissingUnusedLibrary, `FvdepLedgerFixtures.UnusedLib]
    rows :=
      [{  component := `FvdepLedgerFixtures.MissingUnusedLibrary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MissingUnusedLibrary.statement,
                `FvdepLedgerFixtures.MissingUnusedLibrary.proof)]
          subject := `FvdepLedgerFixtures.MissingUnusedLibrary.plan
          path :=
            [`FvdepLedgerFixtures.MissingUnusedLibrary.main,
              `FvdepLedgerFixtures.MissingUnusedLibrary.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MissingUnusedLibrary
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MissingUnusedLibrary.interpret
          path :=
            [`FvdepLedgerFixtures.MissingUnusedLibrary.main,
              `FvdepLedgerFixtures.MissingUnusedLibrary.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MissingUnusedLibrary
