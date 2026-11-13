import FvdepLedger.Types

/-! Contract-only fixture: DefeqNotAlpha. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.DefeqNotAlpha

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, args.length = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.DefeqNotAlpha.main
    interpreter := `FvdepLedgerFixtures.DefeqNotAlpha.interpret
    plan := `FvdepLedgerFixtures.DefeqNotAlpha.plan
    libs := [`FvdepLedgerFixtures.DefeqNotAlpha]
    rows :=
      [{  component := `FvdepLedgerFixtures.DefeqNotAlpha
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.DefeqNotAlpha.statement,
                `FvdepLedgerFixtures.DefeqNotAlpha.proof)]
          subject := `FvdepLedgerFixtures.DefeqNotAlpha.plan
          path := [`FvdepLedgerFixtures.DefeqNotAlpha.main, `FvdepLedgerFixtures.DefeqNotAlpha.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.DefeqNotAlpha
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.DefeqNotAlpha.interpret
          path :=
            [`FvdepLedgerFixtures.DefeqNotAlpha.main, `FvdepLedgerFixtures.DefeqNotAlpha.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.DefeqNotAlpha
