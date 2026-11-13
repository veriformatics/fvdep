import FvdepLedger.Types

/-! Contract-only fixture: AlphaEquivalent. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.AlphaEquivalent

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ input : List String, plan input = input.length := by
  intro input
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.AlphaEquivalent.main
    interpreter := `FvdepLedgerFixtures.AlphaEquivalent.interpret
    plan := `FvdepLedgerFixtures.AlphaEquivalent.plan
    libs := [`FvdepLedgerFixtures.AlphaEquivalent]
    rows :=
      [{  component := `FvdepLedgerFixtures.AlphaEquivalent
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.AlphaEquivalent.statement,
                `FvdepLedgerFixtures.AlphaEquivalent.proof)]
          subject := `FvdepLedgerFixtures.AlphaEquivalent.plan
          path :=
            [`FvdepLedgerFixtures.AlphaEquivalent.main, `FvdepLedgerFixtures.AlphaEquivalent.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.AlphaEquivalent
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.AlphaEquivalent.interpret
          path :=
            [`FvdepLedgerFixtures.AlphaEquivalent.main,
              `FvdepLedgerFixtures.AlphaEquivalent.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.AlphaEquivalent
