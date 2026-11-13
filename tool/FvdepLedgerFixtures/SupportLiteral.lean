import FvdepLedger.Types

/-! Contract-only fixture: SupportLiteral. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.SupportLiteral

def literal : List String := []

def plan (args : List String) : Nat := (literal ++ args).length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.SupportLiteral.main
    interpreter := `FvdepLedgerFixtures.SupportLiteral.interpret
    plan := `FvdepLedgerFixtures.SupportLiteral.plan
    libs := [`FvdepLedgerFixtures.SupportLiteral]
    rows :=
      [{  component := `FvdepLedgerFixtures.SupportLiteral
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.SupportLiteral.statement,
                `FvdepLedgerFixtures.SupportLiteral.proof)]
          subject := `FvdepLedgerFixtures.SupportLiteral.plan
          path :=
            [`FvdepLedgerFixtures.SupportLiteral.main, `FvdepLedgerFixtures.SupportLiteral.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.SupportLiteral
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.SupportLiteral.literal
          path := []
          noCaller := "support"
          residue := []
          unproven := ["literal"] },
        { component := `FvdepLedgerFixtures.SupportLiteral
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.SupportLiteral.interpret
          path :=
            [`FvdepLedgerFixtures.SupportLiteral.main,
              `FvdepLedgerFixtures.SupportLiteral.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] },
        { id := "literal"
          what := "Fixture literal data."
          reason := "Literal data has a structural check, not a theorem."
          ruling := "Fixture literal data is structurally checked."
          boundary := [] }] }

end FvdepLedgerFixtures.SupportLiteral
