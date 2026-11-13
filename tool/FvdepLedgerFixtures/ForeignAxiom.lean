import FvdepLedger.Types

/-! Contract-only fixture: ForeignAxiom. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.ForeignAxiom

axiom oracle : ∀ args : List String, args.length = args.length

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  exact oracle args

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.ForeignAxiom.main
    interpreter := `FvdepLedgerFixtures.ForeignAxiom.interpret
    plan := `FvdepLedgerFixtures.ForeignAxiom.plan
    libs := [`FvdepLedgerFixtures.ForeignAxiom]
    rows :=
      [{  component := `FvdepLedgerFixtures.ForeignAxiom
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.ForeignAxiom.statement, `FvdepLedgerFixtures.ForeignAxiom.proof)]
          subject := `FvdepLedgerFixtures.ForeignAxiom.plan
          path := [`FvdepLedgerFixtures.ForeignAxiom.main, `FvdepLedgerFixtures.ForeignAxiom.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.ForeignAxiom
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.ForeignAxiom.interpret
          path :=
            [`FvdepLedgerFixtures.ForeignAxiom.main, `FvdepLedgerFixtures.ForeignAxiom.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.ForeignAxiom
