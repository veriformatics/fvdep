import FvdepLedger.Types

/-! Contract-only fixture: TransitiveEdge. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.TransitiveEdge

def subject (args : List String) : Nat := args.length

def via (args : List String) : Nat := subject args

def plan (args : List String) : Nat := via args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = subject args

theorem proof : ∀ args : List String, plan args = subject args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.TransitiveEdge.main
    interpreter := `FvdepLedgerFixtures.TransitiveEdge.interpret
    plan := `FvdepLedgerFixtures.TransitiveEdge.plan
    libs := [`FvdepLedgerFixtures.TransitiveEdge]
    rows :=
      [{  component := `FvdepLedgerFixtures.TransitiveEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.TransitiveEdge.statement,
                `FvdepLedgerFixtures.TransitiveEdge.proof)]
          subject := `FvdepLedgerFixtures.TransitiveEdge.plan
          path :=
            [`FvdepLedgerFixtures.TransitiveEdge.main, `FvdepLedgerFixtures.TransitiveEdge.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.TransitiveEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.TransitiveEdge.statement,
                `FvdepLedgerFixtures.TransitiveEdge.proof)]
          subject := `FvdepLedgerFixtures.TransitiveEdge.subject
          path :=
            [`FvdepLedgerFixtures.TransitiveEdge.main, `FvdepLedgerFixtures.TransitiveEdge.plan,
              `FvdepLedgerFixtures.TransitiveEdge.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.TransitiveEdge
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.TransitiveEdge.interpret
          path :=
            [`FvdepLedgerFixtures.TransitiveEdge.main,
              `FvdepLedgerFixtures.TransitiveEdge.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.TransitiveEdge
