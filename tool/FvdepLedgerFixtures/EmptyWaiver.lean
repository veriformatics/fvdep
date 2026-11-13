import FvdepLedger.Types

/-! Contract-only fixture: EmptyWaiver. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.EmptyWaiver

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = args.length

theorem proof : ∀ args : List String, plan args = args.length := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.EmptyWaiver.main
    interpreter := `FvdepLedgerFixtures.EmptyWaiver.interpret
    plan := `FvdepLedgerFixtures.EmptyWaiver.plan
    libs := [`FvdepLedgerFixtures.EmptyWaiver]
    rows :=
      [{  component := `FvdepLedgerFixtures.EmptyWaiver
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.EmptyWaiver.plan
          path := [`FvdepLedgerFixtures.EmptyWaiver.main, `FvdepLedgerFixtures.EmptyWaiver.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.EmptyWaiver
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.EmptyWaiver.interpret
          path :=
            [`FvdepLedgerFixtures.EmptyWaiver.main, `FvdepLedgerFixtures.EmptyWaiver.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.EmptyWaiver
