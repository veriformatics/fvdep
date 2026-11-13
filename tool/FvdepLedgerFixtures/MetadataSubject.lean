import FvdepLedger.Types

/-! Contract-only fixture: MetadataSubject. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.MetadataSubject

def _root_.LooksForeign.subject (args : List String) : Nat := args.length

def plan (args : List String) : Nat := LooksForeign.subject args

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop := ∀ args : List String, plan args = LooksForeign.subject args

theorem proof : ∀ args : List String, plan args = LooksForeign.subject args := by
  intro args
  rfl

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.MetadataSubject.main
    interpreter := `FvdepLedgerFixtures.MetadataSubject.interpret
    plan := `FvdepLedgerFixtures.MetadataSubject.plan
    libs := [`FvdepLedgerFixtures.MetadataSubject]
    rows :=
      [{  component := `FvdepLedgerFixtures.MetadataSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MetadataSubject.statement,
                `FvdepLedgerFixtures.MetadataSubject.proof)]
          subject := `FvdepLedgerFixtures.MetadataSubject.plan
          path :=
            [`FvdepLedgerFixtures.MetadataSubject.main, `FvdepLedgerFixtures.MetadataSubject.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MetadataSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.MetadataSubject.statement,
                `FvdepLedgerFixtures.MetadataSubject.proof)]
          subject := `LooksForeign.subject
          path :=
            [`FvdepLedgerFixtures.MetadataSubject.main, `FvdepLedgerFixtures.MetadataSubject.plan,
              `LooksForeign.subject]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.MetadataSubject
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.MetadataSubject.interpret
          path :=
            [`FvdepLedgerFixtures.MetadataSubject.main,
              `FvdepLedgerFixtures.MetadataSubject.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.MetadataSubject
