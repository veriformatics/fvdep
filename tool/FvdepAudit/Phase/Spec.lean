import FvdepCore.Phase

/-! Specs for a phase's driver (contract `docs/contracts/U5-sandbox.md` P8): the recorder that
observes which steps run, in order. -/

namespace FvdepAudit.Phase.Spec

open FvdepCore.Phase

/-- The driver run with a recorder: each executed step appended to the state, answered by
`answer`. -/
def record (answer : Step → StepResult) (s : Step) : StateM (List Step) StepResult := do
  modify (· ++ [s])
  pure (answer s)

end FvdepAudit.Phase.Spec
