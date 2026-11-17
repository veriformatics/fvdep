import FvdepAudit.Json.Spec
import FvdepCore.Step

/-! U5 R8 (contract `docs/contracts/U5-sandbox.md` R8): the bounds J's profile sets on the step
status record, written apart from the codec. -/

namespace FvdepAudit.Step.Spec

open FvdepCore.Step FvdepCore.Phase FvdepAudit.Json.Spec

/-- The status record fits J's profile: its number ≤ `maxInt`, its reason ≤ `maxStringBytes`. -/
def StatusFits (s : Status) : Prop :=
  match s.child with
  | .exited c => c ≤ maxInt
  | .signaled n => n ≤ maxInt
  | .notStarted r => r.utf8ByteSize ≤ maxStringBytes

end FvdepAudit.Step.Spec
