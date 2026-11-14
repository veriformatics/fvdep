import Fvdep.Base64.Encode.V1_0_0
import FvdepProofs.Base64.Rfc4648.V1_0_0

/-! Obligations of `Fvdep.Base64.Encode.V1_0_0`. -/

namespace FvdepProofs.Base64.Encode.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0 FvdepProofs.Base64.Rfc4648.V1_0_0

theorem bits : Fvdep.Base64.Encode.V1_0_0.bits := by
  intro b
  exact encodeWith_encodeBits standard b

theorem length : Fvdep.Base64.Encode.V1_0_0.length := by
  intro b
  exact encodeWith_length standard b

end FvdepProofs.Base64.Encode.V1_0_0
