import Fvdep.Base64.EncodeUrl.V1_0_0
import FvdepProofs.Base64.Rfc4648.V1_0_0

/-! Obligations of `Fvdep.Base64.EncodeUrl.V1_0_0`. -/

namespace FvdepProofs.Base64.EncodeUrl.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0 FvdepProofs.Base64.Rfc4648.V1_0_0

theorem bits : Fvdep.Base64.EncodeUrl.V1_0_0.bits := by
  intro b
  exact encodeWith_encodeBits url b

theorem length : Fvdep.Base64.EncodeUrl.V1_0_0.length := by
  intro b
  exact encodeWith_length url b

end FvdepProofs.Base64.EncodeUrl.V1_0_0
