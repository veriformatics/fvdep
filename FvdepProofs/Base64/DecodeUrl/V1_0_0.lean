import Fvdep.Base64.DecodeUrl.V1_0_0
import FvdepProofs.Base64.Rfc4648.V1_0_0

/-! Obligations of `Fvdep.Base64.DecodeUrl.V1_0_0`. -/

namespace FvdepProofs.Base64.DecodeUrl.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0 FvdepProofs.Base64.Rfc4648.V1_0_0

theorem inverse : Fvdep.Base64.DecodeUrl.V1_0_0.inverse := by
  intro b
  exact decodeWith_encodeWith url_good b

theorem canonical : Fvdep.Base64.DecodeUrl.V1_0_0.canonical := by
  intro s b h
  exact encodeWith_decodeWith url_good s b h

end FvdepProofs.Base64.DecodeUrl.V1_0_0
