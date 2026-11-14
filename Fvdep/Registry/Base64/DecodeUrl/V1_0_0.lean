import Fvdep.Abi.V1_0_0
import Fvdep.Base64.DecodeUrl.V1_0_0
import Fvdep.Registry.Types.V1

/-! Registry entry `base64.decode_url@1.0.0` (`docs/library.md` Registry). -/

namespace Fvdep.Registry.Base64.DecodeUrl.V1_0_0

def entry : Fvdep.Registry.Types.V1.Module where
  id := "base64.decode_url"
  version := "1.0.0"
  spec := ``Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl
  obligations :=
    [``Fvdep.Base64.DecodeUrl.V1_0_0.inverse, ``Fvdep.Base64.DecodeUrl.V1_0_0.canonical]
  abi := some ``Fvdep.Abi.V1_0_0.decoder
  compat := none

end Fvdep.Registry.Base64.DecodeUrl.V1_0_0
