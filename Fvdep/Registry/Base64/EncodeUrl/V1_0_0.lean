import Fvdep.Abi.V1_0_0
import Fvdep.Base64.EncodeUrl.V1_0_0
import Fvdep.Registry.Types.V1

/-! Registry entry `base64.encode_url@1.0.0` (`docs/library.md` Registry). -/

namespace Fvdep.Registry.Base64.EncodeUrl.V1_0_0

def entry : Fvdep.Registry.Types.V1.Module where
  id := "base64.encode_url"
  version := "1.0.0"
  spec := ``Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl
  obligations := [``Fvdep.Base64.EncodeUrl.V1_0_0.bits, ``Fvdep.Base64.EncodeUrl.V1_0_0.length]
  abi := some ``Fvdep.Abi.V1_0_0.encoder
  compat := none

end Fvdep.Registry.Base64.EncodeUrl.V1_0_0
