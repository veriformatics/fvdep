import Fvdep.Base64.Decode.V1_0_0
import Fvdep.Base64.DecodeUrl.V1_0_0
/-!
# Profile: crates.io `base64` 0.22.1 (engines `STANDARD`, `URL_SAFE`, default config)

No deviations: the model is the contract itself (`*_eq_contract`, by `rfl`).
That the real crate behaves like this model is evidence only:
`fvdep profile crates:base64 --check` compares the crate with the model.
-/
namespace Fvdep.Profiles.CratesBase64.V0_22_1
open Fvdep.Base64

def encode := Encode.V1_0_0.encode
def decode := Decode.V1_0_0.decode
def encodeUrl := EncodeUrl.V1_0_0.encodeUrl
def decodeUrl := DecodeUrl.V1_0_0.decodeUrl

theorem encode_eq_contract : encode = Encode.V1_0_0.encode := rfl
theorem decode_eq_contract : decode = Decode.V1_0_0.decode := rfl
theorem encodeUrl_eq_contract : encodeUrl = EncodeUrl.V1_0_0.encodeUrl := rfl
theorem decodeUrl_eq_contract : decodeUrl = DecodeUrl.V1_0_0.decodeUrl := rfl

end Fvdep.Profiles.CratesBase64.V0_22_1
