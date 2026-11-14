import Fvdep.Base64.EncodeUrl.V1_0_0

/-! `base64.decode_url@1.0.0`: RFC 4648 §5 alphabet (Table 2), strict as `base64.decode@1.0.0` ⇒
the exact inverse of `base64.encode_url@1.0.0` (`inverse` + `canonical`). -/

namespace Fvdep.Base64.DecodeUrl.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0

def decodeUrl : List Char → Option (List UInt8) := decodeWith url

/-- Every byte string's encoding decodes back to it. -/
def inverse : Prop :=
  ∀ b : List UInt8, decodeUrl (Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl b) = some b

/-- Strict: an accepted string is exactly the encoding of its bytes (no second spelling). -/
def canonical : Prop :=
  ∀ (s : List Char) (b : List UInt8),
    decodeUrl s = some b → Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl b = s

end Fvdep.Base64.DecodeUrl.V1_0_0
