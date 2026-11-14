import Fvdep.Base64.Encode.V1_0_0

/-! `base64.decode@1.0.0`: RFC 4648 §4, standard alphabet, strict (§3.2 padding required, §3.3
characters outside the alphabet rejected, §3.5 canonical) ⇒ the exact inverse of
`base64.encode@1.0.0`: `decode s = some b ↔ encode b = s` (`inverse` + `canonical`). -/

namespace Fvdep.Base64.Decode.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0

def decode : List Char → Option (List UInt8) := decodeWith standard

/-- Every byte string's encoding decodes back to it. -/
def inverse : Prop := ∀ b : List UInt8, decode (Fvdep.Base64.Encode.V1_0_0.encode b) = some b

/-- Strict: an accepted string is exactly the encoding of its bytes (no second spelling). -/
def canonical : Prop :=
  ∀ (s : List Char) (b : List UInt8), decode s = some b → Fvdep.Base64.Encode.V1_0_0.encode b = s

end Fvdep.Base64.Decode.V1_0_0
