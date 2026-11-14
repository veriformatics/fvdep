import Fvdep.Base64.Rfc4648.V1_0_0

/-! `base64.encode_url@1.0.0`: RFC 4648 §5, URL and filename safe alphabet (Table 2), `=`
padding. -/

namespace Fvdep.Base64.EncodeUrl.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0

def encodeUrl : List UInt8 → List Char := encodeWith url

/-- §5 (§4's process over Table 2): the encoding is the bit-group description (`encodeBits`). -/
def bits : Prop := ∀ b : List UInt8, encodeUrl b = encodeBits url b

/-- Four characters per started 3-byte group. -/
def length : Prop := ∀ b : List UInt8, (encodeUrl b).length = 4 * ((b.length + 2) / 3)

end Fvdep.Base64.EncodeUrl.V1_0_0
