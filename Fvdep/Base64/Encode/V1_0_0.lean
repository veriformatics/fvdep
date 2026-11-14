import Fvdep.Base64.Rfc4648.V1_0_0

/-! `base64.encode@1.0.0`: RFC 4648 §4, standard alphabet (Table 1), `=` padding. -/

namespace Fvdep.Base64.Encode.V1_0_0

open Fvdep.Base64.Rfc4648.V1_0_0

def encode : List UInt8 → List Char := encodeWith standard

/-- §4: the encoding is the bit-group description (`encodeBits`). -/
def bits : Prop := ∀ b : List UInt8, encode b = encodeBits standard b

/-- §4: four characters per started 3-byte group. -/
def length : Prop := ∀ b : List UInt8, (encode b).length = 4 * ((b.length + 2) / 3)

end Fvdep.Base64.Encode.V1_0_0
