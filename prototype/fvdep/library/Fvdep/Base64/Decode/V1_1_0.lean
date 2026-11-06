import Fvdep.Base64.Decode.V1_0_0
/-!
# base64.decode 1.1.0 — same behaviour as 1.0.0, one more obligation

Update without a behaviour change: `decode` is unchanged (`unchanged`, by `rfl`), so every proof of an
implementation against 1.0.0 carries over. Added obligation: `decode_length`.
-/
namespace Fvdep.Base64.Decode.V1_1_0
open Fvdep.Base64

def decode := Decode.V1_0_0.decode
def decodeStr (s : String) : Option (List Nat) := decode s.toList

/-! ## Obligations -/

theorem unchanged : decode = Decode.V1_0_0.decode := rfl

/-- An accepted string has exactly 4 chars per started 3-byte group of its output. -/
theorem decode_length (s : List Char) (bs : List Nat) (h : decode s = some bs) :
    s.length = 4 * ((bs.length + 2) / 3) := by
  rw [← Decode.V1_0_0.encode_decode s bs h, Encode.V1_0_0.encode_length]

end Fvdep.Base64.Decode.V1_1_0
