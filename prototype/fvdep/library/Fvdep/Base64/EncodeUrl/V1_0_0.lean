import Fvdep.Base64.Encode.V1_0_0
/-!
# base64.encode_url 1.0.0 — RFC 4648 §5, URL-safe alphabet, padded

`base64.encode@1.0.0` with `+` → `-` and `/` → `_`.
Not modeled: unpadded base64url (JS `Buffer.toString('base64url')`, RFC 7515 JWS).
-/
namespace Fvdep.Base64.EncodeUrl.V1_0_0
open Fvdep.Base64.Encode.V1_0_0

def toUrl : Char → Char
  | '+' => '-' | '/' => '_' | c => c

def encodeUrl (bs : List Nat) : List Char := (encode bs).map toUrl
def encodeUrlStr (bs : List Nat) : String := String.ofList (encodeUrl bs)

/-! ## Obligations -/

theorem toUrl_not_std (c : Char) : toUrl c ≠ '+' ∧ toUrl c ≠ '/' := by
  unfold toUrl; split <;> simp_all

/-- Output never contains `+` or `/`, so it is safe in URLs and file names. -/
theorem encodeUrl_url_safe (bs : List Nat) : ∀ c ∈ encodeUrl bs, c ≠ '+' ∧ c ≠ '/' := by
  intro c hc
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
  exact toUrl_not_std d

/-- Output length equals that of the standard encoding. -/
theorem encodeUrl_length (bs : List Nat) : (encodeUrl bs).length = 4 * ((bs.length + 2) / 3) := by
  simp [encodeUrl, encode_length]

end Fvdep.Base64.EncodeUrl.V1_0_0
