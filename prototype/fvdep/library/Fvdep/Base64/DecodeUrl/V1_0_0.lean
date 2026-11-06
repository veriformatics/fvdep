import Fvdep.Base64.Decode.V1_0_0
import Fvdep.Base64.EncodeUrl.V1_0_0
/-!
# base64.decode_url 1.0.0 — RFC 4648 §5, URL-safe alphabet, strict

Exact inverse of `base64.encode_url@1.0.0`: rejects `+` and `/`, then decodes strictly
like `base64.decode@1.0.0` (padding mandatory, unused bits zero).
-/
namespace Fvdep.Base64.DecodeUrl.V1_0_0
open Fvdep.Base64 Encode.V1_0_0 EncodeUrl.V1_0_0

def fromUrl : Char → Char
  | '-' => '+' | '_' => '/' | c => c

def decodeUrl (s : List Char) : Option (List Nat) :=
  if s.any (fun c => c = '+' || c = '/') then none else Decode.V1_0_0.decode (s.map fromUrl)
def decodeUrlStr (s : String) : Option (List Nat) := decodeUrl s.toList

/-! ## Obligations -/

set_option maxRecDepth 8000 in
theorem sym_not_url : ∀ i, i < 64 → sym i ≠ '-' ∧ sym i ≠ '_' := by decide

theorem sym_not_url' (i : Nat) : sym i ≠ '-' ∧ sym i ≠ '_' := by
  by_cases h : i < 64
  · exact sym_not_url i h
  · have : chars[i]? = none :=
      List.getElem?_eq_none (by rw [chars_length]; omega)
    simp [sym, List.getD, this]

theorem encode_no_url (bs : List Nat) : ∀ c ∈ encode bs, c ≠ '-' ∧ c ≠ '_' := by
  induction bs using encode.induct with
  | case1 a b c rest ih =>
    simp only [encode, List.mem_cons]
    rintro x (rfl | rfl | rfl | rfl | hx)
    all_goals first | exact ih x hx | exact sym_not_url' _
  | case2 a b =>
    simp only [encode, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    all_goals first | exact sym_not_url' _ | decide
  | case3 a =>
    simp only [encode, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    all_goals first | exact sym_not_url' _ | decide
  | case4 => simp [encode]

theorem fromUrl_toUrl (c : Char) (h : c ≠ '-' ∧ c ≠ '_') : fromUrl (toUrl c) = c := by
  unfold toUrl; split <;> simp_all [fromUrl]

theorem toUrl_fromUrl (c : Char) (h : c ≠ '+' ∧ c ≠ '/') : toUrl (fromUrl c) = c := by
  unfold fromUrl; split <;> simp_all [toUrl]
/-- Round trip: decoding a URL-safe encoding returns the original bytes. -/
theorem decodeUrl_encodeUrl (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    decodeUrl (encodeUrl bs) = some bs := by
  have hany : (encodeUrl bs).any (fun c => c = '+' || c = '/') = false := by
    simp only [List.any_eq_false, encodeUrl, List.mem_map]
    rintro _ ⟨c, -, rfl⟩
    simp [toUrl_not_std c]
  have hmap : (encodeUrl bs).map fromUrl = encode bs := by
    simp only [encodeUrl, List.map_map]
    conv => rhs; rw [← List.map_id (encode bs)]
    exact List.map_congr_left (fun c hc => fromUrl_toUrl c (encode_no_url bs c hc))
  simp only [decodeUrl, hany, hmap]
  exact Decode.V1_0_0.decode_encode bs h

/-- Canonical: every accepted string is exactly the URL-safe encoding of its bytes. -/
theorem encodeUrl_decodeUrl (s : List Char) (bs : List Nat) (h : decodeUrl s = some bs) :
    encodeUrl bs = s := by
  unfold decodeUrl at h
  split at h
  · cases h
  · rename_i hany
    have := Decode.V1_0_0.encode_decode _ _ h
    simp only [encodeUrl, this, List.map_map]
    conv => rhs; rw [← List.map_id s]
    refine List.map_congr_left (fun c hc => toUrl_fromUrl c ?_)
    simp only [Bool.not_eq_true, List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq,
      not_or] at hany
    exact hany c hc

end Fvdep.Base64.DecodeUrl.V1_0_0
