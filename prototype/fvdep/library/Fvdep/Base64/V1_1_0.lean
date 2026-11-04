import Fvdep.Base64.V1_0_0
/-!
# base64 spec v1.1.0 — adds RFC 4648 §5 URL-safe alphabet

Minor bump: v1.0.0 surface unchanged (`std_unchanged` obligations), `encodeUrl`/`decodeUrl`
added with the same round-trip + canonical obligations.
Models: Python `base64.urlsafe_b64encode` (padded). Not modeled: unpadded base64url
(JS `Buffer.toString('base64url')`, RFC 7515 JWS).
-/
namespace Fvdep.Base64.V1_1_0
open Fvdep.Base64

def encode := V1_0_0.encode
def decode := V1_0_0.decode

def toUrl : Char → Char
  | '+' => '-' | '/' => '_' | c => c
def fromUrl : Char → Char
  | '-' => '+' | '_' => '/' | c => c

def encodeUrl (bs : List Nat) : List Char := (encode bs).map toUrl
def decodeUrl (s : List Char) : Option (List Nat) :=
  if s.any (fun c => c = '+' || c = '/') then none else decode (s.map fromUrl)

def encodeStr (bs : List Nat) : String := String.ofList (encode bs)
def decodeStr (s : String) : Option (List Nat) := decode s.toList
def encodeUrlStr (bs : List Nat) : String := String.ofList (encodeUrl bs)
def decodeUrlStr (s : String) : Option (List Nat) := decodeUrl s.toList

/-! ## Obligations -/

theorem std_unchanged_encode : encode = V1_0_0.encode := rfl
theorem std_unchanged_decode : decode = V1_0_0.decode := rfl

set_option maxRecDepth 8000 in
theorem sym_not_url : ∀ i, i < 64 → V1_0_0.sym i ≠ '-' ∧ V1_0_0.sym i ≠ '_' := by decide

theorem sym_not_url' (i : Nat) : V1_0_0.sym i ≠ '-' ∧ V1_0_0.sym i ≠ '_' := by
  by_cases h : i < 64
  · exact sym_not_url i h
  · have : V1_0_0.chars[i]? = none :=
      List.getElem?_eq_none (by rw [V1_0_0.chars_length]; omega)
    simp [V1_0_0.sym, List.getD, this]

theorem encode_no_url (bs : List Nat) : ∀ c ∈ V1_0_0.encode bs, c ≠ '-' ∧ c ≠ '_' := by
  induction bs using V1_0_0.encode.induct with
  | case1 a b c rest ih =>
    simp only [V1_0_0.encode, List.mem_cons]
    rintro x (rfl | rfl | rfl | rfl | hx)
    all_goals first | exact ih x hx | exact sym_not_url' _
  | case2 a b =>
    simp only [V1_0_0.encode, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    all_goals first | exact sym_not_url' _ | decide
  | case3 a =>
    simp only [V1_0_0.encode, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    all_goals first | exact sym_not_url' _ | decide
  | case4 => simp [V1_0_0.encode]

theorem fromUrl_toUrl (c : Char) (h : c ≠ '-' ∧ c ≠ '_') : fromUrl (toUrl c) = c := by
  unfold toUrl; split <;> simp_all [fromUrl]

theorem toUrl_fromUrl (c : Char) (h : c ≠ '+' ∧ c ≠ '/') : toUrl (fromUrl c) = c := by
  unfold fromUrl; split <;> simp_all [toUrl]

theorem toUrl_not_std (c : Char) : toUrl c ≠ '+' ∧ toUrl c ≠ '/' := by
  unfold toUrl; split <;> simp_all

theorem decodeUrl_encodeUrl (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    decodeUrl (encodeUrl bs) = some bs := by
  have hany : (encodeUrl bs).any (fun c => c = '+' || c = '/') = false := by
    simp only [List.any_eq_false, encodeUrl, List.mem_map]
    rintro _ ⟨c, -, rfl⟩
    simp [toUrl_not_std c]
  have hmap : (encodeUrl bs).map fromUrl = V1_0_0.encode bs := by
    simp only [encodeUrl, encode, List.map_map]
    conv => rhs; rw [← List.map_id (V1_0_0.encode bs)]
    exact List.map_congr_left (fun c hc => fromUrl_toUrl c (encode_no_url bs c hc))
  simp only [decodeUrl, hany, decode, hmap]
  exact V1_0_0.decode_encode bs h

theorem encodeUrl_decodeUrl (s : List Char) (bs : List Nat) (h : decodeUrl s = some bs) :
    encodeUrl bs = s := by
  unfold decodeUrl at h
  split at h
  · cases h
  · rename_i hany
    have := V1_0_0.encode_decode _ _ h
    simp only [encodeUrl, encode, this, List.map_map]
    conv => rhs; rw [← List.map_id s]
    refine List.map_congr_left (fun c hc => toUrl_fromUrl c ?_)
    simp only [Bool.not_eq_true, List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq,
      not_or] at hany
    exact hany c hc

end Fvdep.Base64.V1_1_0
