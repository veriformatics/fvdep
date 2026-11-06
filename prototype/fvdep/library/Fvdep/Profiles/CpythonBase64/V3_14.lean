import Fvdep.Base64.Decode.V1_0_0
/-!
# Profile: CPython `base64` module, Python 3.14 (`b64encode`, `b64decode(s, validate=True)`)

Model of the package, checked against the real package by `fvdep profile cpython:base64 --check`
(differential = evidence that the model is faithful; the theorems below relate the model
to the contract and are kernel-checked).
Deviation from `base64.decode@1.0.0`: the unused bits of a padded final group are ignored
(`QR==` decodes like `QQ==`). `deviation_exact` states it is the only one.
-/
namespace Fvdep.Profiles.CpythonBase64.V3_14
open Fvdep.Base64 Encode.V1_0_0 Decode.V1_0_0

def encode := Encode.V1_0_0.encode

/-- `binascii.a2b_base64` last group: padding checked, unused bits ignored. -/
def finalLax (c0 c1 c2 c3 : Char) : Option (List Nat) :=
  if c3 = '=' then
    if c2 = '=' then do
      let i0 ← val c0; let i1 ← val c1
      some [i0 * 4 + i1 / 16]
    else do
      let i0 ← val c0; let i1 ← val c1; let i2 ← val c2
      let n := i0 * 4096 + i1 * 64 + i2
      some [n / 1024, n / 4 % 256]
  else quad c0 c1 c2 c3

def decode : List Char → Option (List Nat)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if rest = [] then finalLax c0 c1 c2 c3
    else do
      let q ← quad c0 c1 c2 c3
      let t ← decode rest
      some (q ++ t)
  | _ => none

/-- Zero the unused bits of a padded final group (identity elsewhere). -/
def clearGroup (c0 c1 c2 c3 : Char) : List Char :=
  if c3 = '=' then
    if c2 = '=' then [c0, (val c1).elim c1 (fun i => sym (i / 16 * 16)), c2, c3]
    else [c0, c1, (val c2).elim c2 (fun i => sym (i / 4 * 4)), c3]
  else [c0, c1, c2, c3]

def clear : List Char → List Char
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if rest = [] then clearGroup c0 c1 c2 c3 else c0 :: c1 :: c2 :: c3 :: clear rest
  | s => s

/-! ## Relation to the contract -/

theorem encode_eq_contract : encode = Encode.V1_0_0.encode := rfl

theorem clear_eq_nil (s : List Char) : clear s = [] ↔ s = [] := by
  constructor
  · intro h
    match s, h with
    | [], _ => rfl
    | [_], h | [_, _], h | [_, _, _], h => simp [clear] at h
    | c0 :: c1 :: c2 :: c3 :: rest, h =>
      unfold clear at h
      split at h
      · unfold clearGroup at h; split at h <;> (try split at h) <;> simp at h
      · simp at h
  · rintro rfl; simp [clear]

theorem finalLax_eq (c0 c1 c2 c3 : Char) :
    finalLax c0 c1 c2 c3 = Decode.V1_0_0.decode (clearGroup c0 c1 c2 c3) := by
  by_cases h3 : c3 = '=' <;> by_cases h2 : c2 = '=' <;> subst_vars
  · simp only [finalLax, clearGroup, Decode.V1_0_0.decode, final, ite_true]
    cases hv : val c1 with
    | none => simp [hv]
    | some i =>
      obtain ⟨hi, -⟩ := val_spec hv
      have : i / 16 * 16 < 64 := by omega
      cases val c0 <;> simp [Option.elim, val_sym _ this] <;> omega
  · simp only [finalLax, clearGroup, Decode.V1_0_0.decode, final, h2, ite_true, ite_false]
    cases hv : val c2 with
    | none => cases val c0 <;> cases val c1 <;> simp [hv, h2]
    | some i =>
      obtain ⟨hi, -⟩ := val_spec hv
      have : i / 4 * 4 < 64 := by omega
      have hne : sym (i / 4 * 4) ≠ '=' := sym_ne_pad _ this
      cases h0 : val c0 <;> cases h1 : val c1 <;> simp [Option.elim, val_sym _ this, hne, h0, h1]
      omega
  · simp [finalLax, clearGroup, Decode.V1_0_0.decode, final, h3]
  · simp [finalLax, clearGroup, Decode.V1_0_0.decode, final, h3]

/-- The only deviation: the package decodes exactly as the contract does after the unused
bits of the final group are zeroed. -/
theorem deviation_exact (s : List Char) : decode s = Decode.V1_0_0.decode (clear s) := by
  induction s using decode.induct with
  | case1 => rfl
  | case2 c0 c1 c2 c3 => simp only [decode, clear, ite_true]; exact finalLax_eq _ _ _ _
  | case3 c0 c1 c2 c3 rest hr ih =>
    have : clear rest ≠ [] := mt (clear_eq_nil rest).mp hr
    simp only [decode, clear, hr, ite_false, Decode.V1_0_0.decode, this, ih]
  | case4 s h1 h2 =>
    match s, h1, h2 with
    | [_], _, _ | [_, _], _, _ | [_, _, _], _, _ => simp [decode, clear, Decode.V1_0_0.decode]
    | [], h, _ => exact absurd rfl h
    | _ :: _ :: _ :: _ :: _, _, h => exact absurd rfl (h _ _ _ _ _)

theorem finalLax_of_final {c0 c1 c2 c3 : Char} {q : List Nat} (h : final c0 c1 c2 c3 = some q) :
    finalLax c0 c1 c2 c3 = some q := by
  unfold final at h; unfold finalLax
  by_cases h3 : c3 = '=' <;> by_cases h2 : c2 = '=' <;>
    cases h0 : val c0 <;> cases h1 : val c1 <;> cases hv : val c2 <;>
    simp_all <;> (try split at h) <;> simp_all

/-- Where the contract accepts, the package returns the same bytes. -/
theorem agrees (s : List Char) (bs : List Nat) (h : Decode.V1_0_0.decode s = some bs) :
    decode s = some bs := by
  induction s using decode.induct generalizing bs with
  | case1 => simpa [decode, Decode.V1_0_0.decode] using h
  | case2 c0 c1 c2 c3 =>
    simp only [Decode.V1_0_0.decode, ite_true] at h
    simp only [decode, ite_true]; exact finalLax_of_final h
  | case3 c0 c1 c2 c3 rest hr ih =>
    simp only [Decode.V1_0_0.decode, hr, ite_false, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, t, ht, h⟩ := h
    simp only [Option.some.injEq] at h; subst h
    simp [decode, hr, hq, ih t ht]
  | case4 => simp [Decode.V1_0_0.decode] at h <;> grind [Decode.V1_0_0.decode]

/-- Witness: `QR==` has unused bits set; the contract rejects it, the package accepts. -/
theorem dev_unused_bits :
    decode "QR==".toList = some [65] ∧ Decode.V1_0_0.decode "QR==".toList = none := by decide

/-- Consequence: two different strings decode to the same bytes (malleability). -/
theorem malleable : decode "QQ==".toList = decode "QR==".toList := by decide

end Fvdep.Profiles.CpythonBase64.V3_14
