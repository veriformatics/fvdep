import Fvdep.Base64.Encode.V1_0_0
/-!
# base64.decode 1.0.0 — RFC 4648 §4, standard alphabet, strict

Strict decoding: alphabet chars only, padding mandatory, unused trailing bits zero.
Strictness makes the encoding canonical ⇒ the decoder is the exact inverse of
`base64.encode@1.0.0`: every accepted string is the encoding of what it decodes to
(`encode_decode`). Permissive decoders break this (malleability: several strings → same bytes).
-/
namespace Fvdep.Base64.Decode.V1_0_0
open Fvdep.Base64.Encode.V1_0_0

/-- Four alphabet chars → three bytes. -/
def quad (c0 c1 c2 c3 : Char) : Option (List Nat) := do
  let i0 ← val c0; let i1 ← val c1; let i2 ← val c2; let i3 ← val c3
  let n := i0 * 262144 + i1 * 4096 + i2 * 64 + i3
  some [n / 65536, n / 256 % 256, n % 256]

/-- Last group: padding allowed; unused bits must be zero. -/
def final (c0 c1 c2 c3 : Char) : Option (List Nat) :=
  if c3 = '=' then
    if c2 = '=' then do
      let i0 ← val c0; let i1 ← val c1
      if i1 % 16 = 0 then some [i0 * 4 + i1 / 16] else none
    else do
      let i0 ← val c0; let i1 ← val c1; let i2 ← val c2
      if i2 % 4 = 0 then
        let n := i0 * 4096 + i1 * 64 + i2
        some [n / 1024, n / 4 % 256]
      else none
  else quad c0 c1 c2 c3

def decode : List Char → Option (List Nat)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if rest = [] then final c0 c1 c2 c3
    else do
      let q ← quad c0 c1 c2 c3
      let t ← decode rest
      some (q ++ t)
  | _ => none

/-- String entry point (what adapters and the oracle call). -/
def decodeStr (s : String) : Option (List Nat) := decode s.toList

/-! ## Obligations -/

/-- Round trip: decoding an encoding returns the original bytes. -/
theorem decode_encode (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    decode (encode bs) = some bs := by
  induction bs using encode.induct with
  | case1 a b c rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨ha, hb, hc, hr⟩ := h
    generalize hn : a * 65536 + b * 256 + c = n
    have h0 : n / 262144 < 64 := by omega
    have h1 : n / 4096 % 64 < 64 := by omega
    have h2 : n / 64 % 64 < 64 := by omega
    have h3 : n % 64 < 64 := by omega
    have hq : quad (sym (n / 262144)) (sym (n / 4096 % 64)) (sym (n / 64 % 64)) (sym (n % 64))
        = some [a, b, c] := by
      simp only [quad, val_sym _ h0, val_sym _ h1, val_sym _ h2, val_sym _ h3,
        Option.bind_eq_bind, Option.bind_some, Option.some.injEq, List.cons.injEq, and_true]
      omega
    simp only [encode, hn, decode]
    by_cases hrest : rest = []
    · subst hrest
      simp [encode, final, sym_ne_pad _ h3, hq]
    · have := mt encode_eq_nil.mp hrest
      simp [this, hq, ih hr]
  | case2 a b =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil] at h
    obtain ⟨ha, hb, -⟩ := h
    generalize hn : a * 65536 + b * 256 = n
    have h0 : n / 262144 < 64 := by omega
    have h1 : n / 4096 % 64 < 64 := by omega
    have h2 : n / 64 % 64 < 64 := by omega
    simp only [encode, hn, decode, final, sym_ne_pad _ h2, val_sym _ h0, val_sym _ h1,
      val_sym _ h2, ite_true, ite_false, Option.bind_eq_bind, Option.bind_some]
    have hm : n / 64 % 64 % 4 = 0 := by omega
    simp only [hm, ite_true, Option.some.injEq, List.cons.injEq, and_true]
    omega
  | case3 a =>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil] at h
    obtain ⟨ha, -⟩ := h
    generalize hn : a * 65536 = n
    have h0 : n / 262144 < 64 := by omega
    have h1 : n / 4096 % 64 < 64 := by omega
    simp only [encode, hn, decode, final, val_sym _ h0, val_sym _ h1,
      ite_true, Option.bind_eq_bind, Option.bind_some]
    have hm : n / 4096 % 64 % 16 = 0 := by omega
    simp only [hm, ite_true, Option.some.injEq, List.cons.injEq, and_true]
    omega
  | case4 => rfl


theorem quad_spec {c0 c1 c2 c3 : Char} {q : List Nat} (h : quad c0 c1 c2 c3 = some q)
    (t : List Nat) : encode (q ++ t) = c0 :: c1 :: c2 :: c3 :: encode t := by
  simp only [quad, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨i0, h0, i1, h1, i2, h2, i3, h3, rfl⟩ := h
  obtain ⟨l0, rfl⟩ := val_spec h0; obtain ⟨l1, rfl⟩ := val_spec h1
  obtain ⟨l2, rfl⟩ := val_spec h2; obtain ⟨l3, rfl⟩ := val_spec h3
  simp only [List.cons_append, List.nil_append, encode, List.cons.injEq, and_true]
  refine ⟨congrArg sym ?_, congrArg sym ?_, congrArg sym ?_, congrArg sym ?_⟩ <;> omega

theorem final_spec {c0 c1 c2 c3 : Char} {q : List Nat} (h : final c0 c1 c2 c3 = some q) :
    encode q = [c0, c1, c2, c3] := by
  unfold final at h
  split at h
  · subst_vars
    split at h
    · subst_vars
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i0, h0, i1, h1, h⟩ := h
      split at h
      · cases h
        obtain ⟨l0, rfl⟩ := val_spec h0; obtain ⟨l1, rfl⟩ := val_spec h1
        simp only [encode, List.cons.injEq, and_true]
        refine ⟨congrArg sym ?_, congrArg sym ?_⟩ <;> omega
      · cases h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i0, h0, i1, h1, i2, h2, h⟩ := h
      split at h
      · cases h
        obtain ⟨l0, rfl⟩ := val_spec h0; obtain ⟨l1, rfl⟩ := val_spec h1
        obtain ⟨l2, rfl⟩ := val_spec h2
        simp only [encode, List.cons.injEq, and_true]
        refine ⟨congrArg sym ?_, congrArg sym ?_, congrArg sym ?_⟩ <;> omega
      · cases h
  · simpa [encode] using quad_spec h []

/-- Canonical (anti-malleability): every accepted string is exactly the encoding of
its decoded bytes ⇒ distinct accepted strings never decode to the same bytes. -/
theorem encode_decode (s : List Char) (bs : List Nat) (h : decode s = some bs) :
    encode bs = s := by
  induction s using decode.induct generalizing bs with
  | case1 => simp [decode] at h; subst h; rfl
  | case2 c0 c1 c2 c3 =>
    simp only [decode, ite_true] at h; exact final_spec h
  | case3 c0 c1 c2 c3 rest hr ih =>
    simp only [decode, hr, ite_false, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨q, hq, t, ht, rfl⟩ := h
    rw [quad_spec hq, ih t ht]
  | case4 => simp [decode] at h

theorem decode_injective (s₁ s₂ : List Char) (bs : List Nat)
    (h₁ : decode s₁ = some bs) (h₂ : decode s₂ = some bs) : s₁ = s₂ := by
  rw [← encode_decode s₁ bs h₁, ← encode_decode s₂ bs h₂]

end Fvdep.Base64.Decode.V1_0_0
