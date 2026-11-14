import Conformance.Decode
import Fvdep.Abi.V1_0_0
import Fvdep.Base64.Decode.V1_0_0

/-! `Conformance.Decode.decode` = `Fvdep.Abi.V1_0_0.decoder` of `base64.decode@1.0.0` (contract U4
A8, shape `abi`). Imports the spec modules alone: the frozen closure, never the library's proof
helpers. -/

namespace Conformance.Proof.Decode

open Fvdep.Base64.Rfc4648.V1_0_0 Conformance.Decode

set_option maxRecDepth 8000 in
theorem standard_length : standard.length = 64 := by decide

set_option maxRecDepth 8000 in
theorem value_symbol : ∀ i, i < 64 → value standard (symbol standard i) = some i := by decide

theorem value_spec {c : Char} {i : Nat} (h : value standard c = some i) :
    i < 64 ∧ symbol standard i = c := by
  obtain ⟨hi, hc, -⟩ := List.idxOf?_eq_some_iff.mp h
  refine ⟨standard_length ▸ hi, ?_⟩
  simp [symbol, List.getD, hi, hc]

set_option maxRecDepth 8000 in
theorem val_symbol : ∀ i, i < 64 → val (symbol standard i) = some i := by decide

set_option maxRecDepth 8000 in
theorem symbol_upper : ∀ i, i < 26 → symbol standard i = Char.ofNat (65 + i) := by decide

set_option maxRecDepth 8000 in
theorem symbol_lower : ∀ i, i < 26 → symbol standard (26 + i) = Char.ofNat (97 + i) := by decide

set_option maxRecDepth 8000 in
theorem symbol_digit : ∀ i, i < 10 → symbol standard (52 + i) = Char.ofNat (48 + i) := by decide

theorem val_some {c : Char} {i : Nat} (h : val c = some i) : i < 64 ∧ symbol standard i = c := by
  have hc : Char.ofNat c.toNat = c := Char.ofNat_toNat c
  simp only [val] at h
  by_cases h1 : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · simp only [h1, and_self, ↓reduceIte, Option.some.injEq] at h
    subst h
    refine ⟨by omega, ?_⟩
    rw [symbol_upper _ (by omega), show 65 + (c.toNat - 65) = c.toNat by omega, hc]
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : 97 ≤ c.toNat ∧ c.toNat ≤ 122
  · simp only [h2, and_self, ↓reduceIte, Option.some.injEq] at h
    subst h
    refine ⟨by omega, ?_⟩
    rw [show c.toNat - 71 = 26 + (c.toNat - 97) by omega, symbol_lower _ (by omega),
      show 97 + (c.toNat - 97) = c.toNat by omega, hc]
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · simp only [h3, and_self, ↓reduceIte, Option.some.injEq] at h
    subst h
    refine ⟨by omega, ?_⟩
    rw [show c.toNat + 4 = 52 + (c.toNat - 48) by omega, symbol_digit _ (by omega),
      show 48 + (c.toNat - 48) = c.toNat by omega, hc]
  simp only [h3, ↓reduceIte] at h
  by_cases h4 : c.toNat = 43
  · simp only [h4, ↓reduceIte, Option.some.injEq] at h
    subst h
    rw [← hc, h4]
    decide
  simp only [h4, ↓reduceIte] at h
  by_cases h5 : c.toNat = 47
  · simp only [h5, ↓reduceIte, Option.some.injEq] at h
    subst h
    rw [← hc, h5]
    decide
  simp [h5] at h

theorem val_eq (c : Char) : val c = value standard c := by
  rcases h : val c with _ | i
  · rcases hv : value standard c with _ | j
    · rfl
    · obtain ⟨hj, rfl⟩ := value_spec hv
      rw [val_symbol j hj] at h
      cases h
  · obtain ⟨hi, rfl⟩ := val_some h
    exact (value_symbol i hi).symm

theorem value_lt {c : Char} {i : Nat} (h : value standard c = some i) : i < 64 :=
  (value_spec h).1

theorem quad_eq {c0 c1 c2 c3 : Char} {i0 i1 i2 i3 : Nat} (h0 : value standard c0 = some i0)
    (h1 : value standard c1 = some i1) (h2 : value standard c2 = some i2)
    (h3 : value standard c3 = some i3) : quad standard c0 c1 c2 c3 = some (bytes3 i0 i1 i2 i3) := by
  have b0 := value_lt h0
  have b1 := value_lt h1
  have b2 := value_lt h2
  have b3 := value_lt h3
  have e0 : (i0 * 262144 + i1 * 4096 + i2 * 64 + i3) / 65536 = i0 * 4 + i1 / 16 := by omega
  have e1 : (i0 * 262144 + i1 * 4096 + i2 * 64 + i3) / 256 % 256 = i1 % 16 * 16 + i2 / 4 := by
    omega
  have e2 : (i0 * 262144 + i1 * 4096 + i2 * 64 + i3) % 256 = i2 % 4 * 64 + i3 := by omega
  simp only [quad, h0, h1, h2, h3, Option.bind_eq_bind, Option.bind_some, e0, e1, e2, bytes3,
    Nat.toUInt8_eq]

theorem chars_eq : ∀ s : List Char, chars s = decodeWith standard s
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | c0 :: c1 :: c2 :: c3 :: rest => by
    have ih := chars_eq rest
    simp only [chars, decodeWith, val_eq, ih]
    rcases h0 : value standard c0 with _ | i0
    · by_cases hr : rest.isEmpty <;>
        simp [hr, final, quad, h0, Option.bind_eq_bind]
    rcases h1 : value standard c1 with _ | i1
    · by_cases hr : rest.isEmpty <;>
        simp [hr, final, quad, h0, h1, Option.bind_eq_bind]
    have b0 := value_lt h0
    have b1 := value_lt h1
    by_cases hr : rest.isEmpty
    · by_cases h3 : c3 = '='
      · by_cases h2 : c2 = '='
        · simp [hr, h2, h3, final, h0, h1, Option.bind_eq_bind, Nat.toUInt8_eq]
        · rcases hv2 : value standard c2 with _ | i2
          · simp [hr, h2, h3, final, h0, h1, hv2, Option.bind_eq_bind]
          · have b2 := value_lt hv2
            have e0 : (i0 * 4096 + i1 * 64 + i2) / 1024 = i0 * 4 + i1 / 16 := by omega
            have e1 : (i0 * 4096 + i1 * 64 + i2) / 4 % 256 = i1 % 16 * 16 + i2 / 4 := by omega
            simp [hr, h2, h3, final, h0, h1, hv2, Option.bind_eq_bind, Nat.toUInt8_eq, e0, e1]
      · rcases hv2 : value standard c2 with _ | i2
        · simp [hr, h3, final, quad, h0, h1, hv2, Option.bind_eq_bind]
        rcases hv3 : value standard c3 with _ | i3
        · simp [hr, h3, final, quad, h0, h1, hv2, hv3, Option.bind_eq_bind]
        simp [h3, final, quad_eq h0 h1 hv2 hv3, Option.bind_eq_bind, List.isEmpty_iff.mp hr,
          decodeWith]
    · rcases hv2 : value standard c2 with _ | i2
      · simp [hr, quad, h0, h1, hv2, Option.bind_eq_bind]
      rcases hv3 : value standard c3 with _ | i3
      · simp [hr, quad, h0, h1, hv2, hv3, Option.bind_eq_bind]
      simp [hr, quad_eq h0 h1 hv2 hv3, Option.bind_eq_bind]

/-- The `abi` statement: `@impl = Fvdep.Abi.V1_0_0.decoder @spec`. -/
theorem decode_eq :
    Conformance.Decode.decode =
      Fvdep.Abi.V1_0_0.decoder Fvdep.Base64.Decode.V1_0_0.decode := by
  funext b
  simp only [Conformance.Decode.decode, Fvdep.Abi.V1_0_0.decoder,
    Fvdep.Base64.Decode.V1_0_0.decode, chars_eq]
  cases String.fromUTF8? b <;> rfl

end Conformance.Proof.Decode
