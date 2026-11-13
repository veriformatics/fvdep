import FvdepAudit.Manifest.Spec

/-! T5 `Utf8Offset` + `TextStage`: the scan stops at the end of the longest valid UTF-8 prefix; the
text stage = T1's order. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Manifest FvdepAudit.Manifest.Spec

theorem hasBom_iff (b : ByteArray) : hasBom b = true ↔ Bom b := by
  simp only [hasBom, Bom, beq_iff_eq, Array.toList_extract, List.extract, List.drop_zero,
    Nat.sub_zero]

theorem extract_of_size_le {b : ByteArray} {k : Nat} (h : b.size ≤ k) : b.extract 0 k = b := by
  ext1
  simp only [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le h

theorem validUtf8_iff (b : ByteArray) : ValidUtf8 b ↔ b.IsValidUTF8 := by
  unfold ValidUtf8 String.fromUTF8?
  split <;> simp_all

/-- The bytes from `i` on are valid UTF-8 exactly when the scan from `i` finds no failure. -/
theorem scan_none_iff (b : ByteArray) (i : Nat) :
    i ≤ b.size → (scanUtf8 b i = none ↔ (b.extract i b.size).IsValidUTF8) := by
  fun_induction scanUtf8 b i with
  | case1 i h c h₂ ih =>
    intro _
    rw [ih (ByteArray.le_size_of_utf8DecodeChar?_eq_some h₂)]
    have h₂' := h₂
    rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂'
    obtain ⟨l, hl⟩ := ByteArray.exists_of_utf8DecodeChar?_eq_some h₂'
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega)
        (ByteArray.le_size_of_utf8DecodeChar?_eq_some h₂)] at hl ⊢
    rw [ByteArray.append_inj_left hl
        (by
          have := ByteArray.le_size_of_utf8DecodeChar?_eq_some h₂; simp; omega),
      ← List.utf8Encode_singleton, ByteArray.isValidUTF8_utf8Encode_singleton_append_iff]
  | case2 i h h₂ =>
    intro _
    simp only [reduceCtorEq, false_iff]
    rintro ⟨l, hl⟩
    have : l ≠ [] := by
      rintro rfl
      simp at hl
      omega
    rw [← l.cons_head_tail this] at hl
    rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract, hl,
      List.utf8DecodeChar?_utf8Encode_cons] at h₂
    simp at h₂
  | case3 i h =>
    intro hi
    have : i = b.size := by omega
    subst this
    simp

/-- A failing scan from `i` stops at `k`: the bytes from `i` to `k` are valid UTF-8 + no character
decodes at `k`. -/
theorem scan_some (b : ByteArray) (i : Nat) :
    ∀ k,
      scanUtf8 b i = some k →
        i ≤ k ∧ k < b.size ∧ (b.extract i k).IsValidUTF8 ∧ b.utf8DecodeChar? k = none := by
  fun_induction scanUtf8 b i with
  | case1 i h c h₂ ih =>
    intro k hk
    obtain ⟨hk1, hk2, hk3, hk4⟩ := ih k hk
    have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some h₂
    refine ⟨by omega, hk2, ?_, hk4⟩
    have h₂' := h₂
    rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂'
    obtain ⟨l, hl⟩ := ByteArray.exists_of_utf8DecodeChar?_eq_some h₂'
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega) hle] at hl
    have hc :=
      ByteArray.append_inj_left hl
        (by
          simp; omega)
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega) (by omega),
      hc, ← List.utf8Encode_singleton, ByteArray.isValidUTF8_utf8Encode_singleton_append_iff]
    exact hk3
  | case2 i h h₂ =>
    intro k hk
    simp only [Option.some.injEq] at hk
    subst hk
    exact ⟨Nat.le_refl _, h, by simp, h₂⟩
  | case3 i h => simp

/-- No valid prefix ends beyond a failure point `k` that follows a valid prefix. -/
theorem no_longer_prefix {b : ByteArray} {k : Nat} (hk : (b.extract 0 k).IsValidUTF8)
    (hd : b.utf8DecodeChar? k = none) {j : Nat} (hkj : k < j) (hj : j ≤ b.size) :
    ¬(b.extract 0 j).IsValidUTF8 := by
  rintro ⟨cs, hcs⟩
  obtain ⟨ds, hds⟩ := hk
  have hsplit : b.extract 0 j = b.extract 0 k ++ b.extract k j :=
    ByteArray.extract_eq_extract_append_extract k (by omega) (by omega)
  rw [hsplit, hds] at hcs
  obtain ⟨rest, rfl⟩ := List.isPrefix_of_utf8Encode_append_eq_utf8Encode _ hcs
  rw [List.utf8Encode_append] at hcs
  have hrest : b.extract k j = rest.utf8Encode := ByteArray.append_right_inj _ |>.mp hcs
  have hne : rest ≠ [] := by
    rintro rfl
    have : (b.extract k j).size = 0 := by
      rw [hrest]; simp
    simp at this
    omega
  rw [← rest.cons_head_tail hne] at hrest
  have hdec : (b.extract k j).utf8DecodeChar? 0 = some (rest.head hne) := by
    rw [hrest, List.utf8DecodeChar?_utf8Encode_cons]
  have hsplit2 : b.extract k b.size = b.extract k j ++ b.extract j b.size :=
    ByteArray.extract_eq_extract_append_extract j (by omega) hj
  have := ByteArray.utf8DecodeChar?_append_eq_some (b' := b.extract j b.size) hdec
  rw [← hsplit2, ← ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract, hd] at this
  cases this

/-- T5 `Utf8Offset`. -/
theorem utf8Offset (b : ByteArray) :
    (utf8ErrorOffset b = none ↔ ValidUtf8 b) ∧
      ∀ k,
        utf8ErrorOffset b = some k ↔
          ¬ValidUtf8 b ∧
            ValidUtf8 (b.extract 0 k) ∧ ∀ j, k < j → j ≤ b.size → ¬ValidUtf8 (b.extract 0 j) := by
  have hnone : utf8ErrorOffset b = none ↔ ValidUtf8 b := by
    rw [validUtf8_iff, utf8ErrorOffset, scan_none_iff b 0 (Nat.zero_le _),
      ByteArray.extract_zero_size]
  refine ⟨hnone, fun k => ⟨fun h => ?_, fun ⟨hinv, hval, hlong⟩ => ?_⟩⟩
  · obtain ⟨_, hks, hv, hd⟩ := scan_some b 0 k h
    refine
      ⟨(fun hb => by
          rw [← hnone, h] at hb; cases hb),
        (validUtf8_iff _).mpr hv, ?_⟩
    intro j hkj hj hvj
    exact no_longer_prefix hv hd hkj hj ((validUtf8_iff _).mp hvj)
  · cases h : utf8ErrorOffset b with
    | none => exact absurd (hnone.mp h) hinv
    | some k' =>
      obtain ⟨_, hk's, hv', hd'⟩ := scan_some b 0 k' h
      have hks : k ≤ b.size := by
        apply Classical.byContradiction
        intro hgt
        apply hinv
        rw [← extract_of_size_le (Nat.le_of_lt (Nat.lt_of_not_le hgt))]
        exact hval
      rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
      · exact absurd ((validUtf8_iff _).mpr hv') (hlong k' hlt (Nat.le_of_lt hk's))
      · simp [heq]
      · exact absurd ((validUtf8_iff _).mp hval) (no_longer_prefix hv' hd' hgt hks)

/-- T5 `TextStage`. -/
theorem textStage_spec (b : ByteArray) : TextSpec b (textStage b) := by
  unfold TextSpec textStage
  by_cases hs : 65536 < b.size
  · simp [hs, maxBytes]
  · have hs' : ¬maxBytes < b.size := hs
    simp only [hs, hs', ite_false]
    have hbom := hasBom_iff b
    by_cases hb : Bom b
    · simp [hb, hbom.mpr hb]
    · have hb' : hasBom b = false := Bool.eq_false_iff.mpr fun h => hb (hbom.mp h)
      simp only [hb, hb', Bool.false_eq_true, ite_false]
      cases hu : utf8ErrorOffset b with
      | some k =>
        have hinv := ((utf8Offset b).2 k).mp hu |>.1
        have : String.fromUTF8? b = none := by
          cases hf : String.fromUTF8? b with
          | none => rfl
          | some s => exact absurd (by simp [ValidUtf8, hf]) hinv
        simp [this]
      | none =>
        have hv := (validUtf8_iff b).mp ((utf8Offset b).1.mp hu)
        refine ⟨String.fromUTF8 b hv, ?_, rfl⟩
        simp [String.fromUTF8?, hv]

end FvdepAudit.Manifest.Proof
