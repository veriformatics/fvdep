import FvdepAudit.Hash.Proof.Frame
import FvdepAudit.Library.Spec
import FvdepAudit.Protocol.Proof.Val

/-! Proofs: one `ls-tree -z -l` record (contract `docs/contracts/U5b-oracle.md` L4): `parseRecord`
accepts exactly the well-formed records' layouts. -/

namespace FvdepAudit.Library.Proof

open FvdepCore.Library FvdepAudit.Library.Spec FvdepAudit.Hash.Spec

/-! ## Decimal digits as bytes -/

theorem digit_roundtrip :
    ∀ d : Fin 10, charOf (byteOf (FvdepCore.Ids.digit d.val)) = FvdepCore.Ids.digit d.val := by
  decide

theorem digit_byte : ∀ d : Fin 10, isDigitByte (byteOf (FvdepCore.Ids.digit d.val)) = true := by
  decide

theorem byte_roundtrip :
    ∀ d : Fin 10, byteOf (charOf (48 + d.val).toUInt8) = (48 + d.val).toUInt8 := by decide

theorem mem_decimal (n : Nat) :
    ∀ c ∈ FvdepCore.Ids.decimal n, ∃ d : Fin 10, c = FvdepCore.Ids.digit d.val := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold FvdepCore.Ids.decimal
    split
    · rename_i h
      intro c hc
      simp only [List.mem_singleton] at hc
      exact ⟨⟨n, h⟩, hc⟩
    · rename_i h
      intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · exact ⟨⟨n % 10, Nat.mod_lt _ (by omega)⟩, hc⟩

theorem decimal_ne_nil (n : Nat) : FvdepCore.Ids.decimal n ≠ [] := by
  unfold FvdepCore.Ids.decimal
  split <;> simp

theorem decimalBytes_eq (n : Nat) : decimalBytes n = digits n := by
  simp [decimalBytes, ascii, digits, byteOf, String.toList_ofList]

theorem charOf_digits (n : Nat) : (digits n).map charOf = FvdepCore.Ids.decimal n := by
  unfold digits
  rw [List.map_map]
  conv =>
    rhs; rw [← List.map_id (FvdepCore.Ids.decimal n)]
  apply List.map_congr_left
  intro c hc
  obtain ⟨d, rfl⟩ := mem_decimal n c hc
  exact digit_roundtrip d

theorem digits_isDigit (n : Nat) : ∀ b ∈ digits n, isDigitByte b = true := by
  intro b hb
  simp only [digits, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  obtain ⟨d, rfl⟩ := mem_decimal n c hc
  exact digit_byte d

theorem byteOf_charOf {b : UInt8} (hb : isDigitByte b = true) : byteOf (charOf b) = b := by
  simp only [isDigitByte, Bool.and_eq_true, decide_eq_true_eq] at hb
  have h1 : 48 ≤ b.toNat := by
    have := hb.1
    simp [UInt8.le_iff_toNat_le] at this
    omega
  have h2 : b.toNat ≤ 57 := by
    have := hb.2
    simp [UInt8.le_iff_toNat_le] at this
    omega
  have hd := byte_roundtrip ⟨b.toNat - 48, by omega⟩
  have hb' : (48 + (b.toNat - 48)).toUInt8 = b := by
    rw [show 48 + (b.toNat - 48) = b.toNat by omega]
    exact UInt8.ofNat_toNat
  simp only [hb'] at hd
  exact hd

theorem digits_of_bytes {t : List UInt8} (ht : ∀ b ∈ t, isDigitByte b = true) :
    (t.map charOf).map byteOf = t := by
  rw [List.map_map]
  conv =>
    rhs; rw [← List.map_id t]
  apply List.map_congr_left
  intro b hb
  exact byteOf_charOf (ht b hb)

/-! ## The fields -/

/-- A size column's text (the spec's `sizeColumn` before padding). -/
def sizeText : Option Nat → List UInt8
  | some n => decimalBytes n
  | none => ascii "-"

theorem sizeColumn_eq (s : Option Nat) : sizeColumn s = pad7 (sizeText s) := by cases s <;> rfl

theorem ascii_names :
    ascii "blob" = [98, 108, 111, 98] ∧
      ascii "tree" = [116, 114, 101, 101] ∧
      ascii "commit" = [99, 111, 109, 109, 105, 116] ∧
      ascii "-" = [45] ∧ ascii " blob " = [32, 98, 108, 111, 98, 32] := by
  decide

theorem kindOf_layout (k : ObjKind) (rest : List UInt8) :
    kindOf (kindName k ++ 32 :: rest) = some (k, rest) := by
  cases k <;> simp [kindName, ascii_names, kindOf]

theorem kindOf_some {rest rest' : List UInt8} {k : ObjKind} (h : kindOf rest = some (k, rest')) :
    rest = kindName k ++ 32 :: rest' := by
  unfold kindOf at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    simp [kindName, ascii_names]

theorem sizeField_layout (k : ObjKind) (s : Option Nat) (hk : k = .blob ↔ s.isSome) :
    sizeField k (sizeText s) = some s := by
  cases k with
  | blob =>
    cases s with
    | none => simp at hk
    | some n =>
      have hd := digits_isDigit n
      simp only [sizeField, sizeText, decimalBytes_eq]
      simp [List.all_eq_true.2 hd, charOf_digits, FvdepCore.Ids.parseNat_decimal]
  | tree
  | commit =>
    cases s with
    | none => simp [sizeField, sizeText, ascii_names]
    | some n => simp at hk

theorem sizeField_some {k : ObjKind} {t : List UInt8} {s : Option Nat}
    (h : sizeField k t = some s) : t = sizeText s ∧ (k = .blob ↔ s.isSome) := by
  cases k with
  | blob =>
    simp only [sizeField] at h
    split at h
    · rename_i ht
      rw [List.all_eq_true] at ht
      cases hp : FvdepCore.Ids.parseNat (t.map charOf) with
      | none => simp [hp] at h
      | some n =>
        simp only [hp, Option.map_some, Option.some.injEq] at h
        subst h
        have hd := FvdepAudit.Protocol.Proof.decimal_of_parseNat hp
        refine ⟨?_, by simp⟩
        simp only [sizeText, decimalBytes_eq, digits, hd]
        exact (digits_of_bytes ht).symm
    · cases h
  | tree
  | commit =>
    simp only [sizeField] at h
    split at h
    · rename_i ht
      simp only [Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at ht
      exact ⟨by simp [sizeText, ascii_names, ht], by simp⟩
    · cases h

theorem sizeText_ne (s : Option Nat) : ∃ x xs, sizeText s = x :: xs ∧ x ≠ 32 ∧ x ≠ 9 := by
  cases s with
  | none => exact ⟨45, [], by simp [sizeText, ascii_names], by decide, by decide⟩
  | some n =>
    cases hd : digits n with
    | nil =>
      have : FvdepCore.Ids.decimal n = [] := by simpa [digits] using hd
      exact absurd this (decimal_ne_nil n)
    | cons x xs =>
      have hx := digits_isDigit n x (by simp [hd])
      simp only [isDigitByte, Bool.and_eq_true, decide_eq_true_eq] at hx
      refine ⟨x, xs, by simp [sizeText, decimalBytes_eq, hd], ?_, ?_⟩
      · intro e
        rw [e] at hx
        exact absurd hx.1 (by decide)
      · intro e
        rw [e] at hx
        exact absurd hx.1 (by decide)

theorem sizeText_no_tab (s : Option Nat) : ∀ b ∈ sizeText s, b ≠ 9 := by
  cases s with
  | none => simp [sizeText, ascii_names]
  | some n =>
    intro b hb
    rw [sizeText, decimalBytes_eq] at hb
    have := digits_isDigit n b hb
    simp only [isDigitByte, Bool.and_eq_true, decide_eq_true_eq] at this
    intro e
    rw [e] at this
    exact absurd this.1 (by decide)

theorem dropSpaces (k : Nat) (t : List UInt8) (ht : ∀ x xs, t = x :: xs → x ≠ 32) :
    (List.replicate k 32 ++ t).dropWhile (· == 32) = t := by
  induction k with
  | zero =>
    cases t with
    | nil => rfl
    | cons x xs =>
      have := ht x xs rfl
      simp [this]
  | succ k ih => simpa [List.replicate_succ, List.dropWhile] using ih

/-! ## The record -/

theorem octal_all {m : List UInt8} (h : ∀ b ∈ m, 48 ≤ b ∧ b ≤ 55) : m.all isOctal = true :=
  List.all_eq_true.2 fun b hb => by simpa [isOctal] using h b hb

theorem hex_all {m : List UInt8} (h : ∀ b ∈ m, 48 ≤ b ∧ b ≤ 57 ∨ 97 ≤ b ∧ b ≤ 102) :
    m.all isHexByte = true := List.all_eq_true.2 fun b hb => by simpa [isHexByte] using h b hb

theorem pad_no_tab (s : Option Nat) : ∀ b ∈ pad7 (sizeText s), (b != 9) = true := by
  intro b hb
  simp only [pad7, List.mem_append, List.mem_replicate] at hb
  rcases hb with ⟨-, rfl⟩ | hb
  · decide
  · simpa using sizeText_no_tab s b hb

theorem pad_text (s : Option Nat) : (pad7 (sizeText s)).dropWhile (· == 32) = sizeText s := by
  obtain ⟨x, xs, htx, hx32, -⟩ := sizeText_ne s
  unfold pad7
  apply dropSpaces
  intro y ys hy
  rw [htx] at hy
  simp only [List.cons.injEq] at hy
  rw [← hy.1]
  exact hx32

theorem parseRecord_layout (e : TreeEntry) (hw : EntryWF e) :
    parseRecord (recordLayout e) = some e := by
  obtain ⟨hm, hmo, ho, hoh, hk, hp, hp0⟩ := hw
  rcases e with ⟨mode, kind, oid, size, path⟩
  simp only at hm hmo ho hoh hk hp hp0
  have hr :
    recordLayout ⟨mode, kind, oid, size, path⟩ =
      mode ++
        32 :: (kindName kind ++ 32 :: (oid ++ 32 :: (pad7 (sizeText size) ++ 9 :: utf8 path))) := by
    simp [recordLayout, sizeColumn_eq]
  rw [hr]
  have h9 : ((9 : UInt8) != 9) = false := by decide
  unfold parseRecord
  simp only [List.take_left' hm, List.drop_left' hm, hm, octal_all hmo, beq_self_eq_true,
    Bool.and_self, ↓reduceIte, kindOf_layout, List.take_left' ho, List.drop_left' ho, ho,
    hex_all hoh, List.takeWhile_append_of_pos (pad_no_tab size),
    List.dropWhile_append_of_pos (pad_no_tab size), pad_text, sizeField_layout kind size hk,
    FvdepAudit.Hash.Proof.text_utf8, List.takeWhile_cons, List.dropWhile_cons, h9, List.append_nil,
    Bool.false_eq_true]
  have hpb : (utf8 path != []) = true := by simpa using hp
  simp [hpb, hp0]

theorem parseRecord_some {r : List UInt8} {e : TreeEntry} (h : parseRecord r = some e) :
    r = recordLayout e ∧ EntryWF e := by
  unfold parseRecord at h
  simp only at h
  split at h
  next h1 =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
    obtain ⟨hm, hmo⟩ := h1
    split at h
    next rest hrest =>
      split at h
      next kind rest' hk =>
        split at h
        next h2 =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
          obtain ⟨ho, hoh⟩ := h2
          split at h
          next rest'' hrest'' =>
            split at h
            next path hpath =>
              split at h
              next h3 =>
                simp only [beq_iff_eq] at h3
                split at h
                next size p hs hp =>
                  split at h
                  next h4 =>
                    simp only [Option.some.injEq] at h
                    subst h
                    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h4
                    obtain ⟨htext, hks⟩ := sizeField_some hs
                    have hu := FvdepAudit.Hash.Proof.text_some hp
                    have hsplit :=
                      List.takeWhile_append_dropWhile (p := fun b : UInt8 => b != 9) (l := rest'')
                    rw [hpath, ← h3, htext] at hsplit
                    have hr1 := List.take_append_drop 6 r
                    rw [hrest, kindOf_some hk] at hr1
                    have hr2 := List.take_append_drop 40 rest'
                    rw [hrest''] at hr2
                    generalize List.take 6 r = mode at hr1 hm hmo ⊢
                    generalize List.take 40 rest' = oid at hr2 ho hoh ⊢
                    refine ⟨?_, ?_⟩
                    · rw [← hr1, ← hr2, ← hsplit, ← hu]
                      simp [recordLayout, sizeColumn_eq]
                    · refine ⟨hm, fun b hb => ?_, ho, fun b hb => ?_, hks, ?_, ?_⟩
                      · have := hmo b hb
                        simpa [isOctal] using this
                      · have := hoh b hb
                        simpa [isHexByte] using this
                      · rw [hu]
                        exact h4.1
                      · rw [hu]
                        simpa using h4.2
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- L4: one record = exactly a well-formed entry's layout. -/
theorem parseRecord_exact (r : List UInt8) (e : TreeEntry) :
    parseRecord r = some e ↔ r = recordLayout e ∧ EntryWF e :=
  ⟨parseRecord_some, fun ⟨hr, hw⟩ => hr ▸ parseRecord_layout e hw⟩

end FvdepAudit.Library.Proof
