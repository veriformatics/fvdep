import FvdepAudit.Doc.Spec

/-! Each shipped field check decides its D2 predicate (`Rule.check r v = true ↔ ruleHolds r v`). -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepAudit.Doc.Spec

theorem digit_iff (c : Char) : c.isDigit = true ↔ Digit c := by
  simp [Char.isDigit, Digit, Char.le_def]

theorem isLowerHex_iff (c : Char) : isLowerHex c = true ↔ Digit c ∨ 'a' ≤ c ∧ c ≤ 'f' := by
  simp [isLowerHex, Digit]

theorem isDigest_iff (s : String) : isDigest s = true ↔ DigestText s := by
  simp [isDigest, DigestText, isLowerHex_iff, String.length_toList]

theorem twoDigits_eq (a b : Char) : twoDigits a b = num2 a b := rfl

theorem isUtc_iff (s : String) : isUtc s = true ↔ UtcText s := by
  unfold isUtc UtcText
  constructor
  · intro h
    split at h
    · rename_i y1 y2 y3 y4 o1 o2 d1 d2 h1 h2 m1 m2 s1 s2 heq
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      refine ⟨y1, y2, y3, y4, o1, o2, d1, d2, h1, h2, m1, m2, s1, s2, heq, ?_⟩
      obtain ⟨⟨⟨⟨⟨⟨⟨hd, ho1⟩, ho2⟩, hd1⟩, hd2⟩, hh⟩, hm⟩, hs⟩ := h
      exact ⟨fun c hc => (digit_iff c).mp (hd c hc), ho1, ho2, hd1, hd2, hh, hm, hs⟩
    · exact absurd h (by simp)
  · rintro
      ⟨y1, y2, y3, y4, o1, o2, d1, d2, h1, h2, m1, m2, s1, s2, heq, hd, ho1, ho2, hd1, hd2, hh, hm,
          hs⟩
    rw [heq]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨fun c hc => (digit_iff c).mpr (hd c hc), ho1⟩, ho2⟩, hd1⟩, hd2⟩, hh⟩, hm⟩, hs⟩

theorem isConstant_iff (s : String) : isConstant s = true ↔ ConstantText s := by
  simp only [isConstant, ConstantText, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun c hc => ⟨(h3 c hc).1, by simpa using (h3 c hc).2⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun c hc => ⟨(h3 c hc).1, by simpa using (h3 c hc).2⟩⟩

theorem isProfileId_iff (s : String) : isProfileId s = true ↔ ProfileText s := by
  simp [isProfileId, ProfileText, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower,
    Char.isDigit, Digit, Char.le_def, or_assoc, and_assoc]

theorem isArg_iff (first : Bool) (s : String) : isArg first s = true ↔ ArgText first s := by
  cases first <;> simp [isArg, ArgText, and_assoc]

theorem check_iff (r : Rule) (v : Value) : r.check v = true ↔ ruleHolds r v := by
  cases r <;> cases v <;> simp [Rule.check, ruleHolds]
  · constructor
    · intro h
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
      exact ⟨c, (Commit.toString_parse hc).symm⟩
    · rintro ⟨c, rfl⟩
      simp [Commit.parse_toString]
  · exact isDigest_iff _
  · exact isUtc_iff _
  · constructor
    · rintro ⟨h, hb⟩
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
      exact
        ⟨m, (ModuleId.toString_parse hm).symm, by
          rw [ModuleId.toString_parse hm]; exact hb⟩
    · rintro ⟨m, rfl, hb⟩
      exact ⟨by simp [ModuleId.parse_toString], hb⟩
  · constructor
    · rintro ⟨h, hb⟩
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      exact
        ⟨x, (EntryVersion.toString_parse hx).symm, by
          rw [EntryVersion.toString_parse hx]; exact hb⟩
    · rintro ⟨x, rfl, hb⟩
      exact ⟨by simp [EntryVersion.parse_toString], hb⟩
  · exact isConstant_iff _
  · exact isProfileId_iff _
  · exact isArg_iff _ _

end FvdepAudit.Doc.Proof
