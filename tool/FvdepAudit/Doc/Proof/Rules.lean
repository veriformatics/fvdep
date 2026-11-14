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

theorem isText_iff (cap : Nat) (s : String) : isText cap s = true ↔ TextFits cap s := by
  simp [isText, TextFits, isControl, Control, and_assoc]

theorem ascendingStrs_iff : ∀ ns : List String, ascendingStrs ns = true ↔ Ascends ns
  | [] => by simp [ascendingStrs, Ascends]
  | [_] => by simp [ascendingStrs, Ascends]
  | a :: b :: rest => by simp [ascendingStrs, Ascends, ascendingStrs_iff (b :: rest)]

theorem statusAxiomsOk_iff (st : String) (ns : List String) :
    statusAxiomsOk st ns = true ↔ StatusAxioms st ns := by
  unfold statusAxiomsOk StatusAxioms
  split <;> simp_all [List.isEmpty_iff]

theorem strsOf_map : ∀ ns : List String, strsOf (ns.map .str) = some ns
  | [] => rfl
  | n :: ns => by simp [strsOf, strsOf_map ns]

theorem strsOf_some : ∀ {xs : List Value} {ns : List String}, strsOf xs = some ns → xs = ns.map .str
  | [], ns, h => by
    simp only [strsOf, Option.some.injEq] at h
    subst h
    rfl
  | .str s :: xs, ns, h => by
    simp only [strsOf, Option.map_eq_some_iff] at h
    obtain ⟨ns', h', rfl⟩ := h
    simp [strsOf_some h']
  | .null :: _, _, h | .bool _ :: _, _, h | .int _ :: _, _, h | .arr _ :: _, _, h | .obj _ :: _, _,
    h => by simp [strsOf] at h

theorem compatOk_iff (ms : List (String × Value)) :
    compatOk ms = true ↔
      ∃ (st : String) (ns : List String) (x : EntryVersion),
        ms = [("axioms", .arr (ns.map .str)), ("status", .str st), ("version", .str (toString x))] ∧
          (∀ n ∈ ns, TextFits 1024 n) ∧
          Ascends ns ∧ StatusAxioms st ns ∧ SpellingFits (toString x) := by
  constructor
  · intro h
    unfold compatOk at h
    split at h
    · rename_i axs st ver
      cases hs : strsOf axs with
      | none => simp [hs] at h
      | some ns =>
        simp only [hs, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h4
        refine
          ⟨st, ns, x, ?_, fun n hn => (isText_iff 1024 n).mp (h1 n hn),
            (ascendingStrs_iff ns).mp h2, (statusAxiomsOk_iff st ns).mp h3, ?_⟩
        · rw [strsOf_some hs, EntryVersion.toString_parse hx]
        · unfold SpellingFits
          rw [EntryVersion.toString_parse hx]
          exact h5
    · simp at h
  · rintro ⟨st, ns, x, rfl, h1, h2, h3, h4⟩
    simp only [compatOk, strsOf_map, EntryVersion.parse_toString, Option.isSome_some,
      Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact
      ⟨⟨⟨⟨fun n hn => (isText_iff 1024 n).mpr (h1 n hn), (ascendingStrs_iff ns).mpr h2⟩,
            (statusAxiomsOk_iff st ns).mpr h3⟩,
          trivial⟩,
        h4⟩

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
  · exact isText_iff _ _
  · exact isText_iff _ _
  · constructor
    · rintro ⟨h, hb⟩
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      exact
        ⟨x, (EntryVersion.toString_parse hx).symm, by
          rw [EntryVersion.toString_parse hx]; exact hb⟩
    · rintro ⟨x, rfl, hb⟩
      exact ⟨by simp [EntryVersion.parse_toString], hb⟩
  · exact compatOk_iff _

end FvdepAudit.Doc.Proof
