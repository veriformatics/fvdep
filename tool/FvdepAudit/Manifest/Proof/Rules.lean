import FvdepAudit.Doc.Proof.Rules
import FvdepAudit.Manifest.Spec

/-! Each shipped T3 field check decides its spec predicate. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

theorem isCommit_iff (s : String) : isCommit s = true ↔ ∃ c : Commit, s = toString c := by
  simp only [isCommit]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    exact ⟨c, (Commit.toString_parse hc).symm⟩
  · rintro ⟨c, rfl⟩
    simp [Commit.parse_toString]

theorem isVersion_iff (s : String) : isVersion s = true ↔ VersionText s := by
  simp only [isVersion, VersionText, SpellingFits, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hb⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact ⟨x, (EntryVersion.toString_parse hx).symm, hb⟩
  · rintro ⟨x, rfl, hb⟩
    exact ⟨by simp [EntryVersion.parse_toString], hb⟩

theorem isModuleId_iff (s : String) : isModuleId s = true ↔ IdText s := by
  simp only [isModuleId, IdText, SpellingFits, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hb⟩
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    exact ⟨m, (ModuleId.toString_parse hm).symm, hb⟩
  · rintro ⟨m, rfl, hb⟩
    exact ⟨by simp [ModuleId.parse_toString], hb⟩

theorem isShape_iff (s : String) : isShape s = true ↔ s ∈ ["fn", "abi"] := by simp [isShape]

theorem isPolicy_iff (s : String) : isPolicy s = true ↔ s ∈ ["required", "development"] := by
  simp [isPolicy]

theorem headChar_iff (c : Char) : headChar c = true ↔ Letter c ∨ c = '_' := by
  simp [headChar, Letter, Char.isAlpha, Char.isUpper, Char.isLower, Char.le_def]

theorem tailChar_iff (c : Char) : tailChar c = true ↔ Letter c ∨ Digit c ∨ c = '_' ∨ c = '\'' := by
  simp [tailChar, Letter, Digit, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower,
    Char.isDigit, Char.le_def, or_assoc]

theorem isComponent_iff (cs : List Char) : isComponent cs = true ↔ Component cs := by
  cases cs with
  | nil => simp [isComponent, Component]
  | cons c
    rest =>
    simp only [isComponent, Component, Bool.and_eq_true, headChar_iff, List.all_eq_true,
      tailChar_iff, List.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨c, rest, ⟨rfl, rfl⟩, h1, h2⟩
    · rintro ⟨c', rest', ⟨rfl, rfl⟩, h1, h2⟩
      exact ⟨h1, h2⟩

theorem join_eq (sep : Char) : ∀ ps : List (List Char), join sep ps = [sep].intercalate ps
  | [] => rfl
  | [p] => by simp [join]
  | p :: q :: ps => by
    rw [List.intercalate_cons_cons, ← join_eq sep (q :: ps)]
    simp [join]

/-- A component holds no `.`. -/
theorem dot_not_mem {cs : List Char} (h : Component cs) : '.' ∉ cs := by
  obtain ⟨c, rest, rfl, hc, hr⟩ := h
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · subst he
    simp [Letter, Char.le_def] at hc
  · rcases hr '.' hm with h | h | h | h <;> simp [Letter, Digit, Char.le_def] at h

/-- Components joined by `.` cut back into themselves. -/
theorem cut_intercalate {ps : List (List Char)} (hne : ps ≠ []) (h : ∀ p ∈ ps, Component p) :
    cut '.' (['.'].intercalate ps) = ps := by
  rw [← join_eq]
  exact cut_join '.' ps hne fun p hp => dot_not_mem (h p hp)

theorem reserved_iff (h : List Char) :
    reserved (.str .anonymous (String.ofList h)) = true ↔ ReservedHead (String.ofList h) := by
  rw [reserved_root]
  simp [ReservedHead]

theorem isModuleName_iff (s : String) : isModuleName s = true ↔ ModuleName s := by
  unfold isModuleName ModuleName
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    have hj := join_cut '.' s.toList
    cases hc : cut '.' s.toList with
    | nil => exact absurd hc (cut_ne_nil '.' s.toList)
    | cons first rest =>
      rw [hc] at hm hj
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hm
      obtain ⟨⟨hf, hr⟩, hres⟩ := hm
      refine
        ⟨first, rest, by rw [← join_eq, hj], (isComponent_iff _).mp hf, fun c hc' =>
          (isComponent_iff _).mp (hr c hc'), ?_⟩
      intro hR
      have := (reserved_iff first).mpr hR
      simp [this] at hres
  · rintro ⟨hb, h, rest, hs, hh, hr, hR⟩
    refine ⟨hb, ?_⟩
    have hall : ∀ p ∈ h :: rest, Component p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hh
      · exact hr p hp
    rw [hs, cut_intercalate (List.cons_ne_nil h rest) hall]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨⟨(isComponent_iff _).mpr hh, fun c hc => (isComponent_iff _).mpr (hr c hc)⟩, ?_⟩
    cases hres : reserved (.str .anonymous (String.ofList h)) with
    | false => rfl
    | true => exact absurd ((reserved_iff h).mp hres) hR

theorem isConstName_iff (s : String) : isConstName s = true ↔ ConstName s := by
  unfold isConstName ConstName
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hb, hm⟩
    refine
      ⟨hb, cut '.' s.toList, cut_ne_nil '.' s.toList, ?_, fun c hc =>
        (isComponent_iff _).mp (hm c hc)⟩
    rw [← join_eq, join_cut]
  · rintro ⟨hb, cs, hne, hs, hc⟩
    refine ⟨hb, ?_⟩
    rw [hs, cut_intercalate hne hc]
    exact fun c h => (isComponent_iff _).mpr (hc c h)

end FvdepAudit.Manifest.Proof
