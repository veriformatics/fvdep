import FvdepAudit.Manifest.Proof.Lists
import FvdepAudit.Manifest.Proof.Rules

/-! What each shipped field + table check accepts (`… = none`), as plain facts about the tree. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

theorem strField_none_iff {ok : String → Bool} {p : List PathSeg} {v : Tree} :
    strField ok p v = none ↔ ∃ s, v = .str s ∧ ok s = true := by
  cases v with
  | str s => by_cases h : ok s = true <;> simp [strField, h]
  | _ => simp [strField]

/-- Each string from index `i` on meets `ok` at its index. -/
def ElemsOk (ok : Nat → String → Bool) : Nat → List String → Prop
  | _, [] => True
  | i, s :: ss => ok i s = true ∧ ElemsOk ok (i + 1) ss

theorem strings_map (ss : List String) : strings (ss.map .str) = ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    unfold strings at ih ⊢
    simp only [List.map_cons, List.filterMap_cons, ih]

theorem byKey_nil : byKey [] = [] := by simp [byKey]

theorem byKey_single (m : String × Tree) : byKey [m] = [m] := by simp [byKey]

theorem elemsCheck_none_iff {ok : Nat → String → Bool} {p : List PathSeg} :
    ∀ {i : Nat} {xs : List Tree},
      elemsCheck ok p i xs = none ↔ ∃ ss, xs = ss.map .str ∧ ElemsOk ok i ss
  | _, [] => by simp [elemsCheck, ElemsOk]
  | i, x :: xs => by
    cases x with
    | str s =>
      by_cases h : ok i s = true
      · simp only [elemsCheck, h, ite_true]
        rw [elemsCheck_none_iff]
        constructor
        · rintro ⟨ss, rfl, hs⟩
          exact ⟨s :: ss, rfl, h, hs⟩
        · rintro ⟨ss, hss, hs⟩
          cases ss with
          | nil => simp at hss
          | cons s' ss =>
            simp only [List.map_cons, List.cons.injEq, Tree.str.injEq] at hss
            obtain ⟨rfl, rfl⟩ := hss
            exact ⟨ss, rfl, hs.2⟩
      · simp only [elemsCheck, h, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
        rintro ⟨ss, hss, hs⟩
        cases ss with
        | nil => simp at hss
        | cons s' ss =>
          simp only [List.map_cons, List.cons.injEq, Tree.str.injEq] at hss
          obtain ⟨rfl, rfl⟩ := hss
          exact h hs.1
    | _ =>
      simp only [elemsCheck, reduceCtorEq, false_iff]
      rintro ⟨ss, hss, _⟩
      cases ss <;> simp at hss

theorem firstRepeatIndex_none_iff :
    ∀ {seen : List String} {i : Nat} {xs : List String},
      firstRepeatIndex seen i xs = none ↔ (∀ x ∈ xs, x ∉ seen) ∧ xs.Nodup
  | _, _, [] => by simp [firstRepeatIndex]
  | seen, i, x :: xs => by
    by_cases h : x ∈ seen
    · simp [firstRepeatIndex, h]
    · have hc : seen.contains x = false := by simpa using h
      simp only [firstRepeatIndex, hc, Bool.false_eq_true, ite_false]
      rw [firstRepeatIndex_none_iff]
      constructor
      · rintro ⟨hall, hnd⟩
        refine ⟨fun y hy => ?_, List.nodup_cons.mpr ⟨fun hx => ?_, hnd⟩⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact h
          · exact fun hs => (hall y hy) (List.mem_cons_of_mem _ hs)
        · exact (hall x hx) (List.mem_cons_self ..)
      · rintro ⟨hall, hnd⟩
        refine ⟨fun y hy hs => ?_, (List.nodup_cons.mp hnd).2⟩
        rcases List.mem_cons.mp hs with rfl | hs
        · exact (List.nodup_cons.mp hnd).1 hy
        · exact hall y (List.mem_cons_of_mem _ hy) hs

theorem arrayCheck_none_iff {ok : Nat → String → Bool} {unique : Bool} {p : List PathSeg}
    {v : Tree} :
    arrayCheck ok unique p v = none ↔
      ∃ ss, v = .arr (ss.map .str) ∧ ss ≠ [] ∧ ElemsOk ok 0 ss ∧ (unique = true → ss.Nodup) := by
  cases v with
  | arr xs =>
    simp only [arrayCheck, orElse_eq, Tree.arr.injEq]
    by_cases he : xs.isEmpty = true
    · have : xs = [] := List.isEmpty_iff.mp he
      subst this
      simp
    · simp only [he, Bool.false_eq_true, ite_false, Option.or_eq_none_iff, elemsCheck_none_iff]
      constructor
      · rintro ⟨⟨ss, rfl, hs⟩, hr⟩
        refine ⟨ss, rfl, fun hn => by simp [hn] at he, hs, fun hu => ?_⟩
        simp only [hu, ite_true, strings_map, Option.map_eq_none_iff] at hr
        exact (firstRepeatIndex_none_iff.mp hr).2
      · rintro ⟨ss, rfl, _, hs, hu⟩
        refine ⟨⟨ss, rfl, hs⟩, ?_⟩
        cases unique with
        | false => rfl
        | true =>
          simp only [ite_true, strings_map, Option.map_eq_none_iff]
          exact firstRepeatIndex_none_iff.mpr ⟨by simp, hu rfl⟩
  | _ => simp [arrayCheck]

/-- Distinct keys all equal to `key`: at most one member. -/
theorem single_of_keys {ms : List (String × Tree)} {key : String} (hd : (ms.map (·.1)).Nodup)
    (hk : ∀ m ∈ ms, m.1 = key) : ms = [] ∨ ∃ w, ms = [(key, w)] := by
  match ms, hd, hk with
  | [], _, _ => exact Or.inl rfl
  | [(a, w)], _, hk =>
    have ha : a = key := hk (a, w) (by simp)
    subst ha
    exact Or.inr ⟨w, rfl⟩
  | (a, w) :: (b, u) :: rest, hd, hk =>
    have ha := hk (a, w) (by simp)
    have hb := hk (b, u) (by simp)
    simp only at ha hb
    subst ha hb
    simp at hd

theorem tableCheck_none_iff {key : String} {required : Bool} {ok : String → Bool} {p : List PathSeg}
    {v : Tree} :
    tableCheck key required ok p v = none ↔
      v = .tbl [] ∧ required = false ∨ ∃ s, v = .tbl [(key, .str s)] ∧ ok s = true := by
  cases v with
  | tbl ms =>
    simp only [tableCheck, Tree.tbl.injEq]
    cases hr : repeatedKey ms with
    | some k =>
      simp only [reduceCtorEq, false_iff, not_or, not_and, not_exists]
      have hnd : ¬(ms.map (·.1)).Nodup := fun h => by simp [(repeatedKey_none_iff ms).mpr h] at hr
      refine
        ⟨fun h => by
          subst h; simp at hnd, fun s h => by
          subst h; simp at hnd⟩
    | none =>
      have hd := (repeatedKey_none_iff ms).mp hr
      simp only [orElse_eq, Option.or_eq_none_iff, firstKey_none_iff, bne_eq_false_iff_eq,
        firstMissing_none_iff, valuesCheck_none_iff]
      constructor
      · rintro ⟨hk, hm, hv⟩
        have hk' : ∀ m ∈ ms, m.1 = key := fun m h => hk m (mem_byKey.mpr h)
        rcases single_of_keys hd hk' with rfl | ⟨w, rfl⟩
        · left
          refine ⟨rfl, ?_⟩
          cases required with
          | false => rfl
          | true => simp [byKey_nil] at hm
        · right
          have := hv (key, w) (by simp [byKey_single])
          simp only [beq_self_eq_true, ite_true, strField_none_iff] at this
          obtain ⟨s, rfl, hs⟩ := this
          exact ⟨s, rfl, hs⟩
      · rintro (⟨rfl, rfl⟩ | ⟨s, rfl, hs⟩)
        · simp [byKey_nil]
        · refine ⟨by simp [byKey_single], ?_, ?_⟩
          · intro k hk
            have : k = key := by cases required <;> simp_all
            subst this
            simp [byKey_single]
          · intro m hm
            simp only [byKey_single, List.mem_singleton] at hm
            subst hm
            simp [strField, hs]
  | _ => simp [tableCheck]

end FvdepAudit.Manifest.Proof
