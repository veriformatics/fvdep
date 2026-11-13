import FvdepAudit.Json.Spec
import FvdepCore.Json
import Init.Data.List.Sort.Lemmas

namespace FvdepAudit.Json.Proof

open FvdepCore.Json

mutual
theorem stringsFit_eq (v : Value) : stringsFit v = FvdepAudit.Json.Spec.stringsFit v := by
  cases v with
  | arr xs => exact stringsFitList_eq xs
  | obj ms => exact stringsFitMembers_eq ms
  | _ => rfl
theorem stringsFitList_eq (vs : List Value) :
    stringsFitList vs = FvdepAudit.Json.Spec.stringsFitList vs := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [stringsFitList, FvdepAudit.Json.Spec.stringsFitList, stringsFit_eq v,
      stringsFitList_eq vs]
theorem stringsFitMembers_eq (ms : List (String × Value)) :
    stringsFitMembers ms = FvdepAudit.Json.Spec.stringsFitMembers ms := by
  cases ms with
  | nil => rfl
  | cons p ms =>
    rcases p with ⟨k, v⟩
    simp only [stringsFitMembers, FvdepAudit.Json.Spec.stringsFitMembers, stringsFit_eq v,
      stringsFitMembers_eq ms, maxStringBytes, FvdepAudit.Json.Spec.maxStringBytes]
    rfl
end

mutual
theorem canon_eq (v : Value) : canon v = FvdepAudit.Json.Spec.canon v := by
  cases v with
  | arr xs =>
    simp only [canon, FvdepAudit.Json.Spec.canon, canonList_eq, List.reverse_nil, List.nil_append]
  | obj ms =>
    simp only [canon, FvdepAudit.Json.Spec.canon, canonMembers_eq, List.reverse_nil,
      List.nil_append, Value.sortMembers]
  | _ => rfl
theorem canonList_eq (vs acc : List Value) :
    canonList vs acc = acc.reverse ++ FvdepAudit.Json.Spec.canonList vs := by
  cases vs with
  | nil => simp [canonList, FvdepAudit.Json.Spec.canonList]
  | cons v vs =>
    simp only [canonList, FvdepAudit.Json.Spec.canonList, canonList_eq vs, canon_eq v,
      List.reverse_cons, List.append_assoc, List.singleton_append]
theorem canonMembers_eq (ms acc : List (String × Value)) :
    canonMembers ms acc = acc.reverse ++ FvdepAudit.Json.Spec.canonMembers ms := by
  cases ms with
  | nil => simp [canonMembers, FvdepAudit.Json.Spec.canonMembers]
  | cons p ms =>
    rcases p with ⟨k, v⟩
    simp only [canonMembers, FvdepAudit.Json.Spec.canonMembers, canonMembers_eq ms, canon_eq v,
      List.reverse_cons, List.append_assoc, List.singleton_append]
end

theorem adjacentDup_false_iff (xs : List String) (hs : xs.Pairwise (· ≤ ·)) :
    adjacentDup xs = false ↔ xs.Nodup := by
  induction xs with
  | nil => simp [adjacentDup]
  | cons a xs ih =>
    cases xs with
    | nil => simp [adjacentDup]
    | cons b xs =>
      have htail := List.pairwise_cons.mp hs
      have ih := ih htail.2
      simp only [adjacentDup, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ih]
      constructor
      · rintro ⟨hne, hnd⟩
        apply List.nodup_cons.mpr
        refine ⟨?_, hnd⟩
        intro hm
        rcases List.mem_cons.mp hm with he | hm
        · exact hne he
        · have hab := htail.1 b (by simp)
          have hba := (List.pairwise_cons.mp htail.2).1 a hm
          exact hne (Std.le_antisymm hab hba)
      · intro hnd
        have hn := List.nodup_cons.mp hnd
        exact ⟨fun he => hn.1 (by simp [he]), hn.2⟩

theorem adjacentDup_sort_eq (xs : List String) :
    adjacentDup (xs.mergeSort (· ≤ ·)) = !decide xs.Nodup := by
  have hs : (xs.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
    suffices h : (xs.mergeSort (· ≤ ·)).Pairwise (fun a b => decide (a ≤ b) = true) by simpa using h
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      simpa using Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
    · intro a b
      simpa using (Std.le_total (a := a) (b := b))
  have he := (adjacentDup_false_iff _ hs).trans (List.mergeSort_perm xs _).nodup_iff
  cases hd : adjacentDup (xs.mergeSort (· ≤ ·)) <;> simp_all

mutual
theorem hasDupKey_eq (v : Value) : hasDupKey v = FvdepAudit.Json.Spec.hasDupKey v := by
  cases v with
  | arr xs => exact hasDupKeyList_eq xs
  | obj ms =>
    simp only [hasDupKey, FvdepAudit.Json.Spec.hasDupKey, adjacentDup_sort_eq, hasDupKeyMembers_eq]
  | _ => rfl
theorem hasDupKeyList_eq (vs : List Value) :
    hasDupKeyList vs = FvdepAudit.Json.Spec.hasDupKeyList vs := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [hasDupKeyList, FvdepAudit.Json.Spec.hasDupKeyList, hasDupKey_eq v,
      hasDupKeyList_eq vs]
theorem hasDupKeyMembers_eq (ms : List (String × Value)) :
    hasDupKeyMembers ms = FvdepAudit.Json.Spec.hasDupKeyMembers ms := by
  cases ms with
  | nil => rfl
  | cons p ms =>
    rcases p with ⟨k, v⟩
    simp only [hasDupKeyMembers, FvdepAudit.Json.Spec.hasDupKeyMembers, hasDupKey_eq v,
      hasDupKeyMembers_eq ms]
end

theorem stringsFit_eq_spec : FvdepCore.Json.stringsFit = FvdepAudit.Json.Spec.stringsFit :=
  funext stringsFit_eq

theorem hasDupKey_eq_spec : FvdepCore.Json.hasDupKey = FvdepAudit.Json.Spec.hasDupKey :=
  funext hasDupKey_eq

theorem canon_eq_spec : FvdepCore.Json.canon = FvdepAudit.Json.Spec.canon := funext canon_eq

end FvdepAudit.Json.Proof
