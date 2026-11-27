import FvdepCore.Judge.Reuse

/-! Proofs: K5's memo (contract `docs/contracts/U7-judge.md` Part B K5) — a lookup answers exactly
with the first recordable answer a command's run events gave under that very key. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Judge

theorem lookup_append (m : Memo) (k k' : ReuseKey) (a : Answer) :
    Memo.lookup (m ++ [(k', a)]) k = (m.lookup k).or (if k' == k then some a else none) := by
  unfold Memo.lookup
  rw [List.find?_append]
  cases h : m.find? (·.1 == k) with
  | some x => simp
  | none =>
    by_cases hk : k' == k
    · simp [hk]
    · simp [hk]

theorem lookup_record (m : Memo) (k k' : ReuseKey) (a : Answer) :
    (m.record k' a).lookup k =
      (m.lookup k).or (if k' == k && recordable a.1 then some a else none) := by
  unfold Memo.record
  by_cases hr : recordable a.1 = true
  · cases hl : m.lookup k' with
    | none =>
      simp only [hr, Option.isNone_none, Bool.and_self, ↓reduceIte, Bool.and_true]
      exact lookup_append m k k' a
    | some
      b =>
      simp only [hr, Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        Bool.and_true]
      by_cases hk : k' == k
      · have : k' = k := by simpa using hk
        subst this
        simp [hl]
      · simp [hk]
  · simp [hr]

/-- U7 part B K5 `reuseExact`. -/
theorem reuse_exact (es : List (ReuseKey × Answer)) (k : ReuseKey) :
    (Memo.ofEvents es).lookup k = (es.find? fun e => e.1 == k && recordable e.2.1).map (·.2) := by
  have h :
    ∀ (m : Memo) (es : List (ReuseKey × Answer)),
      (es.foldl (fun m e => m.record e.1 e.2) m).lookup k =
        (m.lookup k).or ((es.find? fun e => e.1 == k && recordable e.2.1).map (·.2)) := by
    intro m es
    induction es generalizing m with
    | nil => simp
    | cons e es ih =>
      simp only [List.foldl_cons, List.find?_cons]
      rw [ih, lookup_record, Option.or_assoc]
      by_cases hc : (e.1 == k && recordable e.2.1) = true
      · simp [hc]
      · simp [hc]
  simpa [Memo.ofEvents, Memo.lookup] using h [] es

end FvdepAudit.Judge.Proof
