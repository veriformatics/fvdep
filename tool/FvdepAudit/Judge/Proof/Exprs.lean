import FvdepAudit.Judge.Proof.Heads

/-! Proofs: one comparison step on expressions (contract `docs/contracts/U7-judge.md` X7) + every
pair's step (`heads_spec`). -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules FvdepAudit.Export.Spec
  FvdepAudit.Judge.Spec

theorem pairEq_name {t1 t2 : Tables} {a b : Nat} {x y : Lean.Name} (hx : t1.names[a]? = some x)
    (hy : t2.names[b]? = some y) : PairEq t1 t2 (.name a b) ↔ x = y := by
  constructor
  · rintro ⟨z, h1, h2⟩
    rw [hx] at h1
    rw [hy] at h2
    cases h1
    cases h2
    rfl
  · rintro rfl
    exact ⟨x, hx, hy⟩

theorem pairEq_level {t1 t2 : Tables} {a b : Nat} {x y : Lean.Level} (hx : t1.levels[a]? = some x)
    (hy : t2.levels[b]? = some y) : PairEq t1 t2 (.level a b) ↔ levelEq x y = true := by
  constructor
  · rintro ⟨x', y', h1, h2, h⟩
    rw [hx] at h1
    rw [hy] at h2
    cases h1
    cases h2
    exact h
  · intro h
    exact ⟨x, y, hx, hy, h⟩

theorem pairEq_expr {t1 t2 : Tables} {a b : Nat} {x y : Lean.Expr} (hx : t1.exprs[a]? = some x)
    (hy : t2.exprs[b]? = some y) : PairEq t1 t2 (.expr a b) ↔ alphaEq x y = true := by
  constructor
  · rintro ⟨x', y', h1, h2, h⟩
    rw [hx] at h1
    rw [hy] at h2
    cases h1
    cases h2
    exact h
  · intro h
    exact ⟨x, y, hx, hy, h⟩

theorem mapM_cons_some {α β : Type} {f : α → Option β} {u : α} {us : List α} {xs : List β} :
    (u :: us).mapM f = some xs ↔ ∃ x xs', f u = some x ∧ us.mapM f = some xs' ∧ xs = x :: xs' := by
  rw [List.mapM_cons]
  cases f u <;> cases us.mapM f <;> simp [eq_comm]

theorem mapM_nil_some {α β : Type} {f : α → Option β} {xs : List β} :
    ([] : List α).mapM f = some xs ↔ xs = [] := by simp [eq_comm]

/-- A constant's level arguments: `zipPairs` decides U4's `levelsEq` of the denoted lists. -/
theorem zipLevels_none {t1 t2 : Tables} :
    ∀ (us vs : List Nat) (xs ys : List Lean.Level),
      us.mapM (fun i => t1.levels[i]?) = some xs →
        vs.mapM (fun i => t2.levels[i]?) = some ys →
        zipPairs .level us vs = none → levelsEq xs ys = false
  | [], [], _, _, _, _, h => by simp [zipPairs] at h
  | [], _ :: _, xs, ys, hx, hy, _ => by
    obtain ⟨y, ys', _, _, rfl⟩ := mapM_cons_some.1 hy
    rw [mapM_nil_some.1 hx]
    rfl
  | _ :: _, [], xs, ys, hx, hy, _ => by
    obtain ⟨x, xs', _, _, rfl⟩ := mapM_cons_some.1 hx
    rw [mapM_nil_some.1 hy]
    rfl
  | u :: us, v :: vs, xs, ys, hx, hy, h => by
    obtain ⟨x, xs', _, hxs, rfl⟩ := mapM_cons_some.1 hx
    obtain ⟨y, ys', _, hys, rfl⟩ := mapM_cons_some.1 hy
    simp only [zipPairs, Option.map_eq_none_iff] at h
    simp [levelsEq, zipLevels_none us vs xs' ys' hxs hys h]

theorem zipLevels_some {t1 t2 : Tables} :
    ∀ (us vs : List Nat) (xs ys : List Lean.Level) (ps : List Pair),
      us.mapM (fun i => t1.levels[i]?) = some xs →
        vs.mapM (fun i => t2.levels[i]?) = some ys →
        zipPairs .level us vs = some ps →
        (levelsEq xs ys = true ↔ ∀ p ∈ ps, PairEq t1 t2 p) ∧
          ∀ p ∈ ps, rank t1 p < t1.names.size + t1.levels.size
  | [], [], xs, ys, ps, hx, hy, h => by
    rw [mapM_nil_some.1 hx, mapM_nil_some.1 hy]
    simp only [zipPairs, Option.some.injEq] at h
    subst h
    simp [levelsEq]
  | [], _ :: _, _, _, _, _, _, h => by simp [zipPairs] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [zipPairs] at h
  | u :: us, v :: vs, xs, ys, ps, hx, hy, h => by
    obtain ⟨x, xs', hu, hxs, rfl⟩ := mapM_cons_some.1 hx
    obtain ⟨y, ys', hv, hys, rfl⟩ := mapM_cons_some.1 hy
    simp only [zipPairs, Option.map_eq_some_iff] at h
    obtain ⟨ps', hps', rfl⟩ := h
    obtain ⟨hiff, hr⟩ := zipLevels_some us vs xs' ys' ps' hxs hys hps'
    refine ⟨?_, ?_⟩
    · simp [levelsEq, hiff, pairEq_level hu hv]
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · have := lt_of_some hu
        simp only [rank]
        omega
      · exact hr p hp

theorem ftag_lt (f : ExprF) : ftag f < 10 := by cases f <;> simp [ftag]

theorem decides_expr {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) (i j : Nat) :
    Decides t1 t2 (.expr i j) (heads t1 t2 (.expr i j)) := by
  simp only [heads]
  cases r1 : t1.rawExprs[i]? with
  | none =>
    apply decides_none
    rintro ⟨_, _, hx, _⟩
    rw [unbound h1.exprsSize r1] at hx
    cases hx
  | some f1 =>
    cases r2 : t2.rawExprs[j]? with
    | none =>
      apply decides_none
      rintro ⟨_, _, _, hy, _⟩
      rw [unbound h2.exprsSize r2] at hy
      cases hy
    | some f2 =>
      show Decides t1 t2 (.expr i j) (exprHeads f1 f2)
      obtain ⟨e1, he1, hd1⟩ := h1.expr i f1 r1
      obtain ⟨e2, he2, hd2⟩ := h2.expr j f2 r2
      have hp : PairEq t1 t2 (.expr i j) ↔ alphaEq e1 e2 = true := pairEq_expr he1 he2
      by_cases ht : ftag f1 = ftag f2
      · cases f1 <;> cases f2 <;> simp [ftag] at ht
        · rename_i a b
          subst hd1
          subst hd2
          by_cases hab : a = b
          · subst hab
            simp only [exprHeads, beq_self_eq_true, ↓reduceIte]
            exact decides_some (by simp [hp, alphaEq_bvar]) (fun k hk => by cases hk)
          · have hb : (a == b) = false := by simpa using hab
            simp only [exprHeads, hb, Bool.false_eq_true, ↓reduceIte]
            apply decides_none
            rw [hp, alphaEq_bvar, hb]
            simp
        · rename_i a b
          obtain ⟨x, hx, rfl⟩ := hd1
          obtain ⟨y, hy, rfl⟩ := hd2
          refine decides_some ?_ ?_
          · simp [hp, alphaEq_sort, pairEq_level hx hy]
          · have := lt_of_some hx
            simp only [List.mem_singleton, forall_eq, rank]
            omega
        · rename_i n us m vs
          obtain ⟨x, xs, hx, hxs, rfl⟩ := hd1
          obtain ⟨y, ys, hy, hys, rfl⟩ := hd2
          simp only [exprHeads]
          cases hz : zipPairs .level us vs with
          | none =>
            show Decides t1 t2 (.expr i j) none
            apply decides_none
            rw [hp, alphaEq_const, zipLevels_none us vs xs ys hxs hys hz]
            simp
          | some ps =>
            show Decides t1 t2 (.expr i j) (some (.name n m :: ps))
            obtain ⟨hiff, hr⟩ := zipLevels_some us vs xs ys ps hxs hys hz
            refine decides_some ?_ ?_
            · simp [hp, alphaEq_const, hiff, pairEq_name hx hy]
            · intro k hk
              rcases List.mem_cons.1 hk with rfl | hk
              · have := lt_of_some hx
                simp only [rank]
                omega
              · have := hr k hk
                simp only [rank] at this ⊢
                omega
        · rename_i f a g b
          obtain ⟨x, y, hx, hy, rfl⟩ := hd1
          obtain ⟨x', y', hx', hy', rfl⟩ := hd2
          obtain ⟨hf, hx⟩ := extract_some hx
          obtain ⟨ha, hy⟩ := extract_some hy
          obtain ⟨-, hx'⟩ := extract_some hx'
          obtain ⟨-, hy'⟩ := extract_some hy'
          refine decides_some ?_ ?_
          · simp [hp, alphaEq_app, pairEq_expr hx hx', pairEq_expr hy hy']
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, rank]
            omega
        · rename_i n ty b bi n' ty' b' bi'
          obtain ⟨x, u, w, _, hu, hw, rfl⟩ := hd1
          obtain ⟨x', u', w', _, hu', hw', rfl⟩ := hd2
          obtain ⟨hty, hu⟩ := extract_some hu
          obtain ⟨hb, hw⟩ := extract_some hw
          obtain ⟨-, hu'⟩ := extract_some hu'
          obtain ⟨-, hw'⟩ := extract_some hw'
          refine decides_some ?_ ?_
          · simp [hp, alphaEq_lam, pairEq_expr hu hu', pairEq_expr hw hw']
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, rank]
            omega
        · rename_i n ty b bi n' ty' b' bi'
          obtain ⟨x, u, w, _, hu, hw, rfl⟩ := hd1
          obtain ⟨x', u', w', _, hu', hw', rfl⟩ := hd2
          obtain ⟨hty, hu⟩ := extract_some hu
          obtain ⟨hb, hw⟩ := extract_some hw
          obtain ⟨-, hu'⟩ := extract_some hu'
          obtain ⟨-, hw'⟩ := extract_some hw'
          refine decides_some ?_ ?_
          · simp [hp, alphaEq_forallE, pairEq_expr hu hu', pairEq_expr hw hw']
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, rank]
            omega
        · rename_i n ty v b nd n' ty' v' b' nd'
          obtain ⟨x, u, z, w, _, hu, hz, hw, rfl⟩ := hd1
          obtain ⟨x', u', z', w', _, hu', hz', hw', rfl⟩ := hd2
          obtain ⟨hty, hu⟩ := extract_some hu
          obtain ⟨hv, hz⟩ := extract_some hz
          obtain ⟨hb, hw⟩ := extract_some hw
          obtain ⟨-, hu'⟩ := extract_some hu'
          obtain ⟨-, hz'⟩ := extract_some hz'
          obtain ⟨-, hw'⟩ := extract_some hw'
          refine decides_some ?_ ?_
          · simp [hp, alphaEq_letE, pairEq_expr hu hu', pairEq_expr hz hz', pairEq_expr hw hw',
              and_assoc]
          · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
              and_true, rank]
            omega
        · rename_i tn idx s tn' idx' s'
          obtain ⟨x, y, hx, hy, rfl⟩ := hd1
          obtain ⟨x', y', hx', hy', rfl⟩ := hd2
          obtain ⟨hs, hy⟩ := extract_some hy
          obtain ⟨-, hy'⟩ := extract_some hy'
          by_cases hidx : idx = idx'
          · subst hidx
            simp only [exprHeads, beq_self_eq_true, ↓reduceIte]
            refine decides_some ?_ ?_
            · simp [hp, alphaEq_proj, pairEq_name hx hx', pairEq_expr hy hy']
            · have := lt_of_some hx
              simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                and_true, rank]
              omega
          · have hb : (idx == idx') = false := by simpa using hidx
            simp only [exprHeads, hb, Bool.false_eq_true, ↓reduceIte]
            apply decides_none
            rw [hp, alphaEq_proj, hb]
            simp
        · rename_i a b
          subst hd1
          subst hd2
          by_cases hab : a = b
          · subst hab
            simp only [exprHeads, beq_self_eq_true, ↓reduceIte]
            exact decides_some (by simp [hp, alphaEq_natVal]) (fun k hk => by cases hk)
          · have hb : (a == b) = false := by simpa using hab
            simp only [exprHeads, hb, Bool.false_eq_true, ↓reduceIte]
            apply decides_none
            rw [hp, alphaEq_natVal, hb]
            simp
        · rename_i a b
          subst hd1
          subst hd2
          by_cases hab : a = b
          · subst hab
            simp only [exprHeads, beq_self_eq_true, ↓reduceIte]
            exact decides_some (by simp [hp, alphaEq_strVal]) (fun k hk => by cases hk)
          · have hb : (a == b) = false := by simpa using hab
            simp only [exprHeads, hb, Bool.false_eq_true, ↓reduceIte]
            apply decides_none
            rw [hp, alphaEq_strVal, hb]
            simp
      · rw [exprHeads_tag ht]
        apply decides_none
        rw [hp]
        have h1t := etag_denotes hd1
        have h2t := etag_denotes hd2
        rw [alphaEq_tag
            (by
              rw [h1t, h2t]; exact ht)
            (by
              rw [h1t]; exact ftag_lt f1)
            (by
              rw [h2t]; exact ftag_lt f2)]
        simp

/-- Every pair's step obeys `Decides`. -/
theorem heads_spec {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) :
    ∀ p, Decides t1 t2 p (heads t1 t2 p)
  | .name i j => decides_name h1 h2 i j
  | .level i j => decides_level h1 h2 i j
  | .expr i j => decides_expr h1 h2 i j

end FvdepAudit.Judge.Proof
