import FvdepAudit.Index.Budget.Spec
import FvdepCore.Index.Budget

/-! Proofs: U7 Part B B5's countdown = the walk's expanded size (`sizeF`) against the budget. -/

namespace FvdepAudit.Index.Budget.Proof

open Lean FvdepCore.Index.Registry FvdepAudit.Index.Budget.Spec FvdepAudit.Registry.Spec

/-- The countdown's read-through = the spec's. -/
theorem unfold_eq (F : Facts) (p : List Name) (c : Name) : unfold? F p c = unfoldS F p c := by
  unfold unfold? unfoldS valueOf?
  by_cases hp : c ∈ p
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    cases F.decls.find? (·.name == c) with
    | none => rfl
    | some d =>
      simp only
      by_cases hk : d.kind = .defn <;> by_cases hr : d.module = `Fvdep.Registry <;>
        by_cases he : c = .str d.module "entry" <;>
        simp [hk, hr, he, rootModule]

/-- The spec's read-through = C2's spec relations (`RootDef` ∨ `EntryDef`). -/
theorem unfoldS_iff (F : Facts) (p : List Name) (c : Name) (x : Expr) :
    unfoldS F p c = some x ↔ RootDef F p c x ∨ ∃ m, EntryDef F p c m x := by
  unfold unfoldS RootDef EntryDef
  by_cases hp : c ∈ p
  · simp [hp]
  · simp only [hp, ↓reduceIte, not_false_eq_true, true_and]
    cases hd : F.decls.find? (·.name == c) with
    | none => simp
    | some d =>
      simp only [Option.some.injEq, exists_eq_left']
      constructor
      · intro h
        split at h
        · rename_i hc
          obtain ⟨hk, hm | he⟩ := hc
          · exact Or.inl ⟨hk, hm, h⟩
          · exact Or.inr ⟨d.module, he, hk, rfl, h⟩
        · cases h
      · rintro (⟨hk, hm, hv⟩ | ⟨m, he, hk, hm, hv⟩)
        · simp [hk, hm, hv]
        · subst hm
          simp [hk, he, hv]

theorem sizeF_pos (F : Facts) (e : Expr) (env : List Expr) (p : List Name) :
    0 < sizeF F e env p := by
  rw [sizeF.eq_def]
  dsimp only
  split <;> (try split) <;> omega

theorem withinF_bvar_some {F : Facts} {k i : Nat} {env : List Expr} {p : List Name} {v : Expr}
    (hv : env[i]? = some v) :
    withinF F (k + 1) (.bvar i) env p = withinF F k v (env.drop (i + 1)) p := by
  rw [withinF.eq_def]
  dsimp only
  split <;> simp_all

theorem withinF_bvar_none {F : Facts} {k i : Nat} {env : List Expr} {p : List Name}
    (hv : env[i]? = none) : withinF F (k + 1) (.bvar i) env p = some k := by
  rw [withinF.eq_def]
  dsimp only
  split <;> simp_all

theorem withinF_const_some {F : Facts} {k : Nat} {c : Name} {us : List Level} {env : List Expr}
    {p : List Name} {v : Expr} (hu : unfold? F p c = some v) :
    withinF F (k + 1) (.const c us) env p = withinF F k v [] (c :: p) := by
  rw [withinF.eq_def]
  dsimp only
  split <;> simp_all

theorem withinF_const_none {F : Facts} {k : Nat} {c : Name} {us : List Level} {env : List Expr}
    {p : List Name} (hu : unfold? F p c = none) :
    withinF F (k + 1) (.const c us) env p = some k := by
  rw [withinF.eq_def]
  dsimp only
  split <;> simp_all

theorem sizeF_bvar_some {F : Facts} {i : Nat} {env : List Expr} {p : List Name} {v : Expr}
    (hv : env[i]? = some v) : sizeF F (.bvar i) env p = 1 + sizeF F v (env.drop (i + 1)) p := by
  rw [sizeF.eq_def]
  dsimp only
  split <;> simp_all

theorem sizeF_bvar_none {F : Facts} {i : Nat} {env : List Expr} {p : List Name}
    (hv : env[i]? = none) : sizeF F (.bvar i) env p = 1 := by
  rw [sizeF.eq_def]
  dsimp only
  split <;> simp_all

theorem sizeF_const_some {F : Facts} {c : Name} {us : List Level} {env : List Expr} {p : List Name}
    {v : Expr} (hu : unfoldS F p c = some v) :
    sizeF F (.const c us) env p = 1 + sizeF F v [] (c :: p) := by
  rw [sizeF.eq_def]
  dsimp only
  split <;> simp_all

theorem sizeF_const_none {F : Facts} {c : Name} {us : List Level} {env : List Expr} {p : List Name}
    (hu : unfoldS F p c = none) : sizeF F (.const c us) env p = 1 := by
  rw [sizeF.eq_def]
  dsimp only
  split <;> simp_all

/-- One node more on both sides. -/
theorem step_ite (n k : Nat) :
    (if n ≤ k then some (k - n) else none) =
      if 1 + n ≤ k + 1 then some (k + 1 - (1 + n)) else none := by
  by_cases h : n ≤ k
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- U7 B5 `decodeBudget`: the countdown = the walk's expanded size against the budget. -/
theorem withinF_eq (F : Facts) (k : Nat) (e : Expr) (env : List Expr) (p : List Name) :
    withinF F k e env p = if sizeF F e env p ≤ k then some (k - sizeF F e env p) else none := by
  have hpos := sizeF_pos F e env p
  match k, e with
  | 0, e => rw [withinF.eq_def, ite_eq_right (by omega)]
  | k + 1, .mdata d b =>
    have ih := withinF_eq F k b env p
    rw [withinF.eq_def, sizeF.eq_def]
    dsimp only
    rw [ih]
    exact step_ite _ _
  | k + 1, .letE n t v b nd =>
    have ih := withinF_eq F k b (v :: env) p
    rw [withinF.eq_def, sizeF.eq_def]
    dsimp only
    rw [ih]
    exact step_ite _ _
  | k + 1, .bvar i =>
    match hv : env[i]? with
    | some v =>
      have := env_le hv
      rw [withinF_bvar_some hv, sizeF_bvar_some hv, withinF_eq F k v (env.drop (i + 1)) p]
      exact step_ite _ _
    | none =>
      rw [withinF_bvar_none hv, sizeF_bvar_none hv, ite_eq_left (by omega)]
      simp
  | k + 1, .app f a =>
    have ihf := withinF_eq F k f env p
    rw [withinF.eq_def, sizeF.eq_def]
    dsimp only
    rw [ihf]
    by_cases hf : sizeF F f env p ≤ k
    · rw [ite_eq_left hf]
      dsimp only
      rw [withinF_eq F (k - sizeF F f env p) a env p]
      by_cases ha : sizeF F a env p ≤ k - sizeF F f env p
      · rw [ite_eq_left ha, ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right ha, ite_eq_right (by omega)]
    · rw [ite_eq_right hf, ite_eq_right (by omega)]
  | k + 1, .const c us =>
    match hu : unfold? F p c with
    | some v =>
      have := unfold_fresh hu
      have hs : unfoldS F p c = some v := by
        rw [← unfold_eq]; exact hu
      rw [withinF_const_some hu, sizeF_const_some hs, withinF_eq F k v [] (c :: p)]
      exact step_ite _ _
    |
    none =>
      have hs : unfoldS F p c = none := by
        rw [← unfold_eq]; exact hu
      rw [withinF_const_none hu, sizeF_const_none hs, ite_eq_left (by omega)]
      simp
  | k + 1, .fvar _ | k + 1, .mvar _ | k + 1, .sort _ | k + 1, .lam _ _ _ _ | k + 1,
    .forallE _ _ _ _ | k + 1, .lit _ | k + 1,
    .proj _ _ _ =>
    rw [withinF.eq_def, sizeF.eq_def]
    dsimp only
    rw [ite_eq_left (by omega)]
    simp
termination_by (fresh F p, sizeOf e + envSize env)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; assumption)
    | (apply Prod.Lex.right; simp; omega)

end FvdepAudit.Index.Budget.Proof
