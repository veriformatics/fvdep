import FvdepAudit.Export.Proof

/-! Proofs: the reader's raw records beside their denotation (contract `docs/contracts/U7-judge.md`
X6): on every export the reader accepts, record `i` of each raw table denotes entry `i` under the
entries before it — the fact the judge's comparisons stand on. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepAudit.Export.Spec FvdepAudit.Export.Proof

/-- Each raw record denotes its table entry under the entries before it (index 0 of names + levels
= the predefined anonymous name + zero). -/
structure RawOk (t : Tables) : Prop where
  namesSize : t.rawNames.size = t.names.size
  levelsSize : t.rawLevels.size = t.levels.size
  exprsSize : t.rawExprs.size = t.exprs.size
  name0 : ∀ i : Nat, t.rawNames[i]? = some none → t.names[i]? = some Lean.Name.anonymous
  name :
    ∀ (i : Nat) (f : NameF),
      t.rawNames[i]? = some (some f) →
        ∃ n, t.names[i]? = some n ∧ NameDenotes (t.names.extract 0 i) f n
  level0 : ∀ i : Nat, t.rawLevels[i]? = some none → t.levels[i]? = some Lean.Level.zero
  level :
    ∀ (i : Nat) (f : LevelF),
      t.rawLevels[i]? = some (some f) →
        ∃ v, t.levels[i]? = some v ∧ LevelDenotes t.names (t.levels.extract 0 i) f v
  expr :
    ∀ (i : Nat) (f : ExprF),
      t.rawExprs[i]? = some f →
        ∃ e, t.exprs[i]? = some e ∧ ExprDenotes t.names t.levels (t.exprs.extract 0 i) f e

theorem lt_of_some {α : Type} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) :
    i < a.size := by
  rw [Array.getElem?_eq_some_iff] at h
  exact h.1

theorem get_push {α : Type} {a : Array α} {x y : α} {i : Nat} (h : a[i]? = some x) :
    (a.push y)[i]? = some x := by
  rw [Array.getElem?_push]
  have : i ≠ a.size := Nat.ne_of_lt (lt_of_some h)
  simp [this, h]

theorem get_push_size {α : Type} (a : Array α) (y : α) : (a.push y)[a.size]? = some y := by simp

/-- A lookup in a prefix = an earlier entry of the whole. -/
theorem extract_some {α : Type} {a : Array α} {i p : Nat} {x : α}
    (h : (a.extract 0 i)[p]? = some x) : p < i ∧ a[p]? = some x := by
  rw [Array.getElem?_extract] at h
  split at h
  · rename_i hp
    simp only [Nat.sub_zero, Nat.lt_min] at hp
    exact ⟨hp.1, by simpa using h⟩
  · cases h

theorem extract_push {α : Type} {a : Array α} {y : α} {i : Nat} (hi : i ≤ a.size) :
    (a.push y).extract 0 i = a.extract 0 i := Array.extract_push_of_le hi

theorem mapM_mono {α : Type} {L L' : Array α}
    (hL : ∀ (l : Nat) (x : α), L[l]? = some x → L'[l]? = some x) :
    ∀ (us : List Nat) (xs : List α),
      us.mapM (fun i => L[i]?) = some xs → us.mapM (fun i => L'[i]?) = some xs
  | [], xs, h => h
  | u :: us, xs, h => by
    rw [List.mapM_cons] at h ⊢
    cases hu : L[u]? with
    | none => simp [hu] at h
    | some a =>
      cases hm : us.mapM (fun i => L[i]?) with
      | none => simp [hu, hm] at h
      | some ys =>
        simp [hu, hm] at h
        subst h
        simp [hL u a hu, mapM_mono hL us ys hm]

theorem levelDenotes_mono {N N' : Array Lean.Name} {L : Array Lean.Level} {f : LevelF}
    {v : Lean.Level} (hN : ∀ (n : Nat) (x : Lean.Name), N[n]? = some x → N'[n]? = some x)
    (h : LevelDenotes N L f v) : LevelDenotes N' L f v := by
  cases f with
  | succ l => exact h
  | max a b => exact h
  | imax a b => exact h
  | param n =>
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨x, hN _ _ hx, rfl⟩

theorem exprDenotes_mono {N N' : Array Lean.Name} {L L' : Array Lean.Level} {X : Array Lean.Expr}
    {f : ExprF} {e : Lean.Expr} (hN : ∀ (n : Nat) (x : Lean.Name), N[n]? = some x → N'[n]? = some x)
    (hL : ∀ (l : Nat) (x : Lean.Level), L[l]? = some x → L'[l]? = some x)
    (h : ExprDenotes N L X f e) : ExprDenotes N' L' X f e := by
  cases f with
  | bvar k => exact h
  | sort l =>
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨x, hL _ _ hx, rfl⟩
  | const n us =>
    obtain ⟨x, xs, hx, hxs, rfl⟩ := h
    exact ⟨x, xs, hN _ _ hx, mapM_mono hL us xs hxs, rfl⟩
  | app f a => exact h
  | lam n ty b bi =>
    obtain ⟨x, u, b', hx, hu, hb, rfl⟩ := h
    exact ⟨x, u, b', hN _ _ hx, hu, hb, rfl⟩
  | forallE n ty b bi =>
    obtain ⟨x, u, b', hx, hu, hb, rfl⟩ := h
    exact ⟨x, u, b', hN _ _ hx, hu, hb, rfl⟩
  | letE n ty v b nd =>
    obtain ⟨x, u, w, b', hx, hu, hw, hb, rfl⟩ := h
    exact ⟨x, u, w, b', hN _ _ hx, hu, hw, hb, rfl⟩
  | proj tn idx s =>
    obtain ⟨x, y, hx, hy, rfl⟩ := h
    exact ⟨x, y, hN _ _ hx, hy, rfl⟩
  | natVal v => exact h
  | strVal s => exact h

/-- A pushed table keeps every earlier entry. -/
theorem push_mono {α : Type} (a : Array α) (y : α) :
    ∀ (n : Nat) (x : α), a[n]? = some x → (a.push y)[n]? = some x := fun _ _ h => get_push h

theorem rawOk_initial : RawOk initial where
  namesSize := rfl
  levelsSize := rfl
  exprsSize := rfl
  name0 i h := by
    cases i with
    | zero => rfl
    | succ k => simp [initial] at h
  name i f h := by
    cases i with
    | zero => simp [initial] at h
    | succ k => simp [initial] at h
  level0 i h := by
    cases i with
    | zero => rfl
    | succ k => simp [initial] at h
  level i f h := by
    cases i with
    | zero => simp [initial] at h
    | succ k => simp [initial] at h
  expr i f h := by simp [initial] at h

/-- `ApplySpec` keeps the raw records beside their denotation. -/
theorem rawOk_apply {t : Tables} {r : Raw} {t' : Tables} (hr : RawOk t) (h : ApplySpec t r t') :
    RawOk t' := by
  cases r with
  | name i f =>
    obtain ⟨hi, n, hn, rfl⟩ := h
    subst hi
    have hs := hr.namesSize
    refine
      { namesSize := by simp [hs]
        levelsSize := hr.levelsSize
        exprsSize := hr.exprsSize
        name0 := fun k hk => ?_
        name := fun k g hk => ?_
        level0 := hr.level0
        level := fun k g hk => ?_
        expr := fun k g hk => ?_ }
    · rw [Array.getElem?_push] at hk
      split at hk
      · cases hk
      · exact get_push (hr.name0 k hk)
    · rw [Array.getElem?_push] at hk
      split at hk
      · rename_i hk'
        subst hk'
        simp only [Option.some.injEq] at hk
        subst hk
        refine ⟨n, ?_, ?_⟩
        · show (t.names.push n)[t.rawNames.size]? = some n
          rw [hs]
          exact get_push_size _ _
        · show NameDenotes ((t.names.push n).extract 0 t.rawNames.size) f n
          rw [hs, extract_push (Nat.le_refl _), Array.extract_size]
          exact hn
      · obtain ⟨m, hm, hd⟩ := hr.name k g hk
        exact
          ⟨m, get_push hm, by
            rw [extract_push (Nat.le_of_lt (lt_of_some hm))]; exact hd⟩
    · obtain ⟨v, hv, hd⟩ := hr.level k g hk
      exact ⟨v, hv, levelDenotes_mono (push_mono _ _) hd⟩
    · obtain ⟨e, he, hd⟩ := hr.expr k g hk
      exact ⟨e, he, exprDenotes_mono (push_mono _ _) (fun _ _ h => h) hd⟩
  | level i f =>
    obtain ⟨hi, v, hv, rfl⟩ := h
    subst hi
    have hs := hr.levelsSize
    refine
      { namesSize := hr.namesSize
        levelsSize := by simp [hs]
        exprsSize := hr.exprsSize
        name0 := hr.name0
        name := hr.name
        level0 := fun k hk => ?_
        level := fun k g hk => ?_
        expr := fun k g hk => ?_ }
    · rw [Array.getElem?_push] at hk
      split at hk
      · cases hk
      · exact get_push (hr.level0 k hk)
    · rw [Array.getElem?_push] at hk
      split at hk
      · rename_i hk'
        subst hk'
        simp only [Option.some.injEq] at hk
        subst hk
        refine ⟨v, ?_, ?_⟩
        · show (t.levels.push v)[t.rawLevels.size]? = some v
          rw [hs]
          exact get_push_size _ _
        · show LevelDenotes t.names ((t.levels.push v).extract 0 t.rawLevels.size) f v
          rw [hs, extract_push (Nat.le_refl _), Array.extract_size]
          exact hv
      · obtain ⟨w, hw, hd⟩ := hr.level k g hk
        exact
          ⟨w, get_push hw, by
            rw [extract_push (Nat.le_of_lt (lt_of_some hw))]; exact hd⟩
    · obtain ⟨e, he, hd⟩ := hr.expr k g hk
      exact ⟨e, he, exprDenotes_mono (fun _ _ h => h) (push_mono _ _) hd⟩
  | expr i f =>
    obtain ⟨hi, e, he, rfl⟩ := h
    subst hi
    have hs := hr.exprsSize
    refine
      { namesSize := hr.namesSize
        levelsSize := hr.levelsSize
        exprsSize := by simp [hs]
        name0 := hr.name0
        name := hr.name
        level0 := hr.level0
        level := hr.level
        expr := fun k g hk => ?_ }
    rw [Array.getElem?_push] at hk
    split at hk
    · rename_i hk'
      subst hk'
      simp only [Option.some.injEq] at hk
      subst hk
      refine ⟨e, ?_, ?_⟩
      · show (t.exprs.push e)[t.rawExprs.size]? = some e
        rw [hs]
        exact get_push_size _ _
      · show ExprDenotes t.names t.levels ((t.exprs.push e).extract 0 t.rawExprs.size) f e
        rw [hs, extract_push (Nat.le_refl _), Array.extract_size]
        exact he
    · obtain ⟨w, hw, hd⟩ := hr.expr k g hk
      exact
        ⟨w, get_push hw, by
          rw [extract_push (Nat.le_of_lt (lt_of_some hw))]; exact hd⟩
  | decl d =>
    obtain ⟨os, _, _, _, _, rfl⟩ := h
    exact
      { namesSize := hr.namesSize
        levelsSize := hr.levelsSize
        exprsSize := hr.exprsSize
        name0 := hr.name0
        name := hr.name
        level0 := hr.level0
        level := hr.level
        expr := hr.expr }

/-- Every table a run reaches keeps its raw records beside their denotation. -/
theorem rawOk_run {g v : String} {k : Nat} {t : Tables} {ls : List (List UInt8)}
    {o : Except (Nat × Class) Tables} (h : Run g v k t ls o) :
    RawOk t → ∀ t', o = .ok t' → RawOk t' := by
  induction h with
  | noHeader => exact fun _ _ h => by cases h
  | done k t _ =>
    intro hr t' h
    cases h
    exact hr
  | json => exact fun _ _ h => by cases h
  | headerBad => exact fun _ _ h => by cases h
  | header _ _ _ _ _ _ _ _ ih => exact ih
  | recordBad => exact fun _ _ h => by cases h
  | record _ _ _ _ _ _ _ _ _ hr _ ih =>
    intro h0 t'' ho
    cases hr with
    | ok r _ _ ha => exact ih (rawOk_apply h0 ha) t'' ho

/-- On an export the reader accepts, the raw records stand beside their denotation. -/
theorem rawOk_read {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t) :
    RawOk t := rawOk_run ((read_tables g v b t).1 h) rawOk_initial t rfl

end FvdepAudit.Judge.Proof
