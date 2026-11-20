import FvdepAudit.Export.Spec

/-! Proofs: the export reader's stage 2 (contract `docs/contracts/U5b-oracle.md` X2–X4): `apply` =
`ApplySpec`, its failure class = density. -/

namespace FvdepAudit.Export.Proof

open FvdepCore.Export FvdepAudit.Export.Spec

theorem need_ok {α : Type} (w : String) (o : Option α) (x : α) : need w o = .ok x ↔ o = some x := by
  cases o <;> simp [need, bad]

theorem nameAt_ok (t : Tables) (i : Nat) (x : Lean.Name) :
    nameAt t i = .ok x ↔ t.names[i]? = some x := need_ok _ _ _

theorem levelAt_ok (t : Tables) (i : Nat) (x : Lean.Level) :
    levelAt t i = .ok x ↔ t.levels[i]? = some x := need_ok _ _ _

theorem exprAt_ok (t : Tables) (i : Nat) (x : Lean.Expr) :
    exprAt t i = .ok x ↔ t.exprs[i]? = some x := need_ok _ _ _

theorem bind_ok {α β : Type} (m : R α) (f : α → R β) (y : β) :
    (m >>= f) = .ok y ↔ ∃ x, m = .ok x ∧ f x = .ok y := by cases m <;> simp [bind, Except.bind]

theorem denoteName_ok (t : Tables) (f : NameF) (n : Lean.Name) :
    denoteName t f = .ok n ↔ NameDenotes t.names f n := by
  cases f <;> simp [denoteName, NameDenotes, bind_ok, nameAt_ok, pure, Except.pure]

theorem denoteLevel_ok (t : Tables) (f : LevelF) (v : Lean.Level) :
    denoteLevel t f = .ok v ↔ LevelDenotes t.names t.levels f v := by
  cases f <;> simp [denoteLevel, LevelDenotes, bind_ok, levelAt_ok, nameAt_ok, pure, Except.pure]

theorem mapM_levelAt_ok (t : Tables) (us : List Nat) (xs : List Lean.Level) :
    us.mapM (levelAt t) = .ok xs ↔ us.mapM (fun i => t.levels[i]?) = some xs := by
  induction us generalizing xs with
  | nil => cases xs <;> simp [pure, Except.pure]
  | cons u us ih =>
    rw [List.mapM_cons, List.mapM_cons, bind_ok]
    constructor
    · rintro ⟨a, ha, h2⟩
      rw [bind_ok] at h2
      obtain ⟨ys, hys, h3⟩ := h2
      simp only [pure, Except.pure, Except.ok.injEq] at h3
      subst h3
      rw [levelAt_ok] at ha
      rw [ih] at hys
      simp [ha, hys]
    · intro h
      cases ha : t.levels[u]? with
      | none => simp [ha] at h
      | some a =>
        cases hm : List.mapM (fun i => t.levels[i]?) us with
        | none => simp [ha, hm] at h
        | some ys =>
          simp [ha, hm] at h
          subst h
          exact ⟨a, (levelAt_ok t u a).2 ha, (bind_ok _ _ _).2 ⟨ys, (ih ys).2 hm, rfl⟩⟩

theorem denoteExpr_ok (t : Tables) (f : ExprF) (e : Lean.Expr) :
    denoteExpr t f = .ok e ↔ ExprDenotes t.names t.levels t.exprs f e := by
  cases f <;>
    simp [denoteExpr, ExprDenotes, bind_ok, nameAt_ok, levelAt_ok, exprAt_ok, mapM_levelAt_ok, pure,
      Except.pure]

theorem mapM_need_ok {α : Type} (w : Nat → String) (arr : Array α) (xs : List Nat) (ys : List α) :
    xs.mapM (fun i => need (w i) arr[i]?) = .ok ys ↔ xs.mapM (fun i => arr[i]?) = some ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [pure, Except.pure]
  | cons u us ih =>
    rw [List.mapM_cons, List.mapM_cons, bind_ok]
    constructor
    · rintro ⟨a, ha, h2⟩
      rw [bind_ok] at h2
      obtain ⟨zs, hzs, h3⟩ := h2
      simp only [pure, Except.pure, Except.ok.injEq] at h3
      subst h3
      rw [need_ok] at ha
      rw [ih] at hzs
      simp [ha, hzs]
    · intro h
      cases ha : arr[u]? with
      | none => simp [ha] at h
      | some a =>
        cases hm : List.mapM (fun i => arr[i]?) us with
        | none => simp [ha, hm] at h
        | some zs =>
          simp [ha, hm] at h
          subst h
          exact ⟨a, rfl, (bind_ok _ _ _).2 ⟨zs, (ih zs).2 hm, rfl⟩⟩

theorem mapM_isSome {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.mapM f).isSome ↔ ∀ x ∈ xs, (f x).isSome := by
  induction xs with
  | nil => simp [pure]
  | cons x xs ih => cases h : f x <;> cases hm : xs.mapM f <;> simp_all [List.mapM_cons]

theorem discard_ok {α : Type} (m : R α) : discard m = .ok () ↔ ∃ x, m = .ok x := by
  cases m <;> simp [discard, Functor.mapConst, Except.map]

theorem mapM_nameAt_isOk (t : Tables) (xs : List Nat) :
    (∃ ys, xs.mapM (nameAt t) = .ok ys) ↔ ∀ n ∈ xs, (t.names[n]?).isSome := by
  have h := fun ys => mapM_need_ok (fun i => s!"name {i} (unbound)") t.names xs ys
  rw [← mapM_isSome (fun i => t.names[i]?) xs, Option.isSome_iff_exists]
  exact ⟨fun ⟨ys, hy⟩ => ⟨ys, (h ys).1 hy⟩, fun ⟨ys, hy⟩ => ⟨ys, (h ys).2 hy⟩⟩

theorem mapM_exprAt_isOk (t : Tables) (xs : List Nat) :
    (∃ ys, xs.mapM (exprAt t) = .ok ys) ↔ ∀ n ∈ xs, (t.exprs[n]?).isSome := by
  have h := fun ys => mapM_need_ok (fun i => s!"expression {i} (unbound)") t.exprs xs ys
  rw [← mapM_isSome (fun i => t.exprs[i]?) xs, Option.isSome_iff_exists]
  exact ⟨fun ⟨ys, hy⟩ => ⟨ys, (h ys).1 hy⟩, fun ⟨ys, hy⟩ => ⟨ys, (h ys).2 hy⟩⟩

theorem mapM_nameAt_ok (t : Tables) (xs : List Nat) (ys : List Lean.Name) :
    xs.mapM (nameAt t) = .ok ys ↔ xs.mapM (fun i => t.names[i]?) = some ys :=
  mapM_need_ok (fun i => s!"name {i} (unbound)") t.names xs ys

theorem optExpr_ok (t : Tables) (v : Option Nat) (w : Option Lean.Expr) :
    optExpr t v = .ok w ↔
      (match v with
      | none => w = none
      | some i => ∃ y, t.exprs[i]? = some y ∧ w = some y) := by
  cases v with
  | none => simp [optExpr, pure, Except.pure, eq_comm]
  | some i =>
    simp only [optExpr, bind_ok, exprAt_ok, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩

theorem denoteItem_ok (t : Tables) (d : Item) (o : Decl) :
    denoteItem t d = .ok o ↔ DeclDenotes t d o := by
  rcases o with ⟨name, kind, lps, ty, value⟩
  simp only [denoteItem, DeclDenotes, bind_ok, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨u1, h1, u2, h2, x, hx, y, hy, z, hz, w, hw, he⟩
    simp only [Decl.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    refine
      ⟨(mapM_nameAt_isOk t d.names).1 ?_, (mapM_exprAt_isOk t d.exprs).1 ?_, (nameAt_ok t _ _).1 hx,
        rfl, (mapM_nameAt_ok t _ _).1 hy, (exprAt_ok t _ _).1 hz, (optExpr_ok t _ _).1 hw⟩
    · exact
        (discard_ok _).1
          (by
            cases u1; exact h1)
    · exact
        (discard_ok _).1
          (by
            cases u2; exact h2)
  · rintro ⟨hn, he, hx, hk, hy, hz, hw⟩
    obtain ⟨ns, hns⟩ := (mapM_nameAt_isOk t d.names).2 hn
    obtain ⟨es, hes⟩ := (mapM_exprAt_isOk t d.exprs).2 he
    cases hv : d.value with
    | none =>
      rw [hv] at hw
      refine
        ⟨(), (discard_ok _).2 ⟨ns, hns⟩, (), (discard_ok _).2 ⟨es, hes⟩, name,
          (nameAt_ok t _ _).2 hx, lps, (mapM_nameAt_ok t _ _).2 hy, ty, (exprAt_ok t _ _).2 hz,
          none, ?_, ?_⟩
      · simp [optExpr, pure, Except.pure]
      · simp [hk, hw]
    | some i =>
      rw [hv] at hw
      obtain ⟨y, hy', rfl⟩ := hw
      refine
        ⟨(), (discard_ok _).2 ⟨ns, hns⟩, (), (discard_ok _).2 ⟨es, hes⟩, name,
          (nameAt_ok t _ _).2 hx, lps, (mapM_nameAt_ok t _ _).2 hy, ty, (exprAt_ok t _ _).2 hz,
          some y, (optExpr_ok t _ _).2 ⟨y, hy', rfl⟩, ?_⟩
      simp [hk]

theorem fresh_ok (tbl : String) (n i : Nat) : fresh tbl n i = .ok () ↔ i = n := by
  unfold fresh
  by_cases h : i = n
  · simp [h, pure, Except.pure]
  · simp [h, outside]

theorem addNames_ok (seen : List Lean.Name) (ds : List Decl) (s' : List Lean.Name) :
    addNames seen ds = .ok s' ↔
      (ds.map (·.name)).Nodup ∧
        (∀ d ∈ ds, d.name ∉ seen) ∧ s' = (ds.map (·.name)).reverse ++ seen := by
  induction ds generalizing seen with
  | nil => simp [addNames, eq_comm]
  | cons d ds ih =>
    unfold addNames
    by_cases h : d.name ∈ seen
    · simp [h, bad]
    · simp only [h, ite_false, ih, List.map_cons, List.nodup_cons, List.mem_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
      constructor
      · rintro ⟨hn, hs, rfl⟩
        refine ⟨⟨fun hm => ?_, hn⟩, ?_, rfl⟩
        · obtain ⟨e, he, hne⟩ := List.mem_map.1 hm
          exact hs e he (by simp [hne])
        · intro e he
          rcases he with rfl | he
          · exact h
          · exact fun hm => hs e he (by simp [hm])
      · rintro ⟨⟨hn, hd⟩, hs, rfl⟩
        refine ⟨hd, fun e he hm => ?_, rfl⟩
        rcases hm with heq | hm
        · exact hn (List.mem_map.2 ⟨e, he, heq⟩)
        · exact hs e (Or.inr he) hm

theorem mapM_denoteItem_ok (t : Tables) (ds : List Item) (os : List Decl) :
    ds.mapM (denoteItem t) = .ok os ↔
      ds.length = os.length ∧ ∀ p ∈ ds.zip os, DeclDenotes t p.1 p.2 := by
  induction ds generalizing os with
  | nil => cases os <;> simp [pure, Except.pure]
  | cons d ds ih =>
    rw [List.mapM_cons, bind_ok]
    constructor
    · rintro ⟨o, ho, h2⟩
      rw [bind_ok] at h2
      obtain ⟨os', hos, h3⟩ := h2
      simp only [pure, Except.pure, Except.ok.injEq] at h3
      subst h3
      obtain ⟨hl, hp⟩ := (ih os').1 hos
      refine ⟨by simp [hl], ?_⟩
      intro p hp'
      simp only [List.zip_cons_cons, List.mem_cons] at hp'
      rcases hp' with rfl | hp'
      · exact (denoteItem_ok t d o).1 ho
      · exact hp p hp'
    · rintro ⟨hl, hp⟩
      cases os with
      | nil => simp at hl
      | cons o os =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hp
        refine ⟨o, (denoteItem_ok t d o).2 hp.1, (bind_ok _ _ _).2 ⟨os, (ih os).2 ⟨hl, hp.2⟩, rfl⟩⟩

/-- The shipped record split = the spec's. -/
theorem items_eq (d : DeclF) : items d = itemsOf d := by cases d <;> rfl

theorem apply_ok (t : Tables) (r : Raw) (t' : Tables) : apply t r = .ok t' ↔ ApplySpec t r t' := by
  cases r with
  | name i
    f =>
    simp only [apply, ApplySpec, bind_ok, denoteName_ok, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro ⟨u, hu, n, hn, rfl⟩
      cases u
      exact ⟨(fresh_ok _ _ _).1 hu, n, hn, rfl⟩
    · rintro ⟨hu, n, hn, rfl⟩
      exact ⟨(), (fresh_ok _ _ _).2 hu, n, hn, rfl⟩
  | level i
    f =>
    simp only [apply, ApplySpec, bind_ok, denoteLevel_ok, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro ⟨u, hu, n, hn, rfl⟩
      cases u
      exact ⟨(fresh_ok _ _ _).1 hu, n, hn, rfl⟩
    · rintro ⟨hu, n, hn, rfl⟩
      exact ⟨(), (fresh_ok _ _ _).2 hu, n, hn, rfl⟩
  | expr i
    f =>
    simp only [apply, ApplySpec, bind_ok, denoteExpr_ok, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro ⟨u, hu, n, hn, rfl⟩
      cases u
      exact ⟨(fresh_ok _ _ _).1 hu, n, hn, rfl⟩
    · rintro ⟨hu, n, hn, rfl⟩
      exact ⟨(), (fresh_ok _ _ _).2 hu, n, hn, rfl⟩
  | decl
    d =>
    simp only [apply, ApplySpec, bind_ok, items_eq, mapM_denoteItem_ok, addNames_ok, pure,
      Except.pure, Except.ok.injEq]
    constructor
    · rintro ⟨os, ⟨hl, hp⟩, s, ⟨hn, hs, rfl⟩, rfl⟩
      exact ⟨os, hl, hp, hn, hs, rfl⟩
    · rintro ⟨os, hl, hp, hn, hs, rfl⟩
      exact ⟨os, ⟨hl, hp⟩, _, ⟨hn, hs, rfl⟩, rfl⟩

/-! ## Failure classes: density alone is outside the profile -/

theorem bind_error {α β : Type} (m : R α) (f : α → R β) (e : Class × String) :
    (m >>= f) = .error e ↔ m = .error e ∨ ∃ x, m = .ok x ∧ f x = .error e := by
  cases m <;> simp [bind, Except.bind]

/-- Every failure of `m` is malformed. -/
def OnlyBad {α : Type} (m : R α) : Prop := ∀ c w, m = .error (c, w) → c = .malformed

theorem onlyBad_bind {α β : Type} {m : R α} {f : α → R β} (hm : OnlyBad m)
    (hf : ∀ x, OnlyBad (f x)) : OnlyBad (m >>= f) := by
  intro c w h
  rcases (bind_error m f (c, w)).1 h with h | ⟨x, _, h⟩
  · exact hm c w h
  · exact hf x c w h

theorem onlyBad_pure {α : Type} (x : α) : OnlyBad (pure x : R α) := by
  intro c w h
  simp [pure, Except.pure] at h

theorem onlyBad_need {α : Type} (what : String) (o : Option α) : OnlyBad (need what o) := by
  intro c w h
  cases o with
  | none =>
    simp only [need, bad, Except.error.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | some x => simp [need] at h

theorem onlyBad_mapM {α β : Type} (f : α → R β) (hf : ∀ x, OnlyBad (f x)) :
    ∀ xs : List α, OnlyBad (xs.mapM f)
  | [] => onlyBad_pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact onlyBad_bind (hf x) fun _ => onlyBad_bind (onlyBad_mapM f hf xs) fun _ => onlyBad_pure _

theorem onlyBad_discard {α : Type} {m : R α} (hm : OnlyBad m) : OnlyBad (discard m) := by
  intro c w h
  cases hx : m with
  | error e =>
    rw [hx] at h
    have h' : (Except.error e : R Unit) = .error (c, w) := h
    exact hm c w (by rw [hx, Except.error.inj h'])
  | ok x =>
    rw [hx] at h
    cases h

theorem onlyBad_nameAt (t : Tables) (i : Nat) : OnlyBad (nameAt t i) := onlyBad_need _ _

theorem onlyBad_levelAt (t : Tables) (i : Nat) : OnlyBad (levelAt t i) := onlyBad_need _ _

theorem onlyBad_exprAt (t : Tables) (i : Nat) : OnlyBad (exprAt t i) := onlyBad_need _ _

theorem onlyBad_denoteName (t : Tables) : ∀ f, OnlyBad (denoteName t f)
  | .str pre _ => onlyBad_bind (onlyBad_nameAt t pre) fun _ => onlyBad_pure _
  | .num pre _ => onlyBad_bind (onlyBad_nameAt t pre) fun _ => onlyBad_pure _

theorem onlyBad_denoteLevel (t : Tables) : ∀ f, OnlyBad (denoteLevel t f)
  | .succ l => onlyBad_bind (onlyBad_levelAt t l) fun _ => onlyBad_pure _
  | .max a b =>
    onlyBad_bind (onlyBad_levelAt t a) fun _ =>
      onlyBad_bind (onlyBad_levelAt t b) fun _ => onlyBad_pure _
  | .imax a b =>
    onlyBad_bind (onlyBad_levelAt t a) fun _ =>
      onlyBad_bind (onlyBad_levelAt t b) fun _ => onlyBad_pure _
  | .param n => onlyBad_bind (onlyBad_nameAt t n) fun _ => onlyBad_pure _

theorem onlyBad_denoteExpr (t : Tables) : ∀ f, OnlyBad (denoteExpr t f)
  | .bvar _ => onlyBad_pure _
  | .sort l => onlyBad_bind (onlyBad_levelAt t l) fun _ => onlyBad_pure _
  | .const n us =>
    onlyBad_bind (onlyBad_nameAt t n) fun _ =>
      onlyBad_bind (onlyBad_mapM _ (onlyBad_levelAt t) us) fun _ => onlyBad_pure _
  | .app f a =>
    onlyBad_bind (onlyBad_exprAt t f) fun _ =>
      onlyBad_bind (onlyBad_exprAt t a) fun _ => onlyBad_pure _
  | .lam n ty b _ =>
    onlyBad_bind (onlyBad_nameAt t n) fun _ =>
      onlyBad_bind (onlyBad_exprAt t ty) fun _ =>
        onlyBad_bind (onlyBad_exprAt t b) fun _ => onlyBad_pure _
  | .forallE n ty b _ =>
    onlyBad_bind (onlyBad_nameAt t n) fun _ =>
      onlyBad_bind (onlyBad_exprAt t ty) fun _ =>
        onlyBad_bind (onlyBad_exprAt t b) fun _ => onlyBad_pure _
  | .letE n ty v b _ =>
    onlyBad_bind (onlyBad_nameAt t n) fun _ =>
      onlyBad_bind (onlyBad_exprAt t ty) fun _ =>
        onlyBad_bind (onlyBad_exprAt t v) fun _ =>
          onlyBad_bind (onlyBad_exprAt t b) fun _ => onlyBad_pure _
  | .proj tn _ st =>
    onlyBad_bind (onlyBad_nameAt t tn) fun _ =>
      onlyBad_bind (onlyBad_exprAt t st) fun _ => onlyBad_pure _
  | .natVal _ => onlyBad_pure _
  | .strVal _ => onlyBad_pure _

theorem onlyBad_optExpr (t : Tables) : ∀ v, OnlyBad (optExpr t v)
  | none => onlyBad_pure _
  | some i => onlyBad_bind (onlyBad_exprAt t i) fun _ => onlyBad_pure _

theorem onlyBad_denoteItem (t : Tables) (d : Item) : OnlyBad (denoteItem t d) :=
  onlyBad_bind (onlyBad_discard (onlyBad_mapM _ (onlyBad_nameAt t) d.names)) fun _ =>
    onlyBad_bind (onlyBad_discard (onlyBad_mapM _ (onlyBad_exprAt t) d.exprs)) fun _ =>
      onlyBad_bind (onlyBad_nameAt t d.name) fun _ =>
        onlyBad_bind (onlyBad_mapM _ (onlyBad_nameAt t) d.levelParams) fun _ =>
          onlyBad_bind (onlyBad_exprAt t d.type) fun _ =>
            onlyBad_bind (onlyBad_optExpr t d.value) fun _ => onlyBad_pure _

theorem onlyBad_addNames : ∀ (seen : List Lean.Name) (ds : List Decl), OnlyBad (addNames seen ds)
  | _, [] => by
    intro c w h
    simp [addNames] at h
  | seen, d :: ds => by
    intro c w h
    unfold addNames at h
    split at h
    · simp only [bad, Except.error.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · exact onlyBad_addNames _ ds c w h

theorem fresh_error (tbl : String) (n i : Nat) (c : Class) (w : String)
    (h : fresh tbl n i = .error (c, w)) : c = .profile ∧ i ≠ n := by
  unfold fresh at h
  by_cases hi : i = n
  · simp [hi, pure, Except.pure] at h
  · simp only [hi, beq_iff_eq, ite_false, outside, Except.error.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, hi⟩

/-- Stage 2's failure class: outside the profile exactly when the record is not dense. -/
theorem apply_class (t : Tables) (r : Raw) (c : Class) (w : String)
    (h : apply t r = .error (c, w)) : c = .profile ↔ ¬Dense t r := by
  cases r with
  | name i f =>
    simp only [apply, bind_error] at h
    rcases h with h | ⟨u, hu, h | ⟨x, _, h⟩⟩
    · obtain ⟨rfl, hi⟩ := fresh_error _ _ _ _ _ h
      simp [Dense, hi]
    · have hi :=
        (fresh_ok _ _ _).1
          (by
            cases u; exact hu)
      simp [Dense, hi, onlyBad_denoteName t f c w h]
    · simp [pure, Except.pure] at h
  | level i f =>
    simp only [apply, bind_error] at h
    rcases h with h | ⟨u, hu, h | ⟨x, _, h⟩⟩
    · obtain ⟨rfl, hi⟩ := fresh_error _ _ _ _ _ h
      simp [Dense, hi]
    · have hi :=
        (fresh_ok _ _ _).1
          (by
            cases u; exact hu)
      simp [Dense, hi, onlyBad_denoteLevel t f c w h]
    · simp [pure, Except.pure] at h
  | expr i f =>
    simp only [apply, bind_error] at h
    rcases h with h | ⟨u, hu, h | ⟨x, _, h⟩⟩
    · obtain ⟨rfl, hi⟩ := fresh_error _ _ _ _ _ h
      simp [Dense, hi]
    · have hi :=
        (fresh_ok _ _ _).1
          (by
            cases u; exact hu)
      simp [Dense, hi, onlyBad_denoteExpr t f c w h]
    · simp [pure, Except.pure] at h
  | decl d =>
    simp only [apply, bind_error] at h
    rcases h with h | ⟨ds, _, h | ⟨x, _, h⟩⟩
    · simp [Dense, onlyBad_mapM _ (onlyBad_denoteItem t) (items d) c w h]
    · simp [Dense, onlyBad_addNames t.declared ds c w h]
    · simp [pure, Except.pure] at h

end FvdepAudit.Export.Proof
