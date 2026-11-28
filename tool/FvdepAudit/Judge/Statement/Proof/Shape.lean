import FvdepAudit.Judge.Proof.Exprs
import FvdepAudit.Judge.Statement.Proof.Ranges

/-! Proofs: the statement step's record tests (contract `docs/contracts/U7-judge.md` S3) — on the
tables of an export the reader accepts, `constIs`, `rhsIs` + `eqParts?` read the denoted shapes, and
an alpha-equality against an application or a constant gives back the records under it. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules FvdepAudit.Export.Spec
  FvdepAudit.Judge.Statement.Spec

theorem levelEq_refl : ∀ u : Lean.Level, levelEq u u = true
  | .zero => rfl
  | .succ u => levelEq_refl u
  | .max a b => by simp [levelEq, levelEq_refl a, levelEq_refl b]
  | .imax a b => by simp [levelEq, levelEq_refl a, levelEq_refl b]
  | .param a => by simp [levelEq]
  | .mvar a => by simp [levelEq]

theorem mapM_nil_eq {α : Type} {L : Array α} :
    ∀ {us : List Nat}, us.mapM (fun i => L[i]?) = some [] → us = []
  | [], _ => rfl
  | u :: us, h => by
    rw [List.mapM_cons] at h
    cases hu : L[u]? <;> cases hm : us.mapM (fun i => L[i]?) <;> simp [hu, hm] at h

/-- An alpha-equality against an application: the record under it is an application. -/
theorem alphaEq_app_inv {t : Tables} (h : RawOk t) {i : Nat} {P f a : Lean.Expr}
    (hP : t.exprs[i]? = some P) (he : alphaEq (.app f a) P = true) :
    ∃ ig ib g b,
      t.rawExprs[i]? = some (.app ig ib) ∧
        P = .app g b ∧
        t.exprs[ig]? = some g ∧
        t.exprs[ib]? = some b ∧ alphaEq f g = true ∧ alphaEq a b = true := by
  obtain ⟨r, hr, hd⟩ := raw_of_expr h hP
  have ht := etag_denotes hd
  cases r with
  | app ig ib =>
    obtain ⟨g, b, hg, hb, rfl⟩ := hd
    rw [alphaEq_app, Bool.and_eq_true] at he
    exact ⟨ig, ib, g, b, hr, rfl, (extract_some hg).2, (extract_some hb).2, he.1, he.2⟩
  | _ =>
    exfalso
    rw [alphaEq_tag
        (by
          rw [ht]; simp [etag, ftag])
        (by simp [etag])
        (by
          rw [ht]; exact ftag_lt _)] at he
    cases he

/-- An alpha-equality against a constant: the record under it is a constant. -/
theorem alphaEq_const_inv {t : Tables} (h : RawOk t) {i : Nat} {P : Lean.Expr} {c : Lean.Name}
    {ls : List Lean.Level} (hP : t.exprs[i]? = some P) (he : alphaEq (.const c ls) P = true) :
    ∃ n us xs,
      t.rawExprs[i]? = some (.const n us) ∧
        P = .const c xs ∧
        t.names[n]? = some c ∧
        us.mapM (fun j => t.levels[j]?) = some xs ∧ levelsEq ls xs = true := by
  obtain ⟨r, hr, hd⟩ := raw_of_expr h hP
  have ht := etag_denotes hd
  cases r with
  | const n us =>
    obtain ⟨x, xs, hx, hxs, rfl⟩ := hd
    rw [alphaEq_const, Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨rfl, hl⟩ := he
    exact ⟨n, us, xs, hr, rfl, hx, hxs, hl⟩
  | _ =>
    exfalso
    rw [alphaEq_tag
        (by
          rw [ht]; simp [etag, ftag])
        (by simp [etag])
        (by
          rw [ht]; exact ftag_lt _)] at he
    cases he

theorem constIs_iff {t : Tables} (h : RawOk t) (i : Nat) (c : Lean.Name) :
    constIs t i c = true ↔ t.exprs[i]? = some (.const c []) := by
  constructor
  · intro hc
    unfold constIs at hc
    split at hc
    · rename_i n hr
      obtain ⟨e, he, hd⟩ := h.expr i _ hr
      obtain ⟨x, xs, hx, hxs, rfl⟩ := hd
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hxs
      subst hxs
      rw [beq_iff_eq, hx, Option.some.injEq] at hc
      subst hc
      exact he
    · cases hc
  · intro he
    have hz : alphaEq (.const c []) (.const c []) = true := by simp [alphaEq_const, levelsEq]
    obtain ⟨n, us, xs, hr, hxs0, hn, hus, _⟩ := alphaEq_const_inv h he hz
    simp only [Lean.Expr.const.injEq, true_and] at hxs0
    subst hxs0
    rw [mapM_nil_eq hus] at hr
    simp [constIs, hr, hn]

/-- S3's right side as a denoted expression. -/
def rhsExpr (r : Request) : Lean.Expr :=
  if r.kind = .compat then .const r.spec []
  else
    match r.abi with
    | none => .const r.spec []
    | some s => .app (.const s []) (.const r.spec [])

theorem template_eq (r : Request) (T : Lean.Expr) (u : Lean.Level) (hk : r.kind ≠ .prop) :
    template r T u = .app (.app (.app (.const `Eq [u]) T) (.const r.impl [])) (rhsExpr r) := by
  by_cases hc : r.kind = .compat <;> cases h : r.abi <;> simp [template, rhsExpr, h, hk, hc]

theorem template_prop (r : Request) (T : Lean.Expr) (u : Lean.Level) (hk : r.kind = .prop) :
    template r T u = .const r.spec [] := by simp [template, hk]

theorem rhsExpr_cases (r : Request) :
    rhsExpr r = .const r.spec [] ∨ ∃ s, rhsExpr r = .app (.const s []) (.const r.spec []) := by
  unfold rhsExpr
  by_cases hc : r.kind = .compat
  · simp [hc]
  · cases r.abi <;> simp [hc]

/-- `isProp` = the record denotes `Sort 0`. -/
theorem isProp_iff {t : Tables} (h : RawOk t) (i : Nat) :
    isProp t i = true ↔ t.exprs[i]? = some (.sort .zero) := by
  constructor
  · intro hp
    unfold isProp at hp
    split at hp
    · rename_i l hr
      split at hp
      · rename_i hl
        obtain ⟨e, he, x, hx, rfl⟩ := h.expr i _ hr
        rw [h.level0 l hl, Option.some.injEq] at hx
        subst hx
        exact he
      · cases hp
    · cases hp
  · intro hP
    obtain ⟨r, hr, hd⟩ := raw_of_expr h hP
    have ht := etag_denotes hd
    cases r with
    | sort l =>
      obtain ⟨x, hx, hxe⟩ := hd
      simp only [Lean.Expr.sort.injEq] at hxe
      subst hxe
      have hlt : l < t.rawLevels.size := by
        rw [h.levelsSize]
        exact lt_of_some hx
      cases hrl : t.rawLevels[l]? with
      | none =>
        rw [Array.getElem?_eq_none_iff] at hrl
        omega
      | some o =>
        cases o with
        | none => simp [isProp, hr, hrl]
        | some f =>
          obtain ⟨v, hv, hd'⟩ := h.level l f hrl
          rw [hx, Option.some.injEq] at hv
          subst hv
          cases f <;> simp [LevelDenotes] at hd'
    | _ => simp [etag, ftag] at ht

/-- An alpha-equality with a level-free constant: the record is that constant. -/
theorem constIs_of_alphaEq {t : Tables} (h : RawOk t) {i : Nat} {P : Lean.Expr} {c : Lean.Name}
    (hP : t.exprs[i]? = some P) (he : alphaEq (.const c []) P = true) : constIs t i c = true := by
  obtain ⟨n, us, xs, hr, rfl, hn, hus, hl⟩ := alphaEq_const_inv h hP he
  have : xs = [] := by
    cases xs with
    | nil => rfl
    | cons _ _ => simp [levelsEq] at hl
  subst this
  rw [mapM_nil_eq hus] at hr
  simp [constIs, hr, hn]

theorem rhsIs_iff {t : Tables} (h : RawOk t) (i : Nat) (r : Request) :
    rhsIs t i r = true ↔ t.exprs[i]? = some (rhsExpr r) := by
  by_cases hc : r.kind = .compat
  · simp only [rhsIs, rhsExpr, hc, beq_self_eq_true, ↓reduceIte]
    exact constIs_iff h i r.spec
  have hc' : (r.kind == .compat) = false := by simp [hc]
  cases hs : r.abi with
  | none =>
    simp only [rhsIs, rhsExpr, hs, hc, hc', Bool.false_eq_true, ↓reduceIte]
    exact constIs_iff h i r.spec
  | some s =>
    simp only [rhsIs, rhsExpr, hs, hc, hc', Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hc
      split at hc
      · rename_i g x hr
        rw [Bool.and_eq_true, constIs_iff h, constIs_iff h] at hc
        obtain ⟨e, he, hd⟩ := h.expr i _ hr
        obtain ⟨y, z, hy, hz, rfl⟩ := hd
        rw [(extract_some hy).2, Option.some.injEq] at hc
        rw [(extract_some hz).2, Option.some.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact he
      · cases hc
    · intro he
      have hz :
        alphaEq (.app (.const s []) (.const r.spec [])) (.app (.const s []) (.const r.spec [])) =
          true := by
        simp [alphaEq_app, alphaEq_const, levelsEq]
      obtain ⟨ig, ib, g, b, hr, hgb, hg, hb, _, _⟩ := alphaEq_app_inv h he hz
      simp only [Lean.Expr.app.injEq] at hgb
      obtain ⟨rfl, rfl⟩ := hgb
      simp only [hr, Bool.and_eq_true]
      exact ⟨(constIs_iff h ig s).2 hg, (constIs_iff h ib r.spec).2 hb⟩

/-- `eqParts?` = the denoted `@Eq.{u} x1 x2 x3`. -/
theorem eqParts_some {t : Tables} (h : RawOk t) {ty a1 a2 a3 : Nat} {P : Lean.Expr}
    (hP : t.exprs[ty]? = some P) (hq : eqParts? t ty = some (a1, a2, a3)) :
    ∃ u x1 x2 x3,
      P = .app (.app (.app (.const `Eq [u]) x1) x2) x3 ∧
        t.exprs[a1]? = some x1 ∧ t.exprs[a2]? = some x2 ∧ t.exprs[a3]? = some x3 := by
  unfold eqParts? at hq
  split at hq
  · rename_i f3 b3 r3
    split at hq
    · rename_i f2 b2 r2
      split at hq
      · rename_i f1 b1 r1
        split at hq
        · rename_i n l r0
          split at hq
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl, rfl⟩ := hq
            obtain ⟨e3, he3, hd3⟩ := h.expr ty _ r3
            rw [hP, Option.some.injEq] at he3
            subst he3
            obtain ⟨F2, x3, hF2, hx3, rfl⟩ := hd3
            obtain ⟨_, hF2⟩ := extract_some hF2
            obtain ⟨e2, he2, hd2⟩ := h.expr f3 _ r2
            rw [hF2, Option.some.injEq] at he2
            subst he2
            obtain ⟨F1, x2, hF1, hx2, rfl⟩ := hd2
            obtain ⟨_, hF1⟩ := extract_some hF1
            obtain ⟨e1, he1, hd1⟩ := h.expr f2 _ r1
            rw [hF1, Option.some.injEq] at he1
            subst he1
            obtain ⟨C, x1, hC, hx1, rfl⟩ := hd1
            obtain ⟨_, hC⟩ := extract_some hC
            obtain ⟨e0, he0, hd0⟩ := h.expr f1 _ r0
            rw [hC, Option.some.injEq] at he0
            subst he0
            obtain ⟨x, xs, hx, hxs, rfl⟩ := hd0
            cases hl : t.levels[l]? with
            | none => simp [List.mapM_cons, hl] at hxs
            | some v =>
              simp [List.mapM_cons, hl] at hxs
              subst hxs
              rw [beq_iff_eq, hx, Option.some.injEq] at hn
              subst hn
              exact
                ⟨v, x1, x2, x3, rfl, (extract_some hx1).2, (extract_some hx2).2,
                  (extract_some hx3).2⟩
          · cases hq
        · cases hq
      · cases hq
    · cases hq
  · cases hq

end FvdepAudit.Judge.Proof
