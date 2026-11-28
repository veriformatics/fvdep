import FvdepAudit.Judge.Proof
import FvdepAudit.Judge.Proof.View
import FvdepAudit.Judge.Statement.Proof.Shape

/-! Proofs: the statement step (contract `docs/contracts/U7-judge.md` S1–S4) — on two exports the
reader accepts: an infrastructure outcome exactly when the trusted side lacks the target type,
`.matched` ⇒ the template holds (the memo kept sound), and when it holds the step fails only by
exhausting its budget. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules FvdepAudit.Export.Spec
  FvdepAudit.Judge.Spec FvdepAudit.Judge.Statement.Spec

theorem byName_none {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    (n : Lean.Name) : (viewOf t).byName[n]? = none ↔ ∀ e, ¬Named t n e := by
  constructor
  · intro hn e he
    rw [(viewOf_get h n e).2 he] at hn
    cases hn
  · intro hn
    cases hg : (viewOf t).byName[n]? with
    | none => rfl
    | some e => exact absurd ((viewOf_get h n e).1 hg) (hn e)

theorem named_unique {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {n : Lean.Name} {e e' : Entry} (he : Named t n e) (he' : Named t n e') : e = e' := by
  have h1 := (viewOf_get h n e).2 he
  rw [(viewOf_get h n e').2 he', Option.some.injEq] at h1
  exact h1.symm

theorem safeType_some {e : Entry} {ty : Nat} :
    safeType? (some e) = some ty ↔ ∃ all hn i v, e = .defn all hn [] i .safe ty v := by
  constructor
  · intro hs
    unfold safeType? at hs
    split at hs
    · rename_i all hn i ty' v he
      simp only [Option.some.injEq] at he hs
      subst he hs
      exact ⟨all, hn, i, v, rfl⟩
    · cases hs
  · rintro ⟨all, hn, i, v, rfl⟩
    rfl

/-- `SafeDefn` through the index. -/
theorem safeDefn_iff {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    (n : Lean.Name) (T : Lean.Expr) :
    SafeDefn t n T ↔
      ∃ e ty,
        (viewOf t).byName[n]? = some e ∧ safeType? (some e) = some ty ∧ t.exprs[ty]? = some T := by
  constructor
  · rintro ⟨all, hn, i, ty, val, hN, hT⟩
    exact ⟨_, ty, (viewOf_get h n _).2 hN, rfl, hT⟩
  · rintro ⟨e, ty, hg, hs, hT⟩
    obtain ⟨all, hn, i, val, rfl⟩ := safeType_some.1 hs
    exact ⟨all, hn, i, ty, val, (viewOf_get h n _).1 hg, hT⟩

theorem safeDefn_unique {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {n : Lean.Name} {T T' : Lean.Expr} (h1 : SafeDefn t n T) (h2 : SafeDefn t n T') : T = T' := by
  obtain ⟨e, ty, hg, hs, hT⟩ := (safeDefn_iff h n T).1 h1
  obtain ⟨e', ty', hg', hs', hT'⟩ := (safeDefn_iff h n T').1 h2
  rw [hg, Option.some.injEq] at hg'
  subst hg'
  rw [hs, Option.some.injEq] at hs'
  subst hs'
  rw [hT, Option.some.injEq] at hT'
  exact hT'

/-- A named constant's type is bound. -/
theorem named_typed {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {n : Lean.Name} {e : Entry} (hN : Named t n e) : ∃ T, t.exprs[entryType e]? = some T :=
  Option.isSome_iff_exists.1 (entriesOk_typed (entriesOk_read h) e (named_iff.1 hN).1)

/-- The shape test of `target`: an ABI shape's index + its codomain's. -/
theorem shape_some {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {s : Lean.Name} {e : Entry} {bi : Nat} (he : (viewOf t).byName[s]? = some e)
    (hc : (safeType? (some e) >>= arrowCodomain? (viewOf t).t) = some bi) :
    ∃ n A B bnd,
      SafeDefn t s (.forallE n A B bnd) ∧ Closed A 0 ∧ Closed B 0 ∧ t.exprs[bi]? = some B := by
  cases hs : safeType? (some e) with
  | none => simp [hs] at hc
  | some
    sty =>
    have ha : arrowCodomain? t sty = some bi := by
      have h' := hc
      simp only [hs] at h'
      exact h'
    obtain ⟨all, hn, i, val, rfl⟩ := safeType_some.1 hs
    have hN := (viewOf_get h s _).1 he
    obtain ⟨S, hS⟩ := named_typed h hN
    obtain ⟨n, A, B, bnd, rfl, hA, hB, hb⟩ := arrowCodomain_some (rawOk_read h) hS ha
    exact ⟨n, A, B, bnd, ⟨all, hn, i, sty, val, hN, hS⟩, hA, hB, hb⟩

/-- The trusted side's test: `.ok` names the target type's index. -/
theorem target_ok {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {tT : Nat} (hk : r.kind = .eq) (ht : target (viewOf t) r = .ok tT) :
    ∃ T, t.exprs[tT]? = some T ∧ Target t r T := by
  unfold target at ht
  split at ht
  · cases ht
  · rename_i e he
    split at ht
    · cases ht
    · rename_i specTy hs
      obtain ⟨all, hn, i, val, rfl⟩ := safeType_some.1 hs
      have hN := (viewOf_get h r.spec _).1 he
      obtain ⟨S, hS⟩ := named_typed h hN
      have hspec : SafeDefn t r.spec S := ⟨all, hn, i, specTy, val, hN, hS⟩
      cases hab : r.abi with
      | none =>
        simp only [hab, Except.ok.injEq] at ht
        subst ht
        exact
          ⟨S, hS, by
            simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab]; exact hspec⟩
      | some s =>
        simp only [hab] at ht
        split at ht
        · cases ht
        · rename_i e' he'
          split at ht
          · cases ht
          · rename_i bi hc
            simp only [Except.ok.injEq] at ht
            subst ht
            obtain ⟨n, A, B, bnd, hsd, hA, hB, hb⟩ := shape_some h he' hc
            exact
              ⟨B, hb, by
                simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab]
                exact ⟨⟨S, hspec⟩, n, A, bnd, hsd, hA, hB⟩⟩

/-- The trusted side's test: `.error` ⇒ no target type. -/
theorem target_error {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {w : String} (hk : r.kind = .eq) (ht : target (viewOf t) r = .error w) :
    ¬∃ T, Target t r T := by
  have spec_of : ∀ T, Target t r T → ∃ S, SafeDefn t r.spec S := by
    intro T hT
    cases hab : r.abi with
    | none =>
      simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab] at hT; exact ⟨T, hT⟩
    | some s =>
      simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab] at hT; exact hT.1
  rintro ⟨T, hT⟩
  obtain ⟨S, hS⟩ := spec_of T hT
  obtain ⟨e, sty, hg, hs, _⟩ := (safeDefn_iff h _ _).1 hS
  unfold target at ht
  rw [hg] at ht
  simp only [hs] at ht
  cases hab : r.abi with
  | none =>
    simp only [hab] at ht
    cases ht
  | some s =>
    simp only [hab] at ht
    simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab] at hT
    obtain ⟨_, n, A, bnd, hsd, hA, hB⟩ := hT
    obtain ⟨e', sty', hg', hs', hS'⟩ := (safeDefn_iff h _ _).1 hsd
    rw [hg'] at ht
    simp only [hs'] at ht
    split at ht
    · rename_i hc
      exact arrowCodomain_none (rawOk_read h) hS' hc ⟨n, A, T, bnd, rfl, hA, hB⟩
    · cases ht

theorem target_unique {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {T T' : Lean.Expr} (h1 : Target t r T) (h2 : Target t r T') : T = T' := by
  by_cases hp : r.kind = .prop
  · simp only [Target, hp, ↓reduceIte] at h1 h2
    exact safeDefn_unique h h1.1 h2.1
  by_cases hc : r.kind = .compat
  · simp only [Target, hc, ↓reduceIte, reduceCtorEq] at h1 h2
    exact safeDefn_unique h h1.1 h2.1
  have hk : r.kind = .eq := by cases hk2 : r.kind <;> simp_all
  cases hab : r.abi with
  | none =>
    simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab] at h1 h2
    exact safeDefn_unique h h1 h2
  | some s =>
    simp only [Target, hk, reduceCtorEq, ↓reduceIte, hab] at h1 h2
    obtain ⟨_, n, A, bnd, hs1, _, _⟩ := h1
    obtain ⟨_, n', A', bnd', hs2, _, _⟩ := h2
    have := safeDefn_unique h hs1 hs2
    simp only [Lean.Expr.forallE.injEq] at this
    exact this.2.2.1

theorem mapM_length {α : Type} {L : Array α} :
    ∀ {us : List Nat} {xs : List α}, us.mapM (fun i => L[i]?) = some xs → xs.length = us.length
  | [], xs, h => by
    simp at h; subst h; rfl
  | u :: us, xs, h => by
    rw [List.mapM_cons] at h
    cases hu : L[u]? with
    | none => simp [hu] at h
    | some a =>
      cases hm : us.mapM (fun i => L[i]?) with
      | none => simp [hu, hm] at h
      | some ys =>
        simp [hu, hm] at h
        subst h
        simp [mapM_length hm]

/-- An alpha-equality with the template gives back the records `statement` tests. -/
theorem template_inv {t : Tables} (h : RawOk t) {ty : Nat} {P : Lean.Expr}
    (hP : t.exprs[ty]? = some P) {r : Request} {T : Lean.Expr} {u : Lean.Level}
    (hk : r.kind ≠ .prop) (he : alphaEq (template r T u) P = true) :
    ∃ a1 a2 a3 x1,
      eqParts? t ty = some (a1, a2, a3) ∧
        t.exprs[a1]? = some x1 ∧
        alphaEq T x1 = true ∧ constIs t a2 r.impl = true ∧ rhsIs t a3 r = true := by
  rw [template_eq r T u hk] at he
  obtain ⟨i3, b3, g3, x3, r3, rfl, hg3, hx3, he3, hR⟩ := alphaEq_app_inv h hP he
  obtain ⟨i2, b2, g2, x2, r2, rfl, hg2, hx2, he2, hI⟩ := alphaEq_app_inv h hg3 he3
  obtain ⟨i1, b1, g1, x1, r1, rfl, hg1, hx1, he1, hT⟩ := alphaEq_app_inv h hg2 he2
  obtain ⟨n, us, xs, r0, rfl, hn, hus, hl⟩ := alphaEq_const_inv h hg1 he1
  obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
    match xs, hl with
    | [x], _ => exact ⟨x, rfl⟩
    | [], hl => simp [levelsEq] at hl
    | _ :: _ :: _, hl => simp [levelsEq] at hl
  obtain ⟨l, rfl⟩ : ∃ l, us = [l] := by
    have hlen := mapM_length hus
    match us, hlen with
    | [l], _ => exact ⟨l, rfl⟩
    | [], hlen => simp at hlen
    | _ :: _ :: _, hlen => simp at hlen
  have hq : eqParts? t ty = some (b1, b2, b3) := by simp [eqParts?, r3, r2, r1, r0, hn]
  refine ⟨b1, b2, b3, x1, hq, hx1, hT, ?_, ?_⟩
  · obtain ⟨_, _, xs2, _, hxe, _, _, hl2⟩ := alphaEq_const_inv h hx2 hI
    have : xs2 = [] := by
      cases xs2 with
      | nil => rfl
      | cons _ _ => simp [levelsEq] at hl2
    rw [hxe, this] at hx2
    exact (constIs_iff h b2 r.impl).2 hx2
  · rw [rhsIs_iff h b3 r]
    rcases rhsExpr_cases r with hre | ⟨s, hre⟩
    · rw [hre] at hR ⊢
      obtain ⟨_, _, xs3, _, hxe, _, _, hl3⟩ := alphaEq_const_inv h hx3 hR
      have : xs3 = [] := by
        cases xs3 with
        | nil => rfl
        | cons _ _ => simp [levelsEq] at hl3
      rw [hxe, this] at hx3
      exact hx3
    · rw [hre] at hR ⊢
      obtain ⟨_, _, gs, xsp, _, hxe, hgs, hxsp, hes, hesp⟩ := alphaEq_app_inv h hx3 hR
      obtain ⟨_, _, ls1, _, hge, _, _, hl4⟩ := alphaEq_const_inv h hgs hes
      obtain ⟨_, _, ls2, _, hpe, _, _, hl5⟩ := alphaEq_const_inv h hxsp hesp
      have h1 : ls1 = [] := by
        cases ls1 with
        | nil => rfl
        | cons _ _ => simp [levelsEq] at hl4
      have h2 : ls2 = [] := by
        cases ls2 with
        | nil => rfl
        | cons _ _ => simp [levelsEq] at hl5
      rw [hxe, hge, hpe, h1, h2] at hx3
      exact hx3

theorem alphaEq_const_refl (c : Lean.Name) : alphaEq (.const c []) (.const c []) = true := by
  simp [alphaEq_const, levelsEq]

theorem alphaEq_rhs_refl (r : Request) : alphaEq (rhsExpr r) (rhsExpr r) = true := by
  rcases rhsExpr_cases r with h | ⟨s, h⟩ <;> rw [h] <;> simp [alphaEq_app, alphaEq_const, levelsEq]

theorem viewOf_t (t : Tables) : (viewOf t).t = t := rfl

theorem thmOf_some {e : Entry} {lps : List Nat} {ty : Nat} :
    thmOf? e = some (lps, ty) ↔ ∃ all i v, e = .thm all lps i ty v := by
  constructor
  · intro h
    cases e <;> simp [thmOf?] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, _, rfl⟩
  · rintro ⟨all, i, v, rfl⟩
    rfl

theorem thmOf_none {e : Entry} (h : thmOf? e = none) :
    ∀ all lps i ty v, e ≠ .thm all lps i ty v := by
  intro all lps i ty v he
  subst he
  simp [thmOf?] at h

/-- A target type ⇒ S4's trusted data. -/
theorem trusted_of_target {t : Tables} {r : Request} {T : Lean.Expr} (hT : Target t r T) :
    Trusted t r := by
  by_cases hk : r.kind = .eq
  · simp only [Trusted, hk, ↓reduceIte]
    exact ⟨T, hT⟩
  · simp only [Trusted, hk, ↓reduceIte]
    by_cases hp : r.kind = .prop
    · simp only [Target, hp, ↓reduceIte] at hT
      obtain ⟨⟨_, _, _, _, _, hN, _⟩, _⟩ := hT
      exact
        ⟨⟨_, hN⟩, fun hc => by
          rw [hp] at hc; cases hc⟩
    · have hc : r.kind = .compat := by cases hk2 : r.kind <;> simp_all
      simp only [Target, hc, ↓reduceIte, reduceCtorEq] at hT
      obtain ⟨⟨_, _, _, _, _, hN, _⟩, _, _, _, _, _, _, hN', _⟩ := hT
      exact ⟨⟨_, hN'⟩, fun _ => ⟨_, hN⟩⟩

/-- Part B's roots: `.ok` names the target type's index. -/
theorem roots_ok {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {tT : Nat} (hk : r.kind ≠ .eq) (ht : roots (viewOf t) r = .ok tT) :
    ∃ T, t.exprs[tT]? = some T ∧ Target t r T := by
  unfold roots at ht
  by_cases hp : r.kind = .prop
  · have hp' : (r.kind == .prop) = true := by simp [hp]
    simp only [hp', ↓reduceIte] at ht
    cases he : (viewOf t).byName[r.spec]? with
    | none =>
      simp only [he] at ht; cases ht
    | some e =>
      simp only [he] at ht
      cases hs : safeType? (some e) with
      | none =>
        simp only [hs] at ht; cases ht
      | some specTy =>
        simp only [hs] at ht
        by_cases hprop : isProp (viewOf t).t specTy = true
        · simp only [hprop, ↓reduceIte, Except.ok.injEq] at ht
          subst ht
          obtain ⟨all, hn, i, val, rfl⟩ := safeType_some.1 hs
          have hN := (viewOf_get h r.spec _).1 he
          obtain ⟨S, hS⟩ := named_typed h hN
          have hx := (isProp_iff (rawOk_read h) _).1 hprop
          have hS' : t.exprs[specTy]? = some S := hS
          rw [hS', Option.some.injEq] at hx
          subst hx
          refine ⟨_, hS, ?_⟩
          simp only [Target, hp, ↓reduceIte]
          exact ⟨⟨all, hn, i, specTy, val, hN, hS⟩, trivial⟩
        · have hpf : isProp (viewOf t).t specTy = false := by simpa using hprop
          simp only [hpf, Bool.false_eq_true, ↓reduceIte] at ht
          cases ht
  · have hp' : (r.kind == .prop) = false := by simp [hp]
    have hc : r.kind = .compat := by cases hk2 : r.kind <;> simp_all
    simp only [hp', Bool.false_eq_true, ↓reduceIte] at ht
    cases hen : (viewOf t).byName[r.impl]? with
    | none =>
      simp only [hen] at ht; cases ht
    | some en =>
      simp only [hen] at ht
      cases heo : (viewOf t).byName[r.spec]? with
      | none =>
        simp only [heo] at ht; cases ht
      | some eo =>
        simp only [heo] at ht
        cases hs' : safeType? (some en) with
        | none =>
          simp only [hs'] at ht; cases ht
        | some newTy =>
          simp only [hs'] at ht
          cases ho : safeType? (some eo) with
          | none =>
            simp only [ho, Option.isNone_none, ↓reduceIte] at ht; cases ht
          | some
            oty =>
            simp only [ho, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
              Except.ok.injEq] at ht
            subst ht
            obtain ⟨all', hn', i', val', rfl⟩ := safeType_some.1 hs'
            obtain ⟨allo, hno, io, valo, rfl⟩ := safeType_some.1 ho
            have hN' := (viewOf_get h r.impl _).1 hen
            have hNo := (viewOf_get h r.spec _).1 heo
            obtain ⟨I, hI⟩ := named_typed h hN'
            obtain ⟨O, hO⟩ := named_typed h hNo
            refine ⟨I, hI, ?_⟩
            simp only [Target, hc, ↓reduceIte, reduceCtorEq]
            exact ⟨⟨all', hn', i', newTy, val', hN', hI⟩, O, allo, hno, io, oty, valo, hNo, hO⟩

/-- Part B's roots: an `.error` is infrastructure exactly when a root is absent, else the
statement's mismatch with no target type. -/
theorem roots_error {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {o : Outcome} (hk : r.kind ≠ .eq) (ht : roots (viewOf t) r = .error o) :
    ((∃ c, o = .infra c) ∧ ¬Trusted t r) ∨
      ((∃ m, o = .mismatch m) ∧ Trusted t r ∧ ¬∃ T, Target t r T) := by
  unfold roots at ht
  have htr :
    Trusted t r ↔ (∃ e, Named t r.spec e) ∧ (r.kind = .compat → ∃ e, Named t r.impl e) := by
    simp only [Trusted, hk, ↓reduceIte]
  by_cases hp : r.kind = .prop
  · have hp' : (r.kind == .prop) = true := by simp [hp]
    simp only [hp', ↓reduceIte] at ht
    cases he : (viewOf t).byName[r.spec]? with
    | none =>
      simp only [he, Except.error.injEq] at ht
      subst ht
      refine Or.inl ⟨⟨_, rfl⟩, fun hT => ?_⟩
      obtain ⟨⟨e, hN⟩, _⟩ := htr.1 hT
      rw [(viewOf_get h _ _).2 hN] at he
      cases he
    | some e =>
      simp only [he] at ht
      have hyes : Trusted t r :=
        htr.2
          ⟨⟨e, (viewOf_get h _ _).1 he⟩, fun hc => by
            rw [hp] at hc; cases hc⟩
      have hno :
        ∀ sty,
          safeType? (some e) = some sty → isProp (viewOf t).t sty = false → ¬∃ T, Target t r T := by
        rintro sty hs hpf ⟨T, hT⟩
        simp only [Target, hp, ↓reduceIte] at hT
        obtain ⟨hS, rfl⟩ := hT
        obtain ⟨e', sty', hg, hs', hx⟩ := (safeDefn_iff h _ _).1 hS
        rw [he, Option.some.injEq] at hg
        subst hg
        rw [hs, Option.some.injEq] at hs'
        subst hs'
        have hprop : isProp (viewOf t).t sty = true := (isProp_iff (rawOk_read h) sty).2 hx
        rw [hprop] at hpf
        cases hpf
      cases hs : safeType? (some e) with
      | none =>
        simp only [hs, Except.error.injEq] at ht
        subst ht
        refine Or.inr ⟨⟨_, rfl⟩, hyes, fun ⟨T, hT⟩ => ?_⟩
        simp only [Target, hp, ↓reduceIte] at hT
        obtain ⟨e', sty', hg, hs', _⟩ := (safeDefn_iff h _ _).1 hT.1
        rw [he, Option.some.injEq] at hg
        subst hg
        rw [hs] at hs'
        cases hs'
      | some sty =>
        simp only [hs] at ht
        by_cases hprop : isProp (viewOf t).t sty = true
        · simp only [hprop, ↓reduceIte] at ht
          cases ht
        · have hpf : isProp (viewOf t).t sty = false := by simpa using hprop
          simp only [hpf, Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at ht
          subst ht
          exact Or.inr ⟨⟨_, rfl⟩, hyes, hno sty hs hpf⟩
  · have hp' : (r.kind == .prop) = false := by simp [hp]
    have hc : r.kind = .compat := by cases hk2 : r.kind <;> simp_all
    simp only [hp', Bool.false_eq_true, ↓reduceIte] at ht
    have tgt : ∀ T, Target t r T → SafeDefn t r.impl T ∧ ∃ S, SafeDefn t r.spec S := by
      intro T hT
      simpa only [Target, hc, ↓reduceIte, reduceCtorEq] using hT
    cases hen : (viewOf t).byName[r.impl]? with
    | none =>
      simp only [hen, Except.error.injEq] at ht
      subst ht
      refine Or.inl ⟨⟨_, rfl⟩, fun hT => ?_⟩
      obtain ⟨e, hN⟩ := (htr.1 hT).2 hc
      rw [(viewOf_get h _ _).2 hN] at hen
      cases hen
    | some en =>
      simp only [hen] at ht
      cases heo : (viewOf t).byName[r.spec]? with
      | none =>
        simp only [heo, Except.error.injEq] at ht
        subst ht
        refine Or.inl ⟨⟨_, rfl⟩, fun hT => ?_⟩
        obtain ⟨⟨e, hN⟩, _⟩ := htr.1 hT
        rw [(viewOf_get h _ _).2 hN] at heo
        cases heo
      | some eo =>
        simp only [heo] at ht
        have hyes : Trusted t r :=
          htr.2 ⟨⟨eo, (viewOf_get h _ _).1 heo⟩, fun _ => ⟨en, (viewOf_get h _ _).1 hen⟩⟩
        cases hs' : safeType? (some en) with
        | none =>
          simp only [hs', Except.error.injEq] at ht
          subst ht
          refine Or.inr ⟨⟨_, rfl⟩, hyes, fun ⟨T, hT⟩ => ?_⟩
          obtain ⟨e', sty', hg, hs'', _⟩ := (safeDefn_iff h _ _).1 (tgt T hT).1
          rw [hen, Option.some.injEq] at hg
          subst hg
          rw [hs'] at hs''
          cases hs''
        | some newTy =>
          simp only [hs'] at ht
          cases ho : safeType? (some eo) with
          | none =>
            simp only [ho, Option.isNone_none, ↓reduceIte, Except.error.injEq] at ht
            subst ht
            refine Or.inr ⟨⟨_, rfl⟩, hyes, fun ⟨T, hT⟩ => ?_⟩
            obtain ⟨S, hS⟩ := (tgt T hT).2
            obtain ⟨e', sty', hg, hs'', _⟩ := (safeDefn_iff h _ _).1 hS
            rw [heo, Option.some.injEq] at hg
            subst hg
            rw [ho] at hs''
            cases hs''
          | some _ =>
            simp only [ho, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at ht
            cases ht

/-- S4's first stages: `.ok` names the target type's index, the implementation checked (part A). -/
theorem front_ok {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {tT : Nat} (hf : front (viewOf t) r = .ok tT) :
    ∃ T, t.exprs[tT]? = some T ∧ Target t r T ∧ (r.kind = .eq → ∃ I, SafeDefn t r.impl I) := by
  unfold front at hf
  by_cases hk : r.kind = .eq
  · have hk' : (r.kind == .eq) = true := by simp [hk]
    simp only [hk', ↓reduceIte] at hf
    cases ht : target (viewOf t) r with
    | error w =>
      simp only [ht] at hf; cases hf
    | ok tT' =>
      simp only [ht] at hf
      cases he : (viewOf t).byName[r.impl]? with
      | none =>
        simp only [he] at hf; cases hf
      | some e =>
        simp only [he] at hf
        cases hs : safeType? (some e) with
        | none =>
          simp only [hs, Option.isNone_none, ↓reduceIte] at hf; cases hf
        | some
          ity =>
          simp only [hs, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hf
          subst hf
          obtain ⟨T, hT, hTg⟩ := target_ok h hk ht
          obtain ⟨all, hn, i, val, rfl⟩ := safeType_some.1 hs
          have hNi := (viewOf_get h _ _).1 he
          obtain ⟨I, hI⟩ := named_typed h hNi
          exact ⟨T, hT, hTg, fun _ => ⟨I, all, hn, i, ity, val, hNi, hI⟩⟩
  · have hk' : (r.kind == .eq) = false := by simp [hk]
    simp only [hk', Bool.false_eq_true, ↓reduceIte] at hf
    obtain ⟨T, hT, hTg⟩ := roots_ok h hk hf
    exact ⟨T, hT, hTg, fun h' => absurd h' hk⟩

/-- S4's first stages: an `.error` is infrastructure exactly without the trusted data, else the
statement's mismatch with no `Holds`. -/
theorem front_error {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {o : Outcome} (hf : front (viewOf t) r = .error o) :
    ((∃ c, o = .infra c) ∧ ¬Trusted t r) ∨
      ((∃ m, o = .mismatch m) ∧ Trusted t r ∧ ∀ t2, ¬Holds t t2 r) := by
  unfold front at hf
  by_cases hk : r.kind = .eq
  · have hk' : (r.kind == .eq) = true := by simp [hk]
    simp only [hk', ↓reduceIte] at hf
    have htr : Trusted t r ↔ ∃ T, Target t r T := by simp only [Trusted, hk, ↓reduceIte]
    cases ht : target (viewOf t) r with
    | error w =>
      simp only [ht, Except.error.injEq] at hf
      subst hf
      exact Or.inl ⟨⟨w, rfl⟩, fun hT => target_error h hk ht (htr.1 hT)⟩
    | ok tT =>
      simp only [ht] at hf
      obtain ⟨T, _, hTg⟩ := target_ok h hk ht
      have impl_of : ∀ t2, Holds t t2 r → ∃ I, SafeDefn t r.impl I := fun _ hH => by
        obtain ⟨_, _, hI, _⟩ := hH
        exact hI hk
      cases he : (viewOf t).byName[r.impl]? with
      | none =>
        simp only [he, Except.error.injEq] at hf
        subst hf
        refine Or.inr ⟨⟨_, rfl⟩, htr.2 ⟨T, hTg⟩, fun t2 hH => ?_⟩
        obtain ⟨I, _, _, _, _, _, hN, _⟩ := impl_of t2 hH
        rw [(viewOf_get h _ _).2 hN] at he
        cases he
      | some e =>
        simp only [he] at hf
        cases hs : safeType? (some e) with
        | none =>
          simp only [hs, Option.isNone_none, ↓reduceIte, Except.error.injEq] at hf
          subst hf
          refine Or.inr ⟨⟨_, rfl⟩, htr.2 ⟨T, hTg⟩, fun t2 hH => ?_⟩
          obtain ⟨I, _, _, _, _, _, hN, _⟩ := impl_of t2 hH
          rw [(viewOf_get h _ _).2 hN, Option.some.injEq] at he
          subst he
          simp [safeType?] at hs
        | some _ =>
          simp only [hs, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hf
          cases hf
  · have hk' : (r.kind == .eq) = false := by simp [hk]
    simp only [hk', Bool.false_eq_true, ↓reduceIte] at hf
    rcases roots_error h hk hf with hl | ⟨hm, hyes, hnot⟩
    · exact Or.inl hl
    · exact Or.inr ⟨hm, hyes, fun _ ⟨T, hT, _⟩ => hnot ⟨T, hT⟩⟩

/-- S4's solution side: `.ok` = e2's theorem without level parameters, its name none of e1's. -/
theorem solution_ok {g v : String} {b1 : ByteArray} {t1 t2 : Tables}
    (hb1 : readTables g v b1 = .ok t1) {r : Request} {ty : Nat}
    (hs : solution (viewOf t1) (viewOf t2) r = .ok ty) :
    (∀ e, ¬Named t1 r.proof e) ∧
      ∃ all i val, (viewOf t2).byName[r.proof]? = some (.thm all [] i ty val) := by
  unfold solution at hs
  cases hp : (viewOf t2).byName[r.proof]? with
  | none =>
    simp only [hp] at hs; cases hs
  | some ep =>
    simp only [hp] at hs
    cases hth : thmOf? ep with
    | none =>
      simp only [hth] at hs; cases hs
    | some lt =>
      obtain ⟨lps, ty'⟩ := lt
      obtain ⟨all, i, val, rfl⟩ := thmOf_some.1 hth
      simp only [hth] at hs
      by_cases hl : lps.isEmpty = true
      · have hlps : lps = [] := List.isEmpty_iff.1 hl
        subst hlps
        simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
        by_cases hc : (viewOf t1).byName.contains r.proof = true
        · simp only [hc, ↓reduceIte] at hs
          cases hs
        · have hcf : (viewOf t1).byName.contains r.proof = false := by simpa using hc
          simp only [hcf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hs
          subst hs
          refine ⟨(byName_none hb1 r.proof).1 ?_, all, i, val, rfl⟩
          cases hg : (viewOf t1).byName[r.proof]? with
          | none => rfl
          | some _ =>
            rw [Std.HashMap.contains_eq_isSome_getElem?, hg] at hcf
            cases hcf
      · have hlf : lps.isEmpty = false := by simpa using hl
        simp only [hlf, Bool.not_false, ↓reduceIte] at hs
        cases hs

/-- S4's solution side: `.error` ⇒ no theorem of e2 fits. -/
theorem solution_error {g v : String} {b1 b2 : ByteArray} {t1 t2 : Tables}
    (hb1 : readTables g v b1 = .ok t1) (hb2 : readTables g v b2 = .ok t2) {r : Request} {w : String}
    (hs : solution (viewOf t1) (viewOf t2) r = .error w) :
    ¬((∀ e, ¬Named t1 r.proof e) ∧ ∃ all i ty val, Named t2 r.proof (.thm all [] i ty val)) := by
  rintro ⟨hno, all, i, ty, val, hN⟩
  have hp := (viewOf_get hb2 _ _).2 hN
  have hcf : (viewOf t1).byName.contains r.proof = false := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, (byName_none hb1 r.proof).2 hno]
    rfl
  simp [solution, hp, thmOf?, hcf] at hs

/-- U7 S `statementExact`. -/
theorem statement_exact (githash version : String) (b1 b2 : ByteArray) (t1 t2 : Tables)
    (r : Request) (fuel : Nat) (seen : Std.HashSet Pair) (o : Outcome × Nat × Std.HashSet Pair) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      (∀ p, seen.contains p = true → PairEq t1 t2 p) →
      statement (viewOf t1) (viewOf t2) r fuel seen = o →
      ((∃ c, o.1 = .infra c) ↔ ¬Trusted t1 r) ∧
        (o.1 = .matched → Holds t1 t2 r ∧ ∀ p, o.2.2.contains p = true → PairEq t1 t2 p) ∧
        (Holds t1 t2 r → o.1 = .matched ∨ o.1 = .exhausted) := by
  intro hb1 hb2 hs ho
  have h2 := rawOk_read hb2
  unfold statement at ho
  cases hf : front (viewOf t1) r with
  | error e =>
    simp only [hf] at ho
    subst ho
    rcases front_error hb1 hf with ⟨⟨c, rfl⟩, hn⟩ | ⟨⟨m, rfl⟩, hyes, hnot⟩
    · refine ⟨⟨fun _ => hn, fun _ => ⟨c, rfl⟩⟩, (fun h => by cases h), fun hH => ?_⟩
      obtain ⟨T, hT, _⟩ := hH
      exact absurd (trusted_of_target hT) hn
    · exact
        ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩, (fun h => by cases h),
          fun hH => absurd hH (hnot t2)⟩
  | ok tT =>
    simp only [hf, viewOf_t] at ho
    obtain ⟨T, hT, hTg, hImpl⟩ := front_ok hb1 hf
    have hyes : Trusted t1 r := trusted_of_target hTg
    have mis :
      ∀ (m : String) (f : Nat) (s' : Std.HashSet Pair),
        o = (.mismatch m, f, s') →
          (¬Holds t1 t2 r) →
          ((∃ c, o.1 = .infra c) ↔ ¬Trusted t1 r) ∧
            (o.1 = .matched → Holds t1 t2 r ∧ ∀ p, o.2.2.contains p = true → PairEq t1 t2 p) ∧
            (Holds t1 t2 r → o.1 = .matched ∨ o.1 = .exhausted) := by
      intro m f s' hm hnot
      subst hm
      exact
        ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩, (fun h => by cases h),
          fun hH => absurd hH hnot⟩
    cases hsol : solution (viewOf t1) (viewOf t2) r with
    | error w =>
      simp only [hsol] at ho
      refine mis _ _ _ ho.symm fun hH => ?_
      obtain ⟨_, _, _, hno, all, i, ty, val, _, _, hN, _⟩ := hH
      exact solution_error hb1 hb2 hsol ⟨hno, all, i, ty, val, hN⟩
    | ok ty =>
      simp only [hsol] at ho
      obtain ⟨hnot1, all, i, val, hp⟩ := solution_ok hb1 hsol
      obtain ⟨P, hP⟩ := named_typed hb2 ((viewOf_get hb2 _ _).1 hp)
      have hP : t2.exprs[ty]? = some P := hP
      have hparts : Holds t1 t2 r → ∃ u, alphaEq (template r T u) P = true := by
        intro hH
        obtain ⟨T', hT', _, _, all', i', ty', val', P', u, hN, hP', he⟩ := hH
        have := target_unique hb1 hTg hT'
        subst this
        rw [(viewOf_get hb2 _ _).2 hN, Option.some.injEq] at hp
        simp only [Entry.thm.injEq] at hp
        obtain ⟨_, _, _, rfl, _⟩ := hp
        rw [hP, Option.some.injEq] at hP'
        subst hP'
        exact ⟨u, he⟩
      have holds_of : ∀ u, alphaEq (template r T u) P = true → Holds t1 t2 r := fun u he =>
        ⟨T, hTg, hImpl, hnot1, all, i, ty, val, P, u, (viewOf_get hb2 _ _).1 hp, hP, he⟩
      by_cases hk : r.kind = .prop
      · have hk' : (r.kind == .prop) = true := by simp [hk]
        simp only [hk', ↓reduceIte] at ho
        by_cases hci : constIs t2 ty r.spec = true
        · simp only [hci, ↓reduceIte] at ho
          subst ho
          have hPc := (constIs_iff h2 ty r.spec).1 hci
          rw [hP, Option.some.injEq] at hPc
          subst hPc
          refine
            ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩,
              (fun _ => ⟨holds_of .zero ?_, hs⟩), (fun _ => Or.inl rfl)⟩
          rw [template_prop r T .zero hk]
          exact alphaEq_const_refl r.spec
        · have hcf' : constIs t2 ty r.spec = false := by simpa using hci
          simp only [hcf', Bool.false_eq_true, ↓reduceIte] at ho
          refine mis _ _ _ ho.symm fun hH => ?_
          obtain ⟨u, he⟩ := hparts hH
          rw [template_prop r T u hk] at he
          rw [constIs_of_alphaEq h2 hP he] at hcf'
          cases hcf'
      have hk' : (r.kind == .prop) = false := by simp [hk]
      simp only [hk', Bool.false_eq_true, ↓reduceIte] at ho
      have parts :
        Holds t1 t2 r →
          ∃ a1 a2 a3 x1,
            eqParts? t2 ty = some (a1, a2, a3) ∧
              t2.exprs[a1]? = some x1 ∧
              alphaEq T x1 = true ∧ constIs t2 a2 r.impl = true ∧ rhsIs t2 a3 r = true := by
        intro hH
        obtain ⟨u, he⟩ := hparts hH
        exact template_inv h2 hP hk he
      cases hq : eqParts? t2 ty with
      | none =>
        simp only [hq] at ho
        refine mis _ _ _ ho.symm fun hH => ?_
        obtain ⟨a1, a2, a3, x1, hq', _⟩ := parts hH
        rw [hq] at hq'
        cases hq'
      | some q =>
        obtain ⟨a1, a2, a3⟩ := q
        simp only [hq] at ho
        have same :
          Holds t1 t2 r →
            ∃ x1,
              t2.exprs[a1]? = some x1 ∧
                alphaEq T x1 = true ∧ constIs t2 a2 r.impl = true ∧ rhsIs t2 a3 r = true := by
          intro hH
          obtain ⟨b1', b2', b3', x1, hq', hx1, hTx, hci, hri⟩ := parts hH
          rw [hq, Option.some.injEq] at hq'
          simp only [Prod.mk.injEq] at hq'
          obtain ⟨rfl, rfl, rfl⟩ := hq'
          exact ⟨x1, hx1, hTx, hci, hri⟩
        by_cases hcr : (constIs t2 a2 r.impl && rhsIs t2 a3 r) = true
        · simp only [hcr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho
          have hw := eqExpr_exact githash version b1 b2 t1 t2 tT a1 fuel seen _ hb1 hb2 hs rfl
          rcases hwr : eqExpr t1 tT t2 a1 fuel seen with ⟨c, f, s'⟩
          rw [hwr] at ho hw
          cases c with
          | equal =>
            simp only at ho
            subst ho
            obtain ⟨hpe, hs'⟩ := hw.1 rfl
            refine
              ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩, (fun _ => ⟨?_, hs'⟩),
                (fun _ => Or.inl rfl)⟩
            rw [Bool.and_eq_true] at hcr
            obtain ⟨u, x1, x2, x3, rfl, hx1, hx2, hx3⟩ := eqParts_some h2 hP hq
            rw [(constIs_iff h2 a2 r.impl).1 hcr.1, Option.some.injEq] at hx2
            rw [(rhsIs_iff h2 a3 r).1 hcr.2, Option.some.injEq] at hx3
            subst hx2 hx3
            obtain ⟨x, y, hx, hy, hxy⟩ := hpe
            rw [hT, Option.some.injEq] at hx
            rw [hx1, Option.some.injEq] at hy
            subst hx hy
            refine holds_of u ?_
            rw [template_eq r T u hk]
            simp [alphaEq_app, alphaEq_const, levelsEq, levelEq_refl, hxy, alphaEq_rhs_refl]
          | differ =>
            simp only at ho
            refine mis _ _ _ ho.symm fun hH => ?_
            obtain ⟨x1, hx1, hTx, _⟩ := same hH
            exact hw.2 rfl ⟨T, x1, hT, hx1, hTx⟩
          | exhausted =>
            simp only at ho
            subst ho
            exact
              ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩, (fun h => by cases h),
                (fun _ => Or.inr rfl)⟩
        · have hcr' : (constIs t2 a2 r.impl && rhsIs t2 a3 r) = false := by simpa using hcr
          simp only [hcr', Bool.not_false, ↓reduceIte] at ho
          refine mis _ _ _ ho.symm fun hH => ?_
          obtain ⟨x1, _, _, hci, hri⟩ := same hH
          rw [hci, hri] at hcr'
          cases hcr'

end FvdepAudit.Judge.Proof
