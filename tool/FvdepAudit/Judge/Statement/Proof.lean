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
  Option.isSome_iff_exists.1 (entriesOk_typed (entriesOk_read h) e hN.1)

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
    {r : Request} {tT : Nat} (ht : target (viewOf t) r = .ok tT) :
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
            simp only [Target, hab]; exact hspec⟩
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
                simp only [Target, hab]; exact ⟨⟨S, hspec⟩, n, A, bnd, hsd, hA, hB⟩⟩

/-- The trusted side's test: `.error` ⇒ no target type. -/
theorem target_error {g v : String} {b : ByteArray} {t : Tables} (h : readTables g v b = .ok t)
    {r : Request} {w : String} (ht : target (viewOf t) r = .error w) : ¬∃ T, Target t r T := by
  have spec_of : ∀ T, Target t r T → ∃ S, SafeDefn t r.spec S := by
    intro T hT
    cases hab : r.abi with
    | none =>
      simp only [Target, hab] at hT; exact ⟨T, hT⟩
    | some s =>
      simp only [Target, hab] at hT; exact hT.1
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
    simp only [Target, hab] at hT
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
  cases hab : r.abi with
  | none =>
    simp only [Target, hab] at h1 h2
    exact safeDefn_unique h h1 h2
  | some s =>
    simp only [Target, hab] at h1 h2
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
    (he : alphaEq (template r T u) P = true) :
    ∃ a1 a2 a3 x1,
      eqParts? t ty = some (a1, a2, a3) ∧
        t.exprs[a1]? = some x1 ∧
        alphaEq T x1 = true ∧ constIs t a2 r.impl = true ∧ rhsIs t a3 r = true := by
  rw [template_eq] at he
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
    unfold rhsExpr at hR ⊢
    cases hab : r.abi with
    | none =>
      simp only [hab] at hR ⊢
      obtain ⟨_, _, xs3, _, hxe, _, _, hl3⟩ := alphaEq_const_inv h hx3 hR
      have : xs3 = [] := by
        cases xs3 with
        | nil => rfl
        | cons _ _ => simp [levelsEq] at hl3
      rw [hxe, this] at hx3
      exact hx3
    | some s =>
      simp only [hab] at hR ⊢
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
  unfold rhsExpr
  cases r.abi <;> simp [alphaEq_app, alphaEq_const, levelsEq]

/-- `Holds` through the indexes, its `T` = the given target's. -/
theorem holds_parts {g v : String} {b1 b2 : ByteArray} {t1 t2 : Tables}
    (hb1 : readTables g v b1 = .ok t1) (hb2 : readTables g v b2 = .ok t2) {r : Request}
    {T : Lean.Expr} (hT : Target t1 r T) (hH : Holds t1 t2 r) :
    (∃ e, (viewOf t1).byName[r.impl]? = some e ∧ (safeType? (some e)).isSome) ∧
      (viewOf t1).byName.contains r.proof = false ∧
      ∃ all i ty val P u,
        (viewOf t2).byName[r.proof]? = some (.thm all [] i ty val) ∧
          t2.exprs[ty]? = some P ∧ alphaEq (template r T u) P = true := by
  obtain ⟨T', hT', ⟨I, hI⟩, hno, all, i, ty, val, P, u, hN, hP, he⟩ := hH
  have := target_unique hb1 hT hT'
  subst this
  refine ⟨?_, ?_, all, i, ty, val, P, u, (viewOf_get hb2 _ _).2 hN, hP, he⟩
  · obtain ⟨e, sty, hg, hs, _⟩ := (safeDefn_iff hb1 _ _).1 hI
    exact
      ⟨e, hg, by
        rw [hs]; rfl⟩
  · rw [Std.HashMap.contains_eq_isSome_getElem?, (byName_none hb1 r.proof).2 hno]
    rfl

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

/-- U7 S `statementExact`. -/
theorem statement_exact (githash version : String) (b1 b2 : ByteArray) (t1 t2 : Tables)
    (r : Request) (fuel : Nat) (seen : Std.HashSet Pair) (o : Outcome × Nat × Std.HashSet Pair) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      (∀ p, seen.contains p = true → PairEq t1 t2 p) →
      statement (viewOf t1) (viewOf t2) r fuel seen = o →
      ((∃ c, o.1 = .infra c) ↔ ¬∃ T, Target t1 r T) ∧
        (o.1 = .matched → Holds t1 t2 r ∧ ∀ p, o.2.2.contains p = true → PairEq t1 t2 p) ∧
        (Holds t1 t2 r →
          o.1 = .matched ∨ o.1 = .mismatch "the comparison passes its work budget") := by
  intro hb1 hb2 hs ho
  have h2 := rawOk_read hb2
  unfold statement at ho
  cases ht : target (viewOf t1) r with
  | error w =>
    simp only [ht] at ho
    subst ho
    have hn := target_error hb1 ht
    refine ⟨⟨(fun _ => hn), (fun _ => ⟨w, rfl⟩)⟩, (fun h => by cases h), fun hH => ?_⟩
    obtain ⟨T, hT, _⟩ := hH
    exact absurd ⟨T, hT⟩ hn
  | ok tT =>
    simp only [ht, viewOf_t] at ho
    obtain ⟨T, hT, hTg⟩ := target_ok hb1 ht
    have hyes : ∃ T, Target t1 r T := ⟨T, hTg⟩
    have mis :
      ∀ (m : String) (f : Nat) (s' : Std.HashSet Pair),
        o = (.mismatch m, f, s') →
          (¬Holds t1 t2 r) →
          ((∃ c, o.1 = .infra c) ↔ ¬∃ T, Target t1 r T) ∧
            (o.1 = .matched → Holds t1 t2 r ∧ ∀ p, o.2.2.contains p = true → PairEq t1 t2 p) ∧
            (Holds t1 t2 r →
              o.1 = .matched ∨ o.1 = .mismatch "the comparison passes its work budget") := by
      intro m f s' hm hnot
      subst hm
      exact
        ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩, (fun h => by cases h),
          fun hH => absurd hH hnot⟩
    cases hi : (viewOf t1).byName[r.impl]? with
    | none =>
      simp only [hi] at ho
      refine mis _ _ _ ho.symm fun hH => ?_
      obtain ⟨⟨e, he, _⟩, _⟩ := holds_parts hb1 hb2 hTg hH
      rw [hi] at he
      cases he
    | some e =>
      simp only [hi] at ho
      cases hsi : safeType? (some e) with
      | none =>
        simp only [hsi, Option.isNone_none, ↓reduceIte] at ho
        refine mis _ _ _ ho.symm fun hH => ?_
        obtain ⟨⟨e', he', hs'⟩, _⟩ := holds_parts hb1 hb2 hTg hH
        rw [hi, Option.some.injEq] at he'
        subst he'
        rw [hsi] at hs'
        cases hs'
      | some ity =>
        simp only [hsi, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at ho
        cases hp : (viewOf t2).byName[r.proof]? with
        | none =>
          simp only [hp] at ho
          refine mis _ _ _ ho.symm fun hH => ?_
          obtain ⟨_, _, all, i, ty, val, P, u, hN, _⟩ := holds_parts hb1 hb2 hTg hH
          rw [hp] at hN
          cases hN
        | some ep =>
          simp only [hp] at ho
          cases hth : thmOf? ep with
          | none =>
            simp only [hth] at ho
            refine mis _ _ _ ho.symm fun hH => ?_
            obtain ⟨_, _, all, i, ty, val, P, u, hN, _⟩ := holds_parts hb1 hb2 hTg hH
            rw [hp, Option.some.injEq] at hN
            exact thmOf_none hth _ _ _ _ _ hN
          | some lt =>
            obtain ⟨lps, ty⟩ := lt
            obtain ⟨all, i, val, rfl⟩ := thmOf_some.1 hth
            simp only [hth] at ho
            by_cases hl : lps.isEmpty = true
            · have hlps : lps = [] := List.isEmpty_iff.1 hl
              subst hlps
              simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho
              by_cases hc : (viewOf t1).byName.contains r.proof = true
              · simp only [hc, ↓reduceIte] at ho
                refine mis _ _ _ ho.symm fun hH => ?_
                obtain ⟨_, hc', _⟩ := holds_parts hb1 hb2 hTg hH
                rw [hc] at hc'
                cases hc'
              · have hcf : (viewOf t1).byName.contains r.proof = false := by simpa using hc
                simp only [hcf, Bool.false_eq_true, ↓reduceIte] at ho
                obtain ⟨P, hP⟩ := named_typed hb2 ((viewOf_get hb2 _ _).1 hp)
                have parts :
                  Holds t1 t2 r →
                    ∃ a1 a2 a3 x1,
                      eqParts? t2 ty = some (a1, a2, a3) ∧
                        t2.exprs[a1]? = some x1 ∧
                        alphaEq T x1 = true ∧
                        constIs t2 a2 r.impl = true ∧ rhsIs t2 a3 r = true := by
                  intro hH
                  obtain ⟨_, _, all', i', ty', val', P', u, hN, hP', he⟩ :=
                    holds_parts hb1 hb2 hTg hH
                  rw [hp, Option.some.injEq] at hN
                  simp only [Entry.thm.injEq] at hN
                  obtain ⟨_, _, _, rfl, _⟩ := hN
                  exact template_inv h2 hP' he
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
                          alphaEq T x1 = true ∧
                          constIs t2 a2 r.impl = true ∧ rhsIs t2 a3 r = true := by
                    intro hH
                    obtain ⟨b1', b2', b3', x1, hq', hx1, hTx, hci, hri⟩ := parts hH
                    rw [hq, Option.some.injEq] at hq'
                    simp only [Prod.mk.injEq] at hq'
                    obtain ⟨rfl, rfl, rfl⟩ := hq'
                    exact ⟨x1, hx1, hTx, hci, hri⟩
                  by_cases hcr : (constIs t2 a2 r.impl && rhsIs t2 a3 r) = true
                  · simp only [hcr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho
                    have hw :=
                      eqExpr_exact githash version b1 b2 t1 t2 tT a1 fuel seen _ hb1 hb2 hs rfl
                    rcases hwr : eqExpr t1 tT t2 a1 fuel seen with ⟨c, f, s'⟩
                    rw [hwr] at ho hw
                    cases c with
                    | equal =>
                      simp only at ho
                      subst ho
                      obtain ⟨hpe, hs'⟩ := hw.1 rfl
                      refine
                        ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩,
                          (fun _ => ⟨?_, hs'⟩), (fun _ => Or.inl rfl)⟩
                      rw [Bool.and_eq_true] at hcr
                      obtain ⟨u, x1, x2, x3, rfl, hx1, hx2, hx3⟩ := eqParts_some h2 hP hq
                      rw [(constIs_iff h2 a2 r.impl).1 hcr.1, Option.some.injEq] at hx2
                      rw [(rhsIs_iff h2 a3 r).1 hcr.2, Option.some.injEq] at hx3
                      subst hx2 hx3
                      obtain ⟨x, y, hx, hy, hxy⟩ := hpe
                      rw [hT, Option.some.injEq] at hx
                      rw [hx1, Option.some.injEq] at hy
                      subst hx hy
                      have hNi := (viewOf_get hb1 _ _).1 hi
                      obtain ⟨all', hn', i', val', rfl⟩ := safeType_some.1 hsi
                      obtain ⟨I, hI⟩ := named_typed hb1 hNi
                      refine
                        ⟨T, hTg, ⟨I, all', hn', i', ity, val', hNi, hI⟩,
                          (byName_none hb1 r.proof).1 ?_, all, i, ty, val, _, u,
                          (viewOf_get hb2 _ _).1 hp, hP, ?_⟩
                      · cases hg : (viewOf t1).byName[r.proof]? with
                        | none => rfl
                        | some _ =>
                          rw [Std.HashMap.contains_eq_isSome_getElem?, hg] at hcf
                          cases hcf
                      · rw [template_eq]
                        simp [alphaEq_app, alphaEq_const, levelsEq, levelEq_refl, hxy,
                          alphaEq_rhs_refl]
                    | differ =>
                      simp only at ho
                      refine mis _ _ _ ho.symm fun hH => ?_
                      obtain ⟨x1, hx1, hTx, _⟩ := same hH
                      exact hw.2 rfl ⟨T, x1, hT, hx1, hTx⟩
                    | exhausted =>
                      simp only at ho
                      subst ho
                      exact
                        ⟨⟨(fun ⟨_, hc⟩ => by cases hc), (fun hn => absurd hyes hn)⟩,
                          (fun h => by cases h), (fun _ => Or.inr rfl)⟩
                  · have hcr' : (constIs t2 a2 r.impl && rhsIs t2 a3 r) = false := by
                      simpa using hcr
                    simp only [hcr', Bool.not_false, ↓reduceIte] at ho
                    refine mis _ _ _ ho.symm fun hH => ?_
                    obtain ⟨x1, _, _, hci, hri⟩ := same hH
                    rw [hci, hri] at hcr'
                    cases hcr'
            · have hlf : lps.isEmpty = false := by simpa using hl
              simp only [hlf, Bool.not_false, ↓reduceIte] at ho
              refine mis _ _ _ ho.symm fun hH => ?_
              obtain ⟨_, _, all', i', ty', val', P, u, hN, _⟩ := holds_parts hb1 hb2 hTg hH
              rw [hp, Option.some.injEq] at hN
              simp only [Entry.thm.injEq] at hN
              rw [hN.2.1] at hlf
              cases hlf

end FvdepAudit.Judge.Proof
