import FvdepAudit.Protocol.Spec

/-! Proof: the type table (contract U4 B1, B4 `SigExact`). -/

namespace FvdepAudit.Protocol.Proof

open FvdepCore.Protocol FvdepAudit.Protocol.Spec

theorem bare_eq (e : Lean.Expr) : bare e = stripMData e := by
  induction e <;> simp_all [bare, stripMData]

theorem tyOf_of_tyIs {e : Lean.Expr} {t : Ty} (h : TyIs e t) : tyOf e = some t := by
  cases h <;> simp_all [tyOf, bare_eq]

theorem tyIs_of_tyOf {e : Lean.Expr} {t : Ty} (h : tyOf e = some t) : TyIs e t := by
  simp only [tyOf, bare_eq] at h
  split at h
  · split at h <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> (try subst h)
    · exact .listUInt8 _ _ _ _ (by assumption) (by assumption) (by assumption)
    · exact .listChar _ _ _ _ (by assumption) (by assumption) (by assumption)
    · exact .listUInt16 _ _ _ _ (by assumption) (by assumption) (by assumption)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> (try subst h)
  · exact .byteArray _ (by assumption)
  · exact .nat _ (by assumption)
  · exact .int _ (by assumption)
  · exact .ordering _ (by assumption)
  · exact .version _ (by assumption)

theorem tyOf_iff (e : Lean.Expr) (t : Ty) : tyOf e = some t ↔ TyIs e t :=
  ⟨tyIs_of_tyOf, tyOf_of_tyIs⟩

theorem rtyOf_of_rtyIs {e : Lean.Expr} {r : RTy} (h : RTyIs e r) : rtyOf e = some r := by
  cases h with
  | option f x u t he hf hx => simp [rtyOf, bare_eq, he, hf, tyOf_of_tyIs hx]
  | plain t ht =>
    have hs := tyOf_of_tyIs ht
    cases ht <;> simp_all [rtyOf, bare_eq]

theorem rtyIs_of_rtyOf {e : Lean.Expr} {r : RTy} (h : rtyOf e = some r) : RTyIs e r := by
  simp only [rtyOf, bare_eq] at h
  split at h
  · split at h
    · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .option _ _ _ _ t (by assumption) (by assumption) (tyIs_of_tyOf ht)
    · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .plain _ t (tyIs_of_tyOf ht)
  · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .plain _ t (tyIs_of_tyOf ht)

theorem rtyOf_iff (e : Lean.Expr) (r : RTy) : rtyOf e = some r ↔ RTyIs e r :=
  ⟨rtyIs_of_rtyOf, rtyOf_of_rtyIs⟩

/-- An arrow never reads as a value type. -/
theorem sigOf_none :
    ∀ e : Lean.Expr, (∀ n a b bi, stripMData e ≠ .forallE n a b bi) → sigOf e = none
  | .mdata d e, h => by
    simp only [sigOf]
    exact sigOf_none e (by simpa [stripMData] using h)
  | .forallE n a b bi, h => absurd (by simp [stripMData]) (h n a b bi)
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _ |
    .letE .., _ | .lit _, _ | .proj .., _ => rfl

theorem sigOf_none_of_rtyIs {e : Lean.Expr} {r : RTy} (h : RTyIs e r) : sigOf e = none := by
  apply sigOf_none
  intro n a b bi hf
  rcases h with ⟨f, x, u, t, he, -, -⟩ | ⟨t, ht⟩
  · rw [he] at hf
    cases hf
  · cases ht <;> simp_all

theorem sigOf_of_sigIs {e : Lean.Expr} {ts : List Ty} {r : RTy} (h : SigIs e ts r) :
    sigOf e = some (ts, r) := by
  induction h with
  | last n a b bi t r ha hb hr =>
    simp [sigOf, hb, tyOf_of_tyIs ha, sigOf_none_of_rtyIs hr, rtyOf_of_rtyIs hr]
  | cons n a b bi t ts r ha hb _ ih => simp [sigOf, hb, tyOf_of_tyIs ha, ih]
  | mdata d e ts r _ ih => simpa [sigOf] using ih

theorem sigIs_of_sigOf :
    ∀ (e : Lean.Expr) (ts : List Ty) (r : RTy), sigOf e = some (ts, r) → SigIs e ts r
  | .mdata d e, ts, r, h => .mdata d e ts r (sigIs_of_sigOf e ts r (by simpa [sigOf] using h))
  | .forallE n a b bi, ts, r, h => by
    unfold sigOf at h
    by_cases hb : b.hasLooseBVars
    · simp [hb] at h
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i t p ha hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact
          .cons n a b bi t p.1 p.2 (tyIs_of_tyOf ha) (by simpa using hb)
            (sigIs_of_sigOf b p.1 p.2 hs)
      · rename_i t ha _
        obtain ⟨r', hr, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .last n a b bi t r' (tyIs_of_tyOf ha) (by simpa using hb) (rtyIs_of_rtyOf hr)
      · cases h
  | .bvar _, _, _, h | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h | .const .., _, _, h |
    .app .., _, _, h | .lam .., _, _, h | .letE .., _, _, h | .lit _, _, _, h | .proj .., _, _, h =>
    by simp [sigOf] at h

theorem sigOf_iff (e : Lean.Expr) (ts : List Ty) (r : RTy) :
    sigOf e = some (ts, r) ↔ SigIs e ts r := ⟨sigIs_of_sigOf e ts r, sigOf_of_sigIs⟩

end FvdepAudit.Protocol.Proof
