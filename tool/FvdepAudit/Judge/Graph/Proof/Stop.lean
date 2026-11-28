import FvdepAudit.Judge.Graph.Proof

/-! Proofs: the judge's stop laws (contract `docs/contracts/U7-judge.md` X7, S4, G3) — a stage
reports `exhausted` only with no work unit left — + G3's trusted-side fault: when every reached
constant e1 declares agrees with e2, a reached name e1 lacks ends the graph step as infrastructure
or exhaustion, never as the solution's mismatch. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepAudit.Export.Spec FvdepAudit.Judge.Spec
  FvdepAudit.Judge.Statement.Spec FvdepAudit.Judge.Graph.Spec

/-! ## Fuel -/

theorem walk_fuel {t1 t2 : Tables} :
    ∀ (fuel : Nat) (ps : List Pair) (seen : Std.HashSet Pair),
      (walk t1 t2 fuel ps seen).2.1 ≤ fuel ∧
        ((walk t1 t2 fuel ps seen).1 = .exhausted → (walk t1 t2 fuel ps seen).2.1 = 0) := by
  intro fuel
  induction fuel with
  | zero =>
    intro ps seen
    cases ps with
    | nil => simp [walk]
    | cons _ _ => simp [walk]
  | succ fuel ih =>
    intro ps seen
    cases ps with
    | nil => simp [walk]
    | cons p rest =>
      simp only [walk]
      split
      · have := ih rest seen
        exact ⟨Nat.le_succ_of_le this.1, this.2⟩
      · split
        · rename_i _ kids _
          have := ih (kids ++ rest) (seen.insert p)
          exact ⟨Nat.le_succ_of_le this.1, this.2⟩
        · simp

theorem walk_exhausted {t1 t2 : Tables} {fuel : Nat} {ps : List Pair} {seen : Std.HashSet Pair}
    {f : Nat} {s : Std.HashSet Pair} (h : walk t1 t2 fuel ps seen = (.exhausted, f, s)) :
    f = 0 := by
  have := (walk_fuel (t1 := t1) (t2 := t2) fuel ps seen).2
  rw [h] at this
  exact this rfl

theorem declEq_fuel (t1 t2 : Tables) (e e' : Entry) (fuel : Nat) (seen : Std.HashSet Pair) :
    (declEq t1 e t2 e' fuel seen).2.1 ≤ fuel ∧
      ((declEq t1 e t2 e' fuel seen).1 = .exhausted → (declEq t1 e t2 e' fuel seen).2.1 = 0) := by
  unfold declEq
  split
  · exact walk_fuel fuel _ seen
  · simp

theorem collect_fuel {t : Tables} :
    ∀ (fuel : Nat) (todo : List Nat) (seen : Std.HashSet Nat) (acc acc' : List Nat) (f : Nat)
      (seen' : Std.HashSet Nat),
      collect t fuel todo seen acc = some (acc', f, seen') → f ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo seen acc acc' f seen' hc
    cases todo with
    | nil =>
      simp only [collect_nil, Option.some.injEq, Prod.mk.injEq] at hc
      omega
    | cons _ _ => simp [collect] at hc
  | succ fuel ih =>
    intro todo seen acc acc' f seen' hc
    cases todo with
    | nil =>
      simp only [collect_nil, Option.some.injEq, Prod.mk.injEq] at hc
      omega
    | cons i rest =>
      simp only [collect] at hc
      by_cases hi : seen.contains i = true
      · simp only [hi, ↓reduceIte] at hc
        exact Nat.le_succ_of_le (ih rest seen acc acc' f seen' hc)
      · simp only [hi] at hc
        rcases hst : exprStep t i with ⟨ns, kids⟩
        simp only [hst] at hc
        exact Nat.le_succ_of_le (ih _ _ _ acc' f seen' hc)

theorem usesOf_fuel {t : Tables} {e : Entry} {fuel : Nat} {seen : Std.HashSet Nat}
    {L : List Lean.Name} {f : Nat} {s : Std.HashSet Nat}
    (hu : usesOf t e fuel seen = some (L, f, s)) : f ≤ fuel := by
  unfold usesOf at hu
  rcases hst : entryUses e with ⟨ns, roots⟩
  simp only [hst] at hu
  rcases hc : collect t fuel roots seen [] with _ | ⟨found, f', s'⟩
  · simp [hc] at hu
  · simp only [hc, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨_, rfl, _⟩ := hu
    exact collect_fuel fuel roots seen [] found f' s' hc

/-! ## Stop laws -/

theorem graphWalk_stop (v1 v2 : View) :
    ∀ (steps : Nat) (w : Walk) (o : Outcome) (w' : Walk),
      w.fuel < steps → graphWalk v1 v2 steps w = (o, w') → o = .exhausted → w'.fuel = 0 := by
  intro steps
  induction steps with
  | zero =>
    intro w _ _ hl; omega
  | succ steps ih =>
    intro w o w' hl hg ho
    rcases htd : w.todo with _ | ⟨c, rest⟩
    · simp only [graphWalk, htd] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact nomatch ho
    · rcases hfu : w.fuel with _ | fuel
      · simp only [graphWalk, htd, hfu] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact hfu
      · simp only [graphWalk, htd, hfu] at hg
        rw [hfu] at hl
        by_cases hck : w.checked.contains c = true
        · simp only [hck, ↓reduceIte] at hg
          exact
            ih _ o w'
              (by
                show fuel < steps; omega)
              hg ho
        · simp only [hck] at hg
          rcases hv1 : v1.byName[c]? with _ | e1
          · simp only [hv1] at hg
            obtain ⟨rfl, rfl⟩ := hg
            exact nomatch ho
          · rcases hv2 : v2.byName[c]? with _ | e2
            · simp only [hv1, hv2] at hg
              obtain ⟨rfl, rfl⟩ := hg
              exact nomatch ho
            · rcases hd : declEq v1.t e1 v2.t e2 fuel w.memo with ⟨r, f, m⟩
              have hf := declEq_fuel v1.t v2.t e1 e2 fuel w.memo
              rw [hd] at hf
              cases r with
              | differ =>
                simp only [hv1, hv2, hd] at hg
                obtain ⟨rfl, rfl⟩ := hg
                exact nomatch ho
              | exhausted =>
                simp only [hv1, hv2, hd] at hg
                obtain ⟨rfl, rfl⟩ := hg
                exact hf.2 rfl
              | equal =>
                have hf1 : f ≤ fuel := hf.1
                rcases hu : usesOf v1.t e1 f w.seen with _ | ⟨ns, f', s'⟩
                · simp only [hv1, hv2, hd, hu] at hg
                  obtain ⟨rfl, rfl⟩ := hg
                  rfl
                · simp only [hv1, hv2, hd, hu] at hg
                  have := usesOf_fuel hu
                  exact
                    ih _ o w'
                      (by
                        show f' < steps; omega)
                      hg ho

theorem proofWalk_stop (v2 : View) :
    ∀ (steps : Nat) (w : ProofWalk) (o : Outcome) (w' : ProofWalk),
      w.fuel < steps → proofWalk v2 steps w = (o, w') → o = .exhausted → w'.fuel = 0 := by
  intro steps
  induction steps with
  | zero =>
    intro w _ _ hl; omega
  | succ steps ih =>
    intro w o w' hl hg ho
    rcases htd : w.todo with _ | ⟨c, rest⟩
    · simp only [proofWalk, htd] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact nomatch ho
    · rcases hfu : w.fuel with _ | fuel
      · simp only [proofWalk, htd, hfu] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact hfu
      · simp only [proofWalk, htd, hfu] at hg
        rw [hfu] at hl
        by_cases hck : w.checked.contains c = true
        · simp only [hck, ↓reduceIte] at hg
          exact
            ih _ o w'
              (by
                show fuel < steps; omega)
              hg ho
        · simp only [hck] at hg
          rcases hv : v2.byName[c]? with _ | e
          · simp only [hv] at hg
            obtain ⟨rfl, rfl⟩ := hg
            exact nomatch ho
          · rcases hu : usesOf v2.t e fuel w.seen with _ | ⟨ns, f, s⟩
            · simp only [hv, hu] at hg
              obtain ⟨rfl, rfl⟩ := hg
              rfl
            · simp only [hv, hu] at hg
              have := usesOf_fuel hu
              exact
                ih _ o w'
                  (by
                    show f < steps; omega)
                  hg ho

/-- U7 G3 + G6 `graphStop`: `graph` reports `exhausted` only with no work unit left. -/
theorem graph_stop (v1 v2 : View) (r : Request) (opaques : List Lean.Name) (fuel : Nat)
    (seen : Std.HashSet Pair) (o : Outcome × List Lean.Name × Nat × Std.HashSet Pair) :
    graph v1 v2 r opaques fuel seen = o → o.1 = .exhausted → o.2.2.1 = 0 := by
  intro ho he
  unfold graph at ho
  rcases hw : graphWalk v1 v2 (fuel + 1) (walkStart r fuel seen) with ⟨o1, w⟩
  have g := graphWalk_stop v1 v2 (fuel + 1) (walkStart r fuel seen) o1 w (Nat.lt_succ_self fuel) hw
  cases o1 with
  | matched =>
    simp only [hw] at ho
    rcases hfo : firstOpaque v1 opaques w.order.reverse with _ | c
    · simp only [hfo] at ho
      rcases hp : proofWalk v2 (w.fuel + 1) (proofStart r w.fuel) with ⟨o2, p⟩
      have pg := proofWalk_stop v2 (w.fuel + 1) (proofStart r w.fuel) o2 p (Nat.lt_succ_self _) hp
      cases o2 with
      | exhausted =>
        simp only [hp] at ho
        subst ho
        exact pg rfl
      | _ =>
        simp only [hp] at ho
        subst ho
        exact nomatch he
    · simp only [hfo] at ho
      subst ho
      exact nomatch he
  | exhausted =>
    simp only [hw] at ho
    subst ho
    exact g rfl
  | _ =>
    simp only [hw] at ho
    subst ho
    exact nomatch he

/-- U7 S4 `statementStop`: `statement` reports `exhausted` only with no work unit left. -/
theorem statement_stop (v1 v2 : View) (r : Request) (fuel : Nat) (seen : Std.HashSet Pair)
    (o : Outcome × Nat × Std.HashSet Pair) :
    statement v1 v2 r fuel seen = o → o.1 = .exhausted → o.2.1 = 0 := by
  intro ho he
  subst ho
  unfold statement at he ⊢
  cases hf : front v1 r with
  | error e =>
    simp only [hf] at he ⊢
    unfold front roots at hf
    repeat' split at hf
    all_goals simp_all
  | ok tT =>
    simp only [hf] at he ⊢
    repeat' split at he
    all_goals simp_all
    rename_i heq
    exact walk_exhausted heq

/-! ## G3's trusted-side fault -/

/-- G3's walk when every reached constant e1 declares agrees with e2: it never reports the
solution's mismatch. -/
theorem graphWalk_agree {g v : String} {b1 b2 : ByteArray} {t1 t2 : Tables}
    (hb1 : readTables g v b1 = .ok t1) (hb2 : readTables g v b2 = .ok t2) (R : List Lean.Name)
    (hagree : ∀ c, Reach t1 R c → ∀ e1, Named t1 c e1 → ∃ e2, Named t2 c e2 ∧ EntryEq t1 t2 e1 e2) :
    ∀ (steps : Nat) (w : Walk) (o : Outcome) (w' : Walk),
      GraphInv t1 t2 R w →
        graphWalk (viewOf t1) (viewOf t2) steps w = (o, w') →
        o = .matched ∨ (∃ d, o = .infra d) ∨ o = .exhausted := by
  intro steps
  induction steps with
  | zero =>
    intro w o w' _ hg
    by_cases he : w.todo.isEmpty = true
    · simp only [graphWalk, he, ↓reduceIte] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact Or.inl rfl
    · simp only [graphWalk, he] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact Or.inr (Or.inr rfl)
  | succ steps ih =>
    intro w o w' hi hg
    rcases htd : w.todo with _ | ⟨c, rest⟩
    · simp only [graphWalk, htd] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact Or.inl rfl
    · have hrc : Reach t1 R c :=
        hi.todo c
          (by
            rw [htd]; exact List.mem_cons_self)
      rcases hfu : w.fuel with _ | fuel
      · simp only [graphWalk, htd, hfu] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact Or.inr (Or.inr rfl)
      · simp only [graphWalk, htd, hfu] at hg
        by_cases hck : w.checked.contains c = true
        · simp only [hck, ↓reduceIte] at hg
          exact ih _ o w' (graphInv_skip hi htd (Std.HashSet.mem_iff_contains.2 hck) fuel) hg
        · simp only [hck] at hg
          rcases hv1 : (viewOf t1).byName[c]? with _ | e1
          · simp only [hv1] at hg
            obtain ⟨rfl, rfl⟩ := hg
            exact Or.inr (Or.inl ⟨_, rfl⟩)
          · have hn1 := (viewOf_get hb1 c e1).1 hv1
            obtain ⟨e2', hn2', hee'⟩ := hagree c hrc e1 hn1
            rcases hv2 : (viewOf t2).byName[c]? with _ | e2
            · exact absurd hn2' (named_none hb2 hv2 e2')
            · have he2 := named_eq hb2 hv2 hn2'
              subst he2
              rcases hd : declEq (viewOf t1).t e1 (viewOf t2).t e2' fuel w.memo with ⟨r, f, m⟩
              have hde :=
                declEq_exact g v b1 b2 t1 t2 e1 e2' fuel w.memo (r, f, m) hb1 hb2 hi.memo hd
              cases r with
              | differ => exact absurd hee' (hde.2 rfl)
              | exhausted =>
                simp only [hv1, hv2, hd] at hg
                obtain ⟨rfl, rfl⟩ := hg
                exact Or.inr (Or.inr rfl)
              | equal =>
                obtain ⟨hee, hm⟩ := hde.1 rfl
                rcases hu : usesOf (viewOf t1).t e1 f w.seen with _ | ⟨ns, f', s'⟩
                · simp only [hv1, hv2, hd, hu] at hg
                  obtain ⟨rfl, rfl⟩ := hg
                  exact Or.inr (Or.inr rfl)
                · simp only [hv1, hv2, hd, hu] at hg
                  exact ih _ o w' (graphInv_step hb1 hb2 hi htd hv1 hv2 hee hm hu) hg

/-- U7 G3 `graphInfra`: when every reached constant e1 declares agrees with e2 and a reached name
is missing in e1, `graph` reports infrastructure or exhaustion. -/
theorem graph_infra (githash version : String) (b1 b2 : ByteArray) (t1 t2 : Tables) (r : Request)
    (opaques : List Lean.Name) (fuel : Nat) (seen : Std.HashSet Pair)
    (o : Outcome × List Lean.Name × Nat × Std.HashSet Pair) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      (∀ p, seen.contains p = true → PairEq t1 t2 p) →
      graph (viewOf t1) (viewOf t2) r opaques fuel seen = o →
      (∀ c,
        Reach t1 (graphRoots r) c →
          ∀ e1, Named t1 c e1 → ∃ e2, Named t2 c e2 ∧ EntryEq t1 t2 e1 e2) →
      (∃ c, Reach t1 (graphRoots r) c ∧ ∀ e, ¬Named t1 c e) →
      (∃ d, o.1 = .infra d) ∨ o.1 = .exhausted := by
  intro hb1 hb2 hs ho hagree ⟨c, hrc, hmiss⟩
  unfold graph at ho
  rcases hw : graphWalk (viewOf t1) (viewOf t2) (fuel + 1) (walkStart r fuel seen) with ⟨o1, w⟩
  have hst := graphInv_start t1 t2 r fuel seen hs
  have ha := graphWalk_agree hb1 hb2 (graphRoots r) hagree (fuel + 1) _ o1 w hst hw
  obtain ⟨ga, _, _⟩ := graphWalk_spec hb1 hb2 (graphRoots r) (fuel + 1) _ o1 w hst hw
  rcases ha with rfl | ⟨d, rfl⟩ | rfl
  · obtain ⟨hgi, hgt⟩ := ga rfl
    obtain ⟨_, e1, _, hn1, _, _⟩ := hgi.checked c (graphInv_closed hgi hgt c hrc)
    exact absurd hn1 (hmiss e1)
  · simp only [hw] at ho
    subst ho
    exact Or.inl ⟨d, rfl⟩
  · simp only [hw] at ho
    subst ho
    exact Or.inr rfl

end FvdepAudit.Judge.Proof
