import FvdepAudit.Judge.Proof.Exprs

/-! Proofs: the judge's comparisons (contract `docs/contracts/U7-judge.md` X7) — the worklist over
a shared memo decides every pair it was given (`walk_spec`), hence `eqExpr` + `declEq` decide
their meaning on two exports the reader accepts, within the budget, the memo kept sound. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules FvdepAudit.Export.Spec
  FvdepAudit.Judge.Spec

/-- The walk's invariant: each accepted pair is equal, or its kids are accepted or still to
come. -/
def WalkOk (t1 t2 : Tables) (S : Std.HashSet Pair) (wl : List Pair) : Prop :=
  ∀ p,
    S.contains p = true →
      PairEq t1 t2 p ∨ ∃ kids, heads t1 t2 p = some kids ∧ ∀ k ∈ kids, S.contains k = true ∨ k ∈ wl

/-- With nothing left to come, every accepted pair is equal (by rank: a kid ranks below its
pair). -/
theorem closed_sound {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) {S : Std.HashSet Pair}
    (hc : WalkOk t1 t2 S []) : ∀ p, S.contains p = true → PairEq t1 t2 p := by
  have key : ∀ n p, rank t1 p = n → S.contains p = true → PairEq t1 t2 p := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hr hp
      rcases hc p hp with he | ⟨kids, hk, hks⟩
      · exact he
      · have hd := heads_spec h1 h2 p
        rw [hk] at hd
        obtain ⟨hiff, hrank⟩ := hd
        refine hiff.2 fun k hk' => ih (rank t1 k) (hr ▸ hrank k hk') k rfl ?_
        rcases hks k hk' with h | h
        · exact h
        · cases h
  exact fun p => key (rank t1 p) p rfl

theorem walk_spec {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) (targets : List Pair) :
    ∀ (fuel : Nat) (wl : List Pair) (S : Std.HashSet Pair),
      WalkOk t1 t2 S wl →
        (∀ p ∈ targets, S.contains p = true ∨ p ∈ wl) →
        (∀ p ∈ wl, ¬PairEq t1 t2 p → ∃ q ∈ targets, ¬PairEq t1 t2 q) →
        ∀ r,
          walk t1 t2 fuel wl S = r →
            (r.1 = .equal →
                (∀ p ∈ targets, PairEq t1 t2 p) ∧ ∀ p, r.2.2.contains p = true → PairEq t1 t2 p) ∧
              (r.1 = .differ → ∃ q ∈ targets, ¬PairEq t1 t2 q)
  | fuel, [], S, hc, ht, _, r, hr => by
    rw [walk] at hr
    subst hr
    have hs := closed_sound h1 h2 hc
    refine ⟨fun _ => ⟨fun p hp => ?_, hs⟩, fun h => by cases h⟩
    rcases ht p hp with h | h
    · exact hs p h
    · cases h
  | 0, _ :: _, S, _, _, _, r, hr => by
    rw [walk] at hr
    subst hr
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | fuel + 1, p :: rest, S, hc, ht, hd, r, hr => by
    rw [walk] at hr
    by_cases hp : S.contains p = true
    · simp only [hp, ↓reduceIte] at hr
      refine walk_spec h1 h2 targets fuel rest S ?_ ?_ ?_ r hr
      · intro q hq
        rcases hc q hq with he | ⟨kids, hk, hks⟩
        · exact Or.inl he
        · refine Or.inr ⟨kids, hk, fun k hk' => ?_⟩
          rcases hks k hk' with h | h
          · exact Or.inl h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl hp
            · exact Or.inr h
      · intro q hq
        rcases ht q hq with h | h
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl hp
          · exact Or.inr h
      · exact fun q hq => hd q (List.mem_cons_of_mem _ hq)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hr
      have hs := heads_spec h1 h2 p
      cases hk : heads t1 t2 p with
      | none =>
        rw [hk] at hr hs
        subst hr
        exact ⟨(fun h => by cases h), (fun _ => hd p List.mem_cons_self hs)⟩
      | some kids =>
        rw [hk] at hr hs
        obtain ⟨hiff, _⟩ := hs
        refine walk_spec h1 h2 targets fuel (kids ++ rest) (S.insert p) ?_ ?_ ?_ r hr
        · intro q hq
          rw [Std.HashSet.contains_insert] at hq
          rcases Bool.or_eq_true_iff.1 hq with hq | hq
          · rw [beq_iff_eq] at hq
            subst hq
            exact Or.inr ⟨kids, hk, fun k hk' => Or.inr (List.mem_append_left _ hk')⟩
          · rcases hc q hq with he | ⟨kq, hkq, hks⟩
            · exact Or.inl he
            · refine Or.inr ⟨kq, hkq, fun k hk' => ?_⟩
              rw [Std.HashSet.contains_insert]
              rcases hks k hk' with h | h
              · exact Or.inl (by simp [h])
              · rcases List.mem_cons.1 h with rfl | h
                · exact Or.inl (by simp)
                · exact Or.inr (List.mem_append_right _ h)
        · intro q hq
          rw [Std.HashSet.contains_insert]
          rcases ht q hq with h | h
          · exact Or.inl (by simp [h])
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl (by simp)
            · exact Or.inr (List.mem_append_right _ h)
        · intro q hq hne
          rcases List.mem_append.1 hq with hq | hq
          · exact hd p List.mem_cons_self fun he => hne (hiff.1 he q hq)
          · exact hd q (List.mem_cons_of_mem _ hq) hne

/-- `walk` from a sound memo over the pairs to decide. -/
theorem walk_from {t1 t2 : Tables} (h1 : RawOk t1) (h2 : RawOk t2) (ps : List Pair) (fuel : Nat)
    (seen : Std.HashSet Pair) (hs : ∀ p, seen.contains p = true → PairEq t1 t2 p)
    (r : Cmp × Nat × Std.HashSet Pair) (hr : walk t1 t2 fuel ps seen = r) :
    (r.1 = .equal → (∀ p ∈ ps, PairEq t1 t2 p) ∧ ∀ p, r.2.2.contains p = true → PairEq t1 t2 p) ∧
      (r.1 = .differ → ∃ q ∈ ps, ¬PairEq t1 t2 q) :=
  walk_spec h1 h2 ps fuel ps seen (fun p hp => Or.inl (hs p hp)) (fun _ hp => Or.inr hp)
    (fun p hp hne => ⟨p, hp, hne⟩) r hr

/-! ## Constants: `fieldsMatch` + `pairsOf` = `EntryEq` -/

theorem namesEq_iff (t1 t2 : Tables) (as bs : List Nat) :
    NamesEq t1 t2 as bs ↔ as.length = bs.length ∧ ∀ p ∈ namePairs as bs, PairEq t1 t2 p := by
  simp only [NamesEq, namePairs, List.forall_mem_map]

theorem rulesEq_iff (t1 t2 : Tables) (rs ss : List RuleF) :
    RulesEq t1 t2 rs ss ↔
      (rs.length = ss.length ∧ ∀ p ∈ rs.zip ss, p.1.nfields = p.2.nfields) ∧
        ∀ q ∈ (rs.zip ss).flatMap fun p => [.name p.1.ctor p.2.ctor, .expr p.1.rhs p.2.rhs],
          PairEq t1 t2 q := by
  simp only [RulesEq, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
    forall_exists_index, and_imp]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨⟨hl, fun p hp => (h p hp).2.1⟩, fun q p hp hq => ?_⟩
    rcases hq with rfl | rfl
    · exact (h p hp).1
    · exact (h p hp).2.2
  · rintro ⟨⟨hl, hn⟩, h⟩
    exact ⟨hl, fun p hp => ⟨h _ p hp (Or.inl rfl), hn p hp, h _ p hp (Or.inr rfl)⟩⟩

/-- X7 `declEq`'s two parts: the exact fields (`fieldsMatch`) + the pairs (`pairsOf`) together =
the spec's field-by-field equality. -/
theorem entryEq_iff (t1 t2 : Tables) (e e' : Entry) :
    EntryEq t1 t2 e e' ↔ fieldsMatch e e' = true ∧ ∀ p ∈ pairsOf e e', PairEq t1 t2 p := by
  cases e <;> cases e' <;>
    simp only [EntryEq, fieldsMatch, pairsOf, namesEq_iff, rulesEq_iff, Bool.and_eq_true,
      beq_iff_eq, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true, Bool.false_eq_true, List.all_eq_true] <;>
    first
    | rfl
    | grind

/-! ## The claims -/

/-- U7 X7 `eqExprExact`. -/
theorem eqExpr_exact (githash version : String) (b1 b2 : ByteArray) (t1 t2 : Tables)
    (i j fuel : Nat) (seen : Std.HashSet Pair) (r : Cmp × Nat × Std.HashSet Pair) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      (∀ p, seen.contains p = true → PairEq t1 t2 p) →
      eqExpr t1 i t2 j fuel seen = r →
      (r.1 = .equal → PairEq t1 t2 (.expr i j) ∧ ∀ p, r.2.2.contains p = true → PairEq t1 t2 p) ∧
        (r.1 = .differ → ¬PairEq t1 t2 (.expr i j)) := by
  intro hb1 hb2 hs hr
  have w := walk_from (rawOk_read hb1) (rawOk_read hb2) [.expr i j] fuel seen hs r hr
  refine ⟨fun he => ?_, fun hd => ?_⟩
  · obtain ⟨ht, hs'⟩ := w.1 he
    exact ⟨ht _ List.mem_cons_self, hs'⟩
  · obtain ⟨q, hq, hne⟩ := w.2 hd
    rw [List.mem_singleton] at hq
    subst hq
    exact hne

/-- U7 X7 `declEqExact`. -/
theorem declEq_exact (githash version : String) (b1 b2 : ByteArray) (t1 t2 : Tables) (e e' : Entry)
    (fuel : Nat) (seen : Std.HashSet Pair) (r : Cmp × Nat × Std.HashSet Pair) :
    readTables githash version b1 = .ok t1 →
      readTables githash version b2 = .ok t2 →
      (∀ p, seen.contains p = true → PairEq t1 t2 p) →
      declEq t1 e t2 e' fuel seen = r →
      (r.1 = .equal → EntryEq t1 t2 e e' ∧ ∀ p, r.2.2.contains p = true → PairEq t1 t2 p) ∧
        (r.1 = .differ → ¬EntryEq t1 t2 e e') := by
  intro hb1 hb2 hs hr
  rw [entryEq_iff]
  unfold declEq at hr
  by_cases hf : fieldsMatch e e' = true
  · simp only [hf, ↓reduceIte] at hr
    have w := walk_from (rawOk_read hb1) (rawOk_read hb2) (pairsOf e e') fuel seen hs r hr
    refine ⟨fun he => ?_, fun hd => ?_⟩
    · obtain ⟨ht, hs'⟩ := w.1 he
      exact ⟨⟨hf, ht⟩, hs'⟩
    · obtain ⟨q, hq, hne⟩ := w.2 hd
      exact fun ⟨_, h⟩ => hne (h q hq)
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hr
    subst hr
    exact ⟨(fun h => by cases h), (fun _ ⟨h, _⟩ => hf h)⟩

end FvdepAudit.Judge.Proof
