import FvdepAudit.Build.Spec

/-! Proofs of K2's plan claims (contract `docs/contracts/U5-sandbox.md` K2; statements =
`FvdepLedger.Rows.BuildClaims`). -/

namespace FvdepAudit.Build.Proof

open FvdepCore.Build FvdepAudit.Build.Spec

/-! ## Names + imports -/

theorem eq_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: xs, h, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, hab.symm⟩ h.1
    · exact absurd ⟨a, ha, hab⟩ h.1
    · exact eq_of_nodup_map f h.2 ha hb hab

theorem importsOf_sub (nodes : List Node) (m i : String) (h : i ∈ importsOf nodes m) :
    Imports nodes m i := by
  unfold importsOf at h
  cases hf : nodes.find? (·.name == m) with
  | none => simp [hf] at h
  | some n =>
    simp only [hf, Option.map_some, Option.getD_some] at h
    have hm := List.mem_of_find?_eq_some hf
    have hn := List.find?_some hf
    exact ⟨n, hm, by simpa using hn, h⟩

theorem importsOf_iff (nodes : List Node) (hn : (names nodes).Nodup) (m i : String) :
    i ∈ importsOf nodes m ↔ Imports nodes m i := by
  refine ⟨importsOf_sub nodes m i, ?_⟩
  rintro ⟨n, hmem, hname, hi⟩
  unfold importsOf
  cases hf : nodes.find? (·.name == m) with
  | none =>
    have := List.find?_eq_none.mp hf n hmem
    simp [hname] at this
  | some n' =>
    have hm' := List.mem_of_find?_eq_some hf
    have hn' : n'.name = m := by simpa using List.find?_some hf
    have hn2 : (nodes.map Node.name).Nodup := hn
    have : n' = n := eq_of_nodup_map Node.name hn2 hm' hmem (by rw [hn', hname])
    subst this
    simpa using hi

theorem importsOf_names (nodes : List Node) (m i : String) (h : i ∈ importsOf nodes m) :
    m ∈ names nodes := by
  obtain ⟨n, hn, hname, _⟩ := importsOf_sub nodes m i h
  exact List.mem_map.mpr ⟨n, hn, hname⟩

theorem importsOf_space (nodes : List Node) (roots : List String) (m i : String)
    (h : i ∈ importsOf nodes m) : i ∈ space nodes roots := by
  obtain ⟨n, hn, _, hi⟩ := importsOf_sub nodes m i h
  simp only [space, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨n, hn, hi⟩

/-! ## Duplicates -/

theorem firstDuplicate_none : ∀ {l : List String}, firstDuplicate l = none → l.Nodup
  | [], _ => List.nodup_nil
  | n :: rest, h => by
    unfold firstDuplicate at h
    split at h
    · cases h
    · rename_i hc
      exact List.nodup_cons.mpr ⟨by simpa using hc, firstDuplicate_none h⟩

theorem firstDuplicate_some :
    ∀ {l : List String} {n : String}, firstDuplicate l = some n → 2 ≤ l.count n
  | [], _, h => by simp [firstDuplicate] at h
  | x :: rest, n, h => by
    unfold firstDuplicate at h
    split at h
    · rename_i hc
      cases h
      have h1 : 0 < rest.count x := List.count_pos_iff.mpr (by simpa using hc)
      rw [List.count_cons_self]
      omega
    · have := firstDuplicate_some h
      rw [List.count_cons]
      split <;> omega

/-! ## Closure -/

/-- Reachable from `todo` through `importsOf`. -/
inductive From (nodes : List Node) (todo : List String) : String → Prop where
  | base {m : String} : m ∈ todo → From nodes todo m
  | step {a i : String} : From nodes todo a → i ∈ importsOf nodes a → From nodes todo i

theorem From.trans {nodes : List Node} {A B : List String} (hAB : ∀ y ∈ A, From nodes B y) :
    ∀ {x}, From nodes A x → From nodes B x
  | _, .base h => hAB _ h
  | _, .step h hi => .step (From.trans hAB h) hi

theorem reach_spec (nodes : List Node) (S : List String)
    (hS : ∀ a i, i ∈ importsOf nodes a → i ∈ S) :
    ∀ (fuel : Nat) (todo seen : List String),
      seen.Nodup →
        (∀ x ∈ seen, x ∈ S) →
        (∀ x ∈ todo, x ∈ S) →
        fuel + seen.length = S.length + 1 →
        (∀ a ∈ seen, ∀ i ∈ importsOf nodes a, i ∈ seen ∨ i ∈ todo) →
        (reach nodes fuel todo seen).Nodup ∧
          (∀ x ∈ seen, x ∈ reach nodes fuel todo seen) ∧
          (∀ x ∈ todo, x ∈ reach nodes fuel todo seen) ∧
          (∀ a ∈ reach nodes fuel todo seen,
            ∀ i ∈ importsOf nodes a, i ∈ reach nodes fuel todo seen) ∧
          ∀ x ∈ reach nodes fuel todo seen, x ∈ seen ∨ From nodes todo x
  | fuel, [], seen, hn, _, _, _, hinv => by
    unfold reach
    refine
      ⟨hn, fun x hx => hx, fun x hx => by simp at hx, fun a ha i hi => ?_, fun x hx => Or.inl hx⟩
    rcases hinv a ha i hi with h | h
    · exact h
    · simp at h
  | 0, m :: rest, seen, hn, hseen, _, hfuel, _ => by
    exfalso
    have := hn.length_le_of_subset hseen
    omega
  | f + 1, m :: rest, seen, hn, hseen, htodo, hfuel, hinv => by
    unfold reach
    by_cases hm : seen.contains m
    · simp only [hm, ↓reduceIte]
      have hm' : m ∈ seen := by simpa using hm
      have ih :=
        reach_spec nodes S hS (f + 1) rest seen hn hseen
          (fun x hx => htodo x (List.mem_cons_of_mem m hx)) hfuel
          (by
            intro a ha i hi
            rcases hinv a ha i hi with h | h
            · exact Or.inl h
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl hm'
              · exact Or.inr h)
      refine ⟨ih.1, ih.2.1, fun x hx => ?_, ih.2.2.2.1, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ih.2.1 _ hm'
        · exact ih.2.2.1 x hx
      · rcases ih.2.2.2.2 x hx with h | h
        · exact Or.inl h
        · exact Or.inr (From.trans (fun y hy => .base (List.mem_cons_of_mem m hy)) h)
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      have hm' : m ∉ seen := by simpa using hm
      have ih :=
        reach_spec nodes S hS f (importsOf nodes m ++ rest) (seen ++ [m])
          ((List.perm_append_singleton m seen).nodup_iff.mpr (List.nodup_cons.mpr ⟨hm', hn⟩))
          (by
            intro x hx
            rcases List.mem_append.mp hx with h | h
            · exact hseen x h
            · simp at h; subst h; exact htodo _ (List.mem_cons_self))
          (by
            intro x hx
            rcases List.mem_append.mp hx with h | h
            · exact hS m x h
            · exact htodo x (List.mem_cons_of_mem m h))
          (by
            simp; omega)
          (by
            intro a ha i hi
            rcases List.mem_append.mp ha with ha | ha
            · rcases hinv a ha i hi with h | h
              · exact Or.inl (List.mem_append_left _ h)
              · rcases List.mem_cons.mp h with rfl | h
                · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
                · exact Or.inr (List.mem_append_right _ h)
            · simp at ha; subst ha
              exact Or.inr (List.mem_append_left _ hi))
      refine
        ⟨ih.1, fun x hx => ih.2.1 x (List.mem_append_left _ hx), fun x hx => ?_, ih.2.2.2.1,
          fun x hx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ih.2.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
        · exact ih.2.2.1 x (List.mem_append_right _ hx)
      · rcases ih.2.2.2.2 x hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · simp at h; subst h; exact Or.inr (.base List.mem_cons_self)
        · refine Or.inr (From.trans (fun y hy => ?_) h)
          rcases List.mem_append.mp hy with hy | hy
          · exact .step (.base List.mem_cons_self) hy
          · exact .base (List.mem_cons_of_mem m hy)
termination_by fuel todo => (fuel, todo.length)

theorem space_cover (nodes : List Node) (roots : List String) :
    ∀ a i, i ∈ importsOf nodes a → i ∈ space nodes roots := fun a i h =>
  importsOf_space nodes roots a i h

/-- The closure: no repeats, the roots + every import of a member, nothing else. -/
theorem closure_spec (nodes : List Node) (roots : List String) :
    (closure nodes roots).Nodup ∧
      (∀ x, x ∈ closure nodes roots ↔ From nodes roots x) ∧
      ∀ a ∈ closure nodes roots, ∀ i ∈ importsOf nodes a, i ∈ closure nodes roots := by
  have h :=
    reach_spec nodes (space nodes roots) (space_cover nodes roots) ((space nodes roots).length + 1)
      roots [] List.nodup_nil (by simp)
      (fun x hx => by
        simp only [space, List.mem_append]; exact Or.inl hx)
      (by simp) (by simp)
  refine ⟨h.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, h.2.2.2.1⟩
  · rcases h.2.2.2.2 x hx with h' | h'
    · simp at h'
    · exact h'
  · induction hx with
    | base hm => exact h.2.2.1 _ hm
    | step _ hi ih => exact h.2.2.2.1 _ ih _ hi

/-- Under unique names, `From` over `importsOf` = the spec's `Reach`. -/
theorem from_iff_reach (nodes : List Node) (roots : List String) (hn : (names nodes).Nodup)
    (x : String) : From nodes roots x ↔ Reach nodes roots x := by
  constructor
  · intro h
    induction h with
    | base hm => exact .root hm
    | step _ hi ih => exact .step ih ((importsOf_iff nodes hn _ _).mp hi)
  · intro h
    induction h with
    | root hm => exact .base hm
    | step _ hi ih => exact .step ih ((importsOf_iff nodes hn _ _).mpr hi)

/-! ## Missing modules -/

theorem firstMissing_none {nodes : List Node} {c : List String} (h : firstMissing nodes c = none) :
    ∀ m ∈ c, m ∈ names nodes := by
  unfold firstMissing at h
  split at h
  · rename_i hf
    intro m hm
    have := List.find?_eq_none.mp hf m hm
    simpa using this
  · split at h <;> cases h

theorem firstMissing_some {nodes : List Node} {c : List String} {a : Option String} {t : String}
    (h : firstMissing nodes c = some (a, t)) :
    t ∈ c ∧
      t ∉ names nodes ∧
      (∀ x, a = some x → x ∈ c ∧ x ∈ names nodes ∧ t ∈ importsOf nodes x) ∧
      (a = none → ∀ x ∈ c, x ∈ names nodes → t ∉ importsOf nodes x) := by
  unfold firstMissing at h
  split at h
  · cases h
  · rename_i t' ht
    have htc := List.mem_of_find?_eq_some ht
    have htn : t' ∉ names nodes := by simpa using List.find?_some ht
    split at h
    · rename_i x hx
      cases h
      have hxc := List.mem_of_find?_eq_some hx
      have hxp := List.find?_some hx
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hxp
      exact
        ⟨htc, htn,
          (fun y hy => by
            cases hy; exact ⟨hxc, hxp.1, hxp.2⟩),
          (fun hn => by cases hn)⟩
    · rename_i hx
      cases h
      refine ⟨htc, htn, (fun y hy => by cases hy), fun _ x hxc hxn hxi => ?_⟩
      have := List.find?_eq_none.mp hx x hxc
      simp [hxn, hxi] at this

/-! ## Layering -/

theorem lt_of_getElem? {l : List String} {k : Nat} {a : String} (h : l[k]? = some a) :
    k < l.length := (List.getElem?_eq_some_iff.mp h).1

theorem before_append_left {l r : List String} {i m : String} (h : Before l i m) :
    Before (l ++ r) i m := by
  obtain ⟨k, k', hk, hk', hlt⟩ := h
  refine ⟨k, k', ?_, ?_, hlt⟩
  · rw [List.getElem?_append_left (lt_of_getElem? hk)]; exact hk
  · rw [List.getElem?_append_left (lt_of_getElem? hk')]; exact hk'

theorem before_append_mid {l r : List String} {i m : String} (hi : i ∈ l) (hm : m ∈ r) :
    Before (l ++ r) i m := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hm
  have hk1 := lt_of_getElem? hk
  refine ⟨k, l.length + k', ?_, ?_, by omega⟩
  · rw [List.getElem?_append_left hk1]; exact hk
  · rw [List.getElem?_append_right (by omega)]; simpa using hk'

theorem layer_spec (nodes : List Node) :
    ∀ (fuel : Nat) (rem done : List String),
      done.Nodup →
        rem.Nodup →
        (∀ x ∈ done, x ∉ rem) →
        rem.length ≤ fuel →
        (∀ m ∈ done, ∀ i ∈ importsOf nodes m, Before done i m) →
        (∀ m, m ∈ done ∨ m ∈ rem → ∀ i ∈ importsOf nodes m, i ∈ done ∨ i ∈ rem) →
        match layer nodes fuel rem done with
        | .ok order =>
          order.Nodup ∧
            (∀ x, x ∈ order ↔ x ∈ done ∨ x ∈ rem) ∧
            ∀ m ∈ order, ∀ i ∈ importsOf nodes m, Before order i m
        | .error (.stuck ms) =>
          ms ≠ [] ∧ (∀ m ∈ ms, m ∈ rem) ∧ ∀ m ∈ ms, ∃ i ∈ importsOf nodes m, i ∈ ms
        | .error _ => False
  | _, [], done, hd, _, _, _, hb, _ => by
    unfold layer
    exact ⟨hd, fun x => by simp, hb⟩
  | 0, m :: rest, _, _, _, _, hf, _, _ => by simp at hf
  | f + 1, m :: rest, done, hd, hr, hdis, hf, hb, hcl => by
    unfold layer
    generalize hR : (m :: rest).filter (fun m => (importsOf nodes m).all done.contains) = ready
    have hrd : ∀ x, x ∈ ready ↔ x ∈ m :: rest ∧ (importsOf nodes x).all done.contains = true := by
      intro x; rw [← hR]; exact List.mem_filter
    by_cases hready : ready.isEmpty
    · simp only [hready, ↓reduceIte]
      refine ⟨by simp, fun x hx => hx, fun x hx => ?_⟩
      have hnot : ¬((importsOf nodes x).all done.contains = true) := by
        intro hall
        have : x ∈ ready := (hrd x).mpr ⟨hx, hall⟩
        simp_all
      have hex : ∃ i ∈ importsOf nodes x, i ∉ done := by
        apply Classical.byContradiction
        intro hno
        apply hnot
        simp only [List.all_eq_true, List.contains_iff_mem]
        intro i hi
        apply Classical.byContradiction
        intro hni
        exact hno ⟨i, hi, hni⟩
      obtain ⟨i, hi, hni⟩ := hex
      refine ⟨i, hi, ?_⟩
      rcases hcl x (Or.inr hx) i hi with h | h
      · exact absurd h hni
      · exact h
    · simp only [hready, Bool.false_eq_true, ↓reduceIte]
      have hne : ready ≠ [] := by simpa using hready
      have hrem' :
        ∀ x, x ∈ (m :: rest).filter (fun x => !ready.contains x) ↔ x ∈ m :: rest ∧ x ∉ ready := by
        intro x; simp [List.mem_filter]
      have ih :=
        layer_spec nodes f ((m :: rest).filter fun x => !ready.contains x) (done ++ ready)
          (by
            refine List.nodup_append.mpr ⟨hd, ?_, ?_⟩
            · rw [← hR]; exact List.Pairwise.filter _ hr
            · intro a ha b hb hab
              subst hab
              exact hdis a ha ((hrd a).mp hb).1)
          (List.Pairwise.filter _ hr)
          (by
            intro x hx hx'
            rcases List.mem_append.mp hx with hx | hx
            · exact hdis x hx ((hrem' x).mp hx').1
            · exact ((hrem' x).mp hx').2 hx)
          (by
            have : ((m :: rest).filter fun x => !ready.contains x).length < (m :: rest).length := by
              apply List.length_filter_lt_length_iff_exists.mpr
              obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil ready hne
              exact ⟨y, ((hrd y).mp hy).1, by simpa using hy⟩
            simp only [List.length_cons] at this hf ⊢
            omega)
          (by
            intro x hx i hi
            rcases List.mem_append.mp hx with hx | hx
            · exact before_append_left (hb x hx i hi)
            · have hall := ((hrd x).mp hx).2
              simp only [List.all_eq_true, List.contains_iff_mem] at hall
              exact before_append_mid (hall i hi) hx)
          (by
            intro x hx i hi
            have hx2 : x ∈ done ∨ x ∈ m :: rest := by
              rcases hx with hx | hx
              · rcases List.mem_append.mp hx with hx | hx
                · exact Or.inl hx
                · exact Or.inr ((hrd x).mp hx).1
              · exact Or.inr ((hrem' x).mp hx).1
            rcases hcl x hx2 i hi with h | h
            · exact Or.inl (List.mem_append_left _ h)
            · by_cases hir : i ∈ ready
              · exact Or.inl (List.mem_append_right _ hir)
              · exact Or.inr ((hrem' i).mpr ⟨h, hir⟩))
      generalize layer nodes f ((m :: rest).filter fun x => !ready.contains x) (done ++ ready) =
        r at ih ⊢
      rcases r with _ | order
      · rename_i e
        cases e with
        | stuck ms => exact ⟨ih.1, fun x hx => ((hrem' x).mp (ih.2.1 x hx)).1, ih.2.2⟩
        | duplicate _ => exact ih.elim
        | missing _ _ => exact ih.elim
      · refine ⟨ih.1, fun x => ?_, ih.2.2⟩
        rw [ih.2.1 x, List.mem_append, hrem' x]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr ((hrd x).mp h).1
          · exact Or.inr h.1
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · by_cases hx : x ∈ ready
            · exact Or.inl (Or.inr hx)
            · exact Or.inr ⟨h, hx⟩

/-! ## The plan -/

theorem plan_cases {nodes : List Node} {roots : List String} {r : Except Refusal (List String)}
    (h : plan nodes roots = r) :
    (∃ n, firstDuplicate (names nodes) = some n ∧ r = .error (.duplicate n)) ∨
      ((names nodes).Nodup ∧
        ((∃ a t,
            firstMissing nodes (closure nodes roots) = some (a, t) ∧ r = .error (.missing a t)) ∨
          (firstMissing nodes (closure nodes roots) = none ∧
            r = layer nodes (closure nodes roots).length (closure nodes roots) []))) := by
  unfold plan at h
  cases hd : firstDuplicate (names nodes) with
  | some n =>
    exact
      Or.inl
        ⟨n, rfl, by
          rw [hd] at h; exact h.symm⟩
  | none =>
    rw [hd] at h
    refine Or.inr ⟨firstDuplicate_none hd, ?_⟩
    cases hm : firstMissing nodes (closure nodes roots) with
    | some p =>
      exact
        Or.inl
          ⟨p.1, p.2, rfl, by
            simp only [hm] at h; exact h.symm⟩
    | none =>
      exact
        Or.inr
          ⟨rfl, by
            simp only [hm] at h; exact h.symm⟩

theorem layer_closure (nodes : List Node) (roots : List String) :
    match layer nodes (closure nodes roots).length (closure nodes roots) [] with
    | .ok order =>
      order.Nodup ∧
        (∀ x, x ∈ order ↔ x ∈ [] ∨ x ∈ closure nodes roots) ∧
        ∀ m ∈ order, ∀ i ∈ importsOf nodes m, Before order i m
    | .error (.stuck ms) =>
      ms ≠ [] ∧ (∀ m ∈ ms, m ∈ closure nodes roots) ∧ ∀ m ∈ ms, ∃ i ∈ importsOf nodes m, i ∈ ms
    | .error _ => False := by
  have hc := closure_spec nodes roots
  exact
    layer_spec nodes _ _ [] List.nodup_nil hc.1 (by simp) (Nat.le_refl _) (by simp)
      (fun m hm i hi =>
        Or.inr
          (by
            rcases hm with hm | hm
            · simp at hm
            · exact hc.2.2 m hm i hi))

/-- K2: a planned order is a valid build order of the closure. -/
theorem plan_ok (nodes : List Node) (roots order : List String) (h : plan nodes roots = .ok order) :
    ValidOrder nodes roots order := by
  rcases plan_cases h with ⟨n, _, hr⟩ | ⟨hn, ⟨a, t, _, hr⟩ | ⟨hm, hr⟩⟩
  · cases hr
  · cases hr
  · have hl := layer_closure nodes roots
    rw [← hr] at hl
    have hc := closure_spec nodes roots
    refine ⟨hl.1, fun x => ?_, fun x hx => ?_, fun x hx i hi => ?_⟩
    · rw [hl.2.1 x, ← from_iff_reach nodes roots hn x, ← hc.2.1 x]
      simp
    · exact firstMissing_none hm x (by simpa using (hl.2.1 x).mp hx)
    · exact hl.2.2 x hx i ((importsOf_iff nodes hn x i).mpr hi)

/-- K2: a duplicate refusal names a module two nodes share. -/
theorem plan_duplicate (nodes : List Node) (roots : List String) (n : String)
    (h : plan nodes roots = .error (.duplicate n)) : 2 ≤ (nodes.map (·.name)).count n := by
  rcases plan_cases h with ⟨n', hd, hr⟩ | ⟨_, ⟨a, t, _, hr⟩ | ⟨_, hr⟩⟩
  · cases hr; exact firstDuplicate_some hd
  · cases hr
  · have hl := layer_closure nodes roots
    rw [← hr] at hl
    exact hl.elim

/-- K2: a missing refusal names a reached module no node provides, + a reached module importing it
(or none: then it is a root). -/
theorem plan_missing (nodes : List Node) (roots : List String) (a : Option String) (t : String)
    (h : plan nodes roots = .error (.missing a t)) :
    Reach nodes roots t ∧
      t ∉ nodes.map (·.name) ∧
      (∀ x, a = some x → Reach nodes roots x ∧ Imports nodes x t) ∧ (a = none → t ∈ roots) := by
  rcases plan_cases h with ⟨n, _, hr⟩ | ⟨hn, ⟨a', t', hm, hr⟩ | ⟨_, hr⟩⟩
  · cases hr
  · cases hr
    have hc := closure_spec nodes roots
    have hs := firstMissing_some hm
    refine
      ⟨(from_iff_reach nodes roots hn t).mp ((hc.2.1 t).mp hs.1), hs.2.1, fun x hx => ?_, fun ha =>
        ?_⟩
    · have := hs.2.2.1 x hx
      exact
        ⟨(from_iff_reach nodes roots hn x).mp ((hc.2.1 x).mp this.1),
          importsOf_sub nodes x t this.2.2⟩
    · have hfrom := (hc.2.1 t).mp hs.1
      cases hfrom with
      | base hm' => exact hm'
      | step hx hi =>
        rename_i x
        exact absurd hi (hs.2.2.2 ha x ((hc.2.1 x).mpr hx) (importsOf_names nodes x t hi))
  · have hl := layer_closure nodes roots
    rw [← hr] at hl
    exact hl.elim

/-- K2: a stuck refusal names reached modules, nonempty, each importing another of them. -/
theorem plan_stuck (nodes : List Node) (roots ms : List String)
    (h : plan nodes roots = .error (.stuck ms)) :
    ms ≠ [] ∧ ∀ m ∈ ms, Reach nodes roots m ∧ ∃ i, Imports nodes m i ∧ i ∈ ms := by
  rcases plan_cases h with ⟨n, _, hr⟩ | ⟨hn, ⟨a, t, _, hr⟩ | ⟨_, hr⟩⟩
  · cases hr
  · cases hr
  · have hl := layer_closure nodes roots
    rw [← hr] at hl
    have hc := closure_spec nodes roots
    refine
      ⟨hl.1, fun m hm => ⟨(from_iff_reach nodes roots hn m).mp ((hc.2.1 m).mp (hl.2.1 m hm)), ?_⟩⟩
    obtain ⟨i, hi, him⟩ := hl.2.2 m hm
    exact ⟨i, importsOf_sub nodes m i hi, him⟩

theorem index_unique {order : List String} (hn : order.Nodup) {a b : Nat} {x : String}
    (ha : order[a]? = some x) (hb : order[b]? = some x) : a = b :=
  (hn.getElem?_inj (lt_of_getElem? ha)).mp (by rw [ha, hb])

/-- K2: a missing or stuck refusal ⇒ no valid build order exists. -/
theorem plan_refuses (nodes : List Node) (roots : List String) (r : Refusal)
    (h : plan nodes roots = .error r) (hr : ∀ n, r ≠ .duplicate n) :
    ¬∃ order, ValidOrder nodes roots order := by
  rintro ⟨order, hno, hmem, hnames, hbefore⟩
  cases r with
  | duplicate n => exact hr n rfl
  | missing a t =>
    have hm := plan_missing nodes roots a t h
    exact hm.2.1 (hnames t ((hmem t).mpr hm.1))
  | stuck ms =>
    have hs := plan_stuck nodes roots ms h
    have key : ∀ k : Nat, ∀ m ∈ ms, order[k]? = some m → False := by
      intro k
      induction k using Nat.strongRecOn with
      | _ k ih =>
        intro m hm hk
        obtain ⟨_, i, hi, hims⟩ := hs.2 m hm
        obtain ⟨k', l, hk', hl, hlt⟩ := hbefore m ((hmem m).mpr (hs.2 m hm).1) i hi
        have := index_unique hno hl hk
        subst this
        exact ih k' hlt i hims hk'
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil ms hs.1
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ((hmem m).mpr (hs.2 m hm).1)
    exact key k m hm hk

end FvdepAudit.Build.Proof
