import FvdepAudit.Index.Rules.Proof.Basic

/-! The worklists against the relations written apart: `reach` decides V3's `ConstReach` (over
library constants), `closure` decides C4's `ImportReach` (each module once). -/

namespace FvdepAudit.Index.Rules.Proof

open Lean FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepAudit.Index.Rules.Spec

/-- `c`'s definition value names `n`. -/
def Succ (F : Facts) (c n : Name) : Prop :=
  ∃ d v, libDecl? F c = some d ∧ d.kind = .defn ∧ d.value = some v ∧ Mentions v n

theorem reachGo_sound (F : Facts) (roots todo seen : List Name)
    (ht : ∀ c ∈ todo, ConstReach F roots c)
    (hs : ∀ c ∈ seen, ConstReach F roots c ∧ libDecl? F c ≠ none) :
    ∀ c ∈ reachGo F todo seen, ConstReach F roots c ∧ libDecl? F c ≠ none := by
  fun_induction reachGo F todo seen with
  | case1 seen => exact hs
  | case2 seen c rest _ ih => exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hs
  | case3 seen c rest _ _ ih => exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hs
  | case4 seen c rest _ d h _ ih =>
    apply ih
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨v, hk, hv, hm⟩ := (mem_bodyConsts d x).mp hx
        exact .step (ht c (by simp)) h hk hv hm
      · exact ht x (List.mem_cons_of_mem _ hx)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨ht x (by simp), by simp [h]⟩
      · exact hs x hx

theorem reachGo_closed (F : Facts) (roots todo seen : List Name)
    (h₁ : ∀ r ∈ roots, libDecl? F r ≠ none → r ∈ seen ∨ r ∈ todo)
    (h₂ : ∀ c ∈ seen, ∀ n, Succ F c n → libDecl? F n ≠ none → n ∈ seen ∨ n ∈ todo) :
    (∀ r ∈ roots, libDecl? F r ≠ none → r ∈ reachGo F todo seen) ∧
      ∀ c ∈ reachGo F todo seen,
        ∀ n, Succ F c n → libDecl? F n ≠ none → n ∈ reachGo F todo seen := by
  fun_induction reachGo F todo seen with
  | case1 seen =>
    exact
      ⟨fun r hr hl => by simpa using h₁ r hr hl, fun c hc n hs hl => by simpa using h₂ c hc n hs hl⟩
  | case2 seen c rest hc ih =>
    apply ih
    · intro r hr hl
      rcases h₁ r hr hl with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl hc
        · exact .inr h
    · intro x hx n hs hl
      rcases h₂ x hx n hs hl with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl hc
        · exact .inr h
  | case3 seen c rest _ hn ih =>
    apply ih
    · intro r hr hl
      rcases h₁ r hr hl with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd hn hl
        · exact .inr h
    · intro x hx n hs hl
      rcases h₂ x hx n hs hl with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd hn hl
        · exact .inr h
  | case4 seen c rest _ d hd _ ih =>
    apply ih
    · intro r hr hl
      rcases h₁ r hr hl with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr (List.mem_append_right _ h)
    · intro x hx n hs hl
      rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨d', v, hd', hk, hv, hm⟩ := hs
        rw [hd] at hd'
        cases hd'
        exact .inr (List.mem_append_left _ ((mem_bodyConsts _ n).mpr ⟨v, hk, hv, hm⟩))
      · rcases h₂ x hx n hs hl with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl List.mem_cons_self
          · exact .inr (List.mem_append_right _ h)

/-- C3 V3: `reach` = the checked constants — reached from the roots through library definition
values, library constants alone. -/
theorem reach_exact (F : Facts) (roots : List Name) (c : Name) :
    c ∈ reach F roots ↔ ConstReach F roots c ∧ libDecl? F c ≠ none := by
  unfold reach
  constructor
  · exact reachGo_sound F roots roots [] (fun x hx => .root hx) (by simp) c
  · rintro ⟨hr, hl⟩
    obtain ⟨hroots, hclosed⟩ := reachGo_closed F roots roots [] (fun r hr _ => .inr hr) (by simp)
    induction hr with
    | root hm => exact hroots _ hm hl
    | step _ hd hk hv hm ih => exact hclosed _ (ih (by simp [hd])) _ ⟨_, _, hd, hk, hv, hm⟩ hl

/-- An `Fvdep` module `a` imports. -/
def ISucc (F : Facts) (a b : Name) : Prop :=
  ∃ x, modFacts? F a = some x ∧ b ∈ x.imports ∧ b.getRoot = `Fvdep

theorem closureGo_sound (F : Facts) (M : Name) (todo seen : List Name)
    (ht : ∀ m ∈ todo, ImportReach F M m) (hs : ∀ m ∈ seen, ImportReach F M m) :
    ∀ m ∈ closureGo F todo seen, ImportReach F M m := by
  fun_induction closureGo F todo seen with
  | case1 seen => exact hs
  | case2 seen m rest _ ih => exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hs
  | case3 seen m rest _ _ _
    ih =>
    apply ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ht x (by simp)
    · exact hs x hx
  | case4 seen m rest _ x hx _ ih =>
    apply ih
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · simp only [List.mem_filter, beq_iff_eq] at hy
        exact .step (ht m (by simp)) hx hy.1 hy.2
      · exact ht y (List.mem_cons_of_mem _ hy)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ht y (by simp)
      · exact hs y hy

theorem closureGo_closed (F : Facts) (M : Name) (todo seen : List Name) (h₁ : M ∈ seen ∨ M ∈ todo)
    (h₂ : ∀ a ∈ seen, ∀ b, ISucc F a b → b ∈ seen ∨ b ∈ todo) :
    M ∈ closureGo F todo seen ∧
      ∀ a ∈ closureGo F todo seen, ∀ b, ISucc F a b → b ∈ closureGo F todo seen := by
  fun_induction closureGo F todo seen with
  | case1 seen => exact ⟨by simpa using h₁, fun a ha b hs => by simpa using h₂ a ha b hs⟩
  | case2 seen m rest hm ih =>
    apply ih
    · rcases h₁ with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl hm
        · exact .inr h
    · intro a ha b hs
      rcases h₂ a ha b hs with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl hm
        · exact .inr h
  | case3 seen m rest _ hn _ ih =>
    apply ih
    · rcases h₁ with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr h
    · intro a ha b hs
      rcases List.mem_cons.mp ha with rfl | ha
      · obtain ⟨x, hx, _, _⟩ := hs
        rw [hn] at hx
        cases hx
      · rcases h₂ a ha b hs with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl List.mem_cons_self
          · exact .inr h
  | case4 seen m rest _ x hx _ ih =>
    apply ih
    · rcases h₁ with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr (List.mem_append_right _ h)
    · intro a ha b hs
      rcases List.mem_cons.mp ha with rfl | ha
      · obtain ⟨x', hx', hb, hr⟩ := hs
        rw [hx] at hx'
        cases hx'
        exact .inr (List.mem_append_left _ (by simp [hb, hr]))
      · rcases h₂ a ha b hs with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl List.mem_cons_self
          · exact .inr (List.mem_append_right _ h)

theorem closureGo_nodup (F : Facts) (todo seen : List Name) (hs : seen.Nodup) :
    (closureGo F todo seen).Nodup := by
  fun_induction closureGo F todo seen with
  | case1 seen => exact hs
  | case2 _ _ _ _ ih => exact ih hs
  | case3 seen m _ hm _ _ ih => exact ih (List.nodup_cons.mpr ⟨hm, hs⟩)
  | case4 seen m _ hm _ _ _ ih => exact ih (List.nodup_cons.mpr ⟨hm, hs⟩)

/-- C4 `ClosureExact`: `closure` holds `M`'s closure, each module once. -/
theorem closure_exact (F : Facts) (M m : Name) :
    (m ∈ closure F M ↔ ImportReach F M m) ∧ (closure F M).Nodup := by
  unfold closure
  refine
    ⟨⟨closureGo_sound F M [M] [] (by simp [ImportReach.self]) (by simp) m, fun h => ?_⟩,
      closureGo_nodup F [M] [] .nil⟩
  obtain ⟨hM, hclosed⟩ := closureGo_closed F M [M] [] (.inr (by simp)) (by simp)
  induction h with
  | self => exact hM
  | step _ hx hb hr ih => exact hclosed _ ih _ ⟨_, hx, hb, hr⟩

end FvdepAudit.Index.Rules.Proof
