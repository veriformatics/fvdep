import FvdepAudit.Index.Rules.Proof.Reach

/-! Each shipped check against its row (`RowOk`), the rows in C9's order (`Corr`), and the claims:
`validate` = none exactly when every rule holds; a refusal = the first failing row's report. -/

namespace FvdepAudit.Index.Rules.Proof

open Lean FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepAudit.Index.Rules.Spec

/-- A shipped check agrees with its row: `none` exactly when the row passes; a refusal is one the
row may report. -/
def RowOk (c : Option Found) (r : Row) : Prop := (c = none ↔ r.1) ∧ ∀ f, c = some f → r.2 f

/-- Shipped checks ↔ rows, position by position. -/
inductive Corr : List (Option Found) → List Row → Prop
  | nil : Corr [] []
  |
  cons {c : Option Found} {r : Row} {cs : List (Option Found)} {rs : List Row} :
    RowOk c r → Corr cs rs → Corr (c :: cs) (r :: rs)

theorem Corr.append {cs₁ cs₂ : List (Option Found)} {rs₁ rs₂ : List Row} (h₁ : Corr cs₁ rs₁)
    (h₂ : Corr cs₂ rs₂) : Corr (cs₁ ++ cs₂) (rs₁ ++ rs₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem corr_map {α : Type} (xs : List α) (f : α → Option Found) (g : α → Row)
    (h : ∀ x ∈ xs, RowOk (f x) (g x)) : Corr (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem corr_flatMap {α : Type} (xs : List α) (f : α → List (Option Found)) (g : α → List Row)
    (h : ∀ x ∈ xs, Corr (f x) (g x)) : Corr (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih fun y hy => h y (by simp [hy]))

theorem head_none {cs : List (Option Found)} {rs : List Row} (h : Corr cs rs) :
    (cs.filterMap id).head? = none ↔ ∀ r ∈ rs, r.1 := by
  induction h with
  | nil => simp
  | @cons c r cs rs hr _ ih =>
    cases c with
    | none =>
      rw [show ((none :: cs).filterMap id).head? = (cs.filterMap id).head? from rfl, ih]
      simp [hr.1.mp rfl]
    | some f =>
      have hn : ¬r.1 := fun hp => by simpa using hr.1.mpr hp
      simp [hn]

theorem head_some {cs : List (Option Found)} {rs : List Row} {f : Found} (h : Corr cs rs)
    (hf : (cs.filterMap id).head? = some f) : FirstFail rs f := by
  induction h with
  | nil => simp at hf
  | @cons c r cs rs hr _ ih =>
    cases c with
    | none =>
      simp only [List.filterMap_cons, id] at hf
      obtain ⟨pre, x, post, e, hpre, hx, hfx⟩ := ih hf
      exact
        ⟨r :: pre, x, post, by simp [e], fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hr.1.mp rfl
          · exact hpre y hy, hx, hfx⟩
    | some g =>
      simp only [List.filterMap_cons, id, List.head?_cons, Option.some.injEq] at hf
      subst hf
      exact ⟨[], r, rs, rfl, by simp, fun hp => by simpa using hr.1.mpr hp, hr.2 _ rfl⟩

/-! ## Row lemmas -/

theorem rowOk_fail {b : Bool} {P : Prop} (s : String) (v : Violation) (h : b = true ↔ P) :
    RowOk ((fail b v).map (s, ·)) (row P (s, v)) := by
  unfold RowOk row fail
  cases b <;> simp_all

theorem rowOk_least {xs : List Name} {P : Name → Prop} (report : Name → Found)
    (h : ∀ c, c ∈ xs ↔ P c) : RowOk ((least xs).map report) (leastRow P report) := by
  obtain ⟨hn, hs⟩ := least_carriers h
  refine ⟨by simp [leastRow, hn], fun f hf => ?_⟩
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hf
  exact ⟨c, hs c hc, rfl⟩

theorem rowOk_find {xs : List Name} {p : Name → Bool} {P : Name → Prop}
    (hp : ∀ x, p x = true ↔ ¬P x) (report : Name → Found) :
    RowOk ((xs.find? p).map report)
      (∀ x ∈ xs, P x, fun f =>
        ∃ pre x post, xs = pre ++ x :: post ∧ (∀ y ∈ pre, P y) ∧ ¬P x ∧ f = report x) := by
  refine ⟨?_, fun f hf => ?_⟩
  · simp only [Option.map_eq_none_iff, List.find?_eq_none]
    exact
      ⟨fun h x hx => Classical.byContradiction fun hn => h x hx ((hp x).mpr hn), fun h x hx hpx =>
        (hp x).mp hpx (h x hx)⟩
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hf
    obtain ⟨hpx, pre, post, e, hpre⟩ := List.find?_eq_some_iff_append.mp hx
    refine ⟨pre, x, post, e, fun y hy => ?_, (hp x).mp hpx, rfl⟩
    have := hpre y hy
    simp only [Bool.not_eq_true'] at this
    exact Classical.byContradiction fun hn => by simp [(hp y).mpr hn] at this

theorem firstRepeat_go (xs S : List Name) :
    (firstRepeat.go xs S = none ↔ xs.Nodup ∧ ∀ x ∈ xs, x ∉ S) ∧
      ∀ o,
        firstRepeat.go xs S = some o →
          ∃ pre post,
            xs = pre ++ o :: post ∧ pre.Nodup ∧ (∀ x ∈ pre, x ∉ S) ∧ (o ∈ S ∨ o ∈ pre) := by
  induction xs generalizing S with
  | nil => simp [firstRepeat.go]
  | cons x xs ih =>
    by_cases hx : x ∈ S
    · simp only [firstRepeat.go, hx, ↓reduceIte, reduceCtorEq, false_iff, Option.some.injEq]
      refine
        ⟨fun h => h.2 x (by simp) hx, fun o ho =>
          ⟨[], xs, by simp [ho], .nil, by simp, .inl (ho ▸ hx)⟩⟩
    · simp only [firstRepeat.go, hx, ↓reduceIte]
      obtain ⟨h₁, h₂⟩ := ih (x :: S)
      refine ⟨?_, fun o ho => ?_⟩
      · rw [h₁]
        constructor
        · rintro ⟨hn, hall⟩
          refine ⟨List.nodup_cons.mpr ⟨fun hm => hall x hm List.mem_cons_self, hn⟩, fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact fun hs => hall y hy (List.mem_cons_of_mem _ hs)
        · rintro ⟨hnd, hall⟩
          obtain ⟨hxs, hn⟩ := List.nodup_cons.mp hnd
          refine ⟨hn, fun y hy hyS => ?_⟩
          rcases List.mem_cons.mp hyS with rfl | hyS
          · exact hxs hy
          · exact hall y (List.mem_cons_of_mem _ hy) hyS
      · obtain ⟨pre, post, e, hn, hpre, ho'⟩ := h₂ o ho
        refine ⟨x :: pre, post, by simp [e], ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨fun hm => (hpre x hm) (by simp), hn⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact fun hs => hpre y hy (List.mem_cons_of_mem _ hs)
        · rcases ho' with ho' | ho'
          · rcases List.mem_cons.mp ho' with rfl | ho'
            · exact .inr (by simp)
            · exact .inl ho'
          · exact .inr (List.mem_cons_of_mem _ ho')

theorem rowOk_repeat (xs : List Name) (report : Name → Found) :
    RowOk ((firstRepeat xs).map report)
      (xs.Nodup, fun f =>
        ∃ pre o post, xs = pre ++ o :: post ∧ pre.Nodup ∧ o ∈ pre ∧ f = report o) := by
  obtain ⟨h₁, h₂⟩ := firstRepeat_go xs []
  refine ⟨by simp [firstRepeat, h₁], fun f hf => ?_⟩
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨pre, post, e, hn, _, ho'⟩ := h₂ o ho
  exact ⟨pre, o, post, e, hn, ho'.resolve_left (by simp), rfl⟩

end FvdepAudit.Index.Rules.Proof
