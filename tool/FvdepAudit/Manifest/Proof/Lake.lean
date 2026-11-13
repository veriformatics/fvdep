import FvdepAudit.Manifest.Spec

/-! T5 `OfLakeExact`: `ofLake` rebuilds Lake's table as the related `Tree` whenever every key is one
string component, and otherwise names a key of another shape. -/

namespace FvdepAudit.Manifest.Proof

open Lean FvdepCore.Manifest FvdepIO.Toml FvdepAudit.Manifest.Spec

theorem map_ok {α β ε : Type} (f : α → β) (x : Except ε α) (b : β) :
    f <$> x = .ok b ↔ ∃ a, x = .ok a ∧ b = f a := by
  cases x <;> simp [Functor.map, Except.map, eq_comm]

theorem map_error {α β ε : Type} (f : α → β) (x : Except ε α) (e : ε) :
    f <$> x = .error e ↔ x = .error e := by cases x <;> simp [Functor.map, Except.map]

mutual
theorem ofValue_ok : ∀ (v : Lake.Toml.Value) (t : Tree), ofValue v = .ok t ↔ LakeRel v t
  | .string _ s, t => by simp [ofValue, LakeRel, eq_comm]
  | .integer _ n, t => by simp [ofValue, LakeRel, eq_comm]
  | .float .., t => by simp [ofValue, LakeRel, eq_comm]
  | .boolean _ b, t => by simp [ofValue, LakeRel, eq_comm]
  | .dateTime .., t => by simp [ofValue, LakeRel, eq_comm]
  | .array _ xs, t => by
    simp only [ofValue, LakeRel, map_ok]
    constructor
    · rintro ⟨ts, h, rfl⟩
      exact ⟨ts, rfl, (ofValues_ok xs.toList ts).mp h⟩
    · rintro ⟨ts, rfl, h⟩
      exact ⟨ts, (ofValues_ok xs.toList ts).mpr h, rfl⟩
  | .table' _ d, t => by
    simp only [ofValue, LakeRel, map_ok]
    constructor
    · rintro ⟨ms, h, rfl⟩
      exact ⟨ms, rfl, (ofMembers_ok d.items.toList ms).mp h⟩
    · rintro ⟨ms, rfl, h⟩
      exact ⟨ms, (ofMembers_ok d.items.toList ms).mpr h, rfl⟩
theorem ofValues_ok :
    ∀ (xs : List Lake.Toml.Value) (ts : List Tree), ofValues xs = .ok ts ↔ LakeRels xs ts
  | [], ts => by simp [ofValues, LakeRels, eq_comm]
  | x :: xs, ts => by
    simp only [ofValues, LakeRels]
    cases hx : ofValue x with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
      intro t ts' _ hr _
      have := (ofValue_ok x t).mpr hr
      rw [hx] at this
      cases this
    | ok t =>
      have hr := (ofValue_ok x t).mp hx
      cases hxs : ofValues xs with
      | error e =>
        simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
        intro t' ts' _ _ hrs
        have := (ofValues_ok xs ts').mpr hrs
        rw [hxs] at this
        cases this
      | ok ts' =>
        have hrs := (ofValues_ok xs ts').mp hxs
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl
          exact ⟨t, ts', rfl, hr, hrs⟩
        · rintro ⟨t₁, ts₁, rfl, h₁, h₂⟩
          have e1 := (ofValue_ok x t₁).mpr h₁
          have e2 := (ofValues_ok xs ts₁).mpr h₂
          rw [hx] at e1
          rw [hxs] at e2
          cases e1
          cases e2
          rfl
theorem ofMembers_ok :
    ∀ (xs : List (Name × Lake.Toml.Value)) (ms : List (String × Tree)),
      ofMembers xs = .ok ms ↔ LakeMembers xs ms
  | [], ms => by simp [ofMembers, LakeMembers, eq_comm]
  | (n, x) :: xs, ms => by
    simp only [ofMembers, LakeMembers]
    split
    · rename_i s
      cases hx : ofValue x with
      | error e =>
        simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
        intro s' t ms' _ _ hr _
        have := (ofValue_ok x t).mpr hr
        rw [hx] at this
        cases this
      | ok t =>
        have hr := (ofValue_ok x t).mp hx
        cases hxs : ofMembers xs with
        | error e =>
          simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
          intro s' t' ms' _ _ _ hrs
          have := (ofMembers_ok xs ms').mpr hrs
          rw [hxs] at this
          cases this
        | ok ms' =>
          have hrs := (ofMembers_ok xs ms').mp hxs
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
          constructor
          · rintro rfl
            exact ⟨s, t, ms', rfl, rfl, hr, hrs⟩
          · rintro ⟨s₁, t₁, ms₁, rfl, hs, h₁, h₂⟩
            simp only [Name.str.injEq, true_and] at hs
            subst hs
            have e1 := (ofValue_ok x t₁).mpr h₁
            have e2 := (ofMembers_ok xs ms₁).mpr h₂
            rw [hx] at e1
            rw [hxs] at e2
            cases e1
            cases e2
            rfl
    · rename_i hn
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro s _ _ _ hs
      exact (hn s hs).elim
end

mutual
theorem ofValue_error :
    ∀ (v : Lake.Toml.Value) (n : Name),
      ofValue v = .error n → n ∈ keysIn v ∧ ∀ s, n ≠ .str .anonymous s
  | .string .., _, h => by simp [ofValue] at h
  | .integer .., _, h => by simp [ofValue] at h
  | .float .., _, h => by simp [ofValue] at h
  | .boolean .., _, h => by simp [ofValue] at h
  | .dateTime .., _, h => by simp [ofValue] at h
  | .array _ xs, n, h => by
    simp only [ofValue, map_error] at h
    simpa [keysIn] using ofValues_error xs.toList n h
  | .table' _ d, n, h => by
    simp only [ofValue, map_error] at h
    simpa [keysIn] using ofMembers_error d.items.toList n h
theorem ofValues_error :
    ∀ (xs : List Lake.Toml.Value) (n : Name),
      ofValues xs = .error n → n ∈ keysInList xs ∧ ∀ s, n ≠ .str .anonymous s
  | [], _, h => by simp [ofValues] at h
  | x :: xs, n, h => by
    simp only [ofValues] at h
    cases hx : ofValue x with
    | error e =>
      simp only [hx, bind, Except.bind, Except.error.injEq] at h
      subst h
      have := ofValue_error x e hx
      exact ⟨by simp [keysInList, this.1], this.2⟩
    | ok t =>
      cases hxs : ofValues xs with
      | error e =>
        simp only [hx, hxs, bind, Except.bind, Except.error.injEq] at h
        subst h
        have := ofValues_error xs e hxs
        exact ⟨by simp [keysInList, this.1], this.2⟩
      | ok ts => simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
theorem ofMembers_error :
    ∀ (xs : List (Name × Lake.Toml.Value)) (n : Name),
      ofMembers xs = .error n → n ∈ keysInMembers xs ∧ ∀ s, n ≠ .str .anonymous s
  | [], _, h => by simp [ofMembers] at h
  | (k, x) :: xs, n, h => by
    simp only [ofMembers] at h
    split at h
    · cases hx : ofValue x with
      | error e =>
        simp only [hx, bind, Except.bind, Except.error.injEq] at h
        subst h
        have := ofValue_error x e hx
        exact ⟨by simp [keysInMembers, this.1], this.2⟩
      | ok t =>
        cases hxs : ofMembers xs with
        | error e =>
          simp only [hx, hxs, bind, Except.bind, Except.error.injEq] at h
          subst h
          have := ofMembers_error xs e hxs
          exact ⟨by simp [keysInMembers, this.1], this.2⟩
        | ok ms => simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
    · rename_i hn
      simp only [Except.error.injEq] at h
      subst h
      exact ⟨by simp [keysInMembers], fun s hs => hn s hs⟩
end

/-- T5 `OfLakeExact`. -/
theorem ofLake_exact (d : Lake.Toml.Table) :
    (∀ t, ofLake d = .ok t ↔ ∃ ms, t = .tbl ms ∧ LakeMembers d.items.toList ms) ∧
      (∀ n, ofLake d = .error n → BadKey d n) ∧ ((∀ n, ¬BadKey d n) → ∃ t, ofLake d = .ok t) := by
  have hok : ∀ t, ofLake d = .ok t ↔ ∃ ms, t = .tbl ms ∧ LakeMembers d.items.toList ms := by
    intro t
    simp only [ofLake, map_ok]
    constructor
    · rintro ⟨ms, h, rfl⟩
      exact ⟨ms, rfl, (ofMembers_ok _ ms).mp h⟩
    · rintro ⟨ms, rfl, h⟩
      exact ⟨ms, (ofMembers_ok _ ms).mpr h, rfl⟩
  have herr : ∀ n, ofLake d = .error n → BadKey d n := by
    intro n h
    simp only [ofLake, map_error] at h
    exact ofMembers_error _ n h
  refine ⟨hok, herr, fun hn => ?_⟩
  cases h : ofLake d with
  | ok t => exact ⟨t, rfl⟩
  | error n => exact absurd (herr n h) (hn n)

end FvdepAudit.Manifest.Proof
