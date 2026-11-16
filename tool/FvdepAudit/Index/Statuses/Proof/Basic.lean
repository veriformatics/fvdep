import FvdepAudit.Index.Statuses.Spec

/-! The status helpers against the relations written apart: the facts' lookups, the axiom order +
`Extra`, a mapped theorem's outcome (`Judged`: sound, unique, a missing axiom list excluded). -/

namespace FvdepAudit.Index.Statuses.Proof

open Lean FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepAudit.Index.Statuses.Spec

/-! ## Lookups -/

theorem find_none (F : Facts) (t : Name) :
    F.decls.find? (·.name == t) = none ↔ ∀ d ∈ F.decls, d.name ≠ t := by simp [List.find?_eq_none]

theorem find_some (F : Facts) (t : Name) (d : Decl) :
    F.decls.find? (·.name == t) = some d ↔ DeclOf F t d := by
  rw [List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨hn, pre, post, e, hpre⟩
    exact ⟨pre, post, e, by simpa using hn, fun x hx => by simpa using hpre x hx⟩
  · rintro ⟨pre, post, e, hn, hpre⟩
    exact ⟨by simpa using hn, pre, post, e, fun x hx => by simpa using hpre x hx⟩

theorem declOf_unique {F : Facts} {t : Name} {d d' : Decl} (h : DeclOf F t d) (h' : DeclOf F t d') :
    d = d' := by
  rw [← find_some] at h h'
  rw [h] at h'
  exact Option.some.inj h'

theorem declOf_mem {F : Facts} {t : Name} {d : Decl} (h : DeclOf F t d) :
    d ∈ F.decls ∧ d.name = t := by
  obtain ⟨pre, post, e, hn, _⟩ := h
  exact ⟨by simp [e], hn⟩

theorem find_axioms (ax : List (Name × List Name)) (t : Name) (raw : List Name) :
    (ax.find? (·.1 == t)).map (·.2) = some raw ↔ AxiomsOf ax t raw := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    obtain ⟨hn, pre, post, e, hpre⟩ := List.find?_eq_some_iff_append.mp hx
    have ha : a = t := by simpa using hn
    subst ha
    exact ⟨pre, post, e, fun y hy => by simpa using hpre y hy⟩
  · rintro ⟨pre, post, e, hpre⟩
    exact
      ⟨(t, raw),
        List.find?_eq_some_iff_append.mpr
          ⟨by simp, pre, post, e, fun y hy => by simpa using hpre y hy⟩,
        rfl⟩

theorem axiomsOf_unique {ax : List (Name × List Name)} {t : Name} {raw raw' : List Name}
    (h : AxiomsOf ax t raw) (h' : AxiomsOf ax t raw') : raw = raw' := by
  rw [← find_axioms] at h h'
  rw [h] at h'
  exact Option.some.inj h'

/-! ## The axiom order -/

theorem str_lt_irrefl (a : String) : ¬a < a := by
  rw [String.lt_iff]
  exact List.lt_irrefl _

theorem str_lt_trans {a b c : String} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [String.lt_iff] at *
  exact List.lt_trans h₁ h₂

theorem str_lt_asymm {a b : String} (h : a < b) : ¬b < a := by
  rw [String.lt_iff] at *
  exact List.lt_asymm h

theorem str_eq_of_not_lt {a b : String} (h₁ : ¬a < b) (h₂ : ¬b < a) : a = b := by grind

theorem mem_insertAsc (x s : String) : ∀ ys : List String, s ∈ insertAsc x ys ↔ s = x ∨ s ∈ ys
  | [] => by simp [insertAsc]
  | y :: ys => by
    unfold insertAsc
    by_cases h₁ : x < y
    · simp [h₁]
    · by_cases h₂ : x = y
      · subst h₂
        simp [h₁]
      · simp [h₁, h₂, mem_insertAsc x s ys, or_left_comm]

theorem insertAsc_sorted (x : String) :
    ∀ ys : List String, ys.Pairwise (· < ·) → (insertAsc x ys).Pairwise (· < ·)
  | [] => fun _ => by simp [insertAsc]
  | y :: ys => fun h => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp h
    unfold insertAsc
    by_cases h₁ : x < y
    · simp only [h₁, decide_true]
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, h⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h₁
      · exact str_lt_trans h₁ (hy z hz)
    · by_cases h₂ : x = y
      · subst h₂
        simpa [h₁] using h
      · have hyx : y < x := Classical.byContradiction fun h₃ => h₂ (str_eq_of_not_lt h₁ h₃)
        simp only [h₁, h₂, decide_false]
        refine List.pairwise_cons.mpr ⟨fun z hz => ?_, insertAsc_sorted x ys hys⟩
        rcases (mem_insertAsc x z ys).mp hz with rfl | hz
        · exact hyx
        · exact hy z hz

theorem ascending_spec (xs : List String) :
    (ascending xs).Pairwise (· < ·) ∧ ∀ s, s ∈ ascending xs ↔ s ∈ xs := by
  induction xs with
  | nil => simp [ascending]
  | cons x xs ih =>
    have e : ascending (x :: xs) = insertAsc x (ascending xs) := rfl
    rw [e]
    exact ⟨insertAsc_sorted x _ ih.1, fun s => by rw [mem_insertAsc, ih.2, List.mem_cons]⟩

theorem sorted_unique :
    ∀ {a b : List String}, a.Pairwise (· < ·) → b.Pairwise (· < ·) → (∀ s, s ∈ a ↔ s ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).mpr (by simp)) (by simp)
  | x :: _, [], _, _, h => absurd ((h x).mp (by simp)) (by simp)
  | x :: xs, y :: ys, ha, hb, h => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp ha
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hb
    have hxy : x = y := by
      rcases List.mem_cons.mp ((h x).mp (by simp)) with e | hxm
      · exact e
      · rcases List.mem_cons.mp ((h y).mpr (by simp)) with e | hym
        · exact e.symm
        · exact absurd (hy x hxm) (str_lt_asymm (hx y hym))
    subst hxy
    rw [sorted_unique hxs hys fun s => ⟨fun hs => ?_, fun hs => ?_⟩]
    · rcases List.mem_cons.mp ((h s).mp (List.mem_cons_of_mem _ hs)) with e | h'
      · subst e
        exact absurd (hx _ hs) (str_lt_irrefl _)
      · exact h'
    · rcases List.mem_cons.mp ((h s).mpr (List.mem_cons_of_mem _ hs)) with e | h'
      · subst e
        exact absurd (hy _ hs) (str_lt_irrefl _)
      · exact h'

theorem extra_ascending (raw : List Name) :
    Extra raw (ascending ((raw.filter (· ∉ std)).map (·.toString))) := by
  obtain ⟨hs, hm⟩ := ascending_spec ((raw.filter (· ∉ std)).map (·.toString))
  refine ⟨hs, fun s => ?_⟩
  rw [hm]
  simp [std, and_assoc]

theorem extra_unique {raw : List Name} {a a' : List String} (h : Extra raw a) (h' : Extra raw a') :
    a = a' := sorted_unique h.1 h'.1 fun s => (h.2 s).trans (h'.2 s).symm

theorem extraAxioms_iff (ax : List (Name × List Name)) (t : Name) (a : List String) :
    extraAxioms ax t = some a ↔ ∃ raw, AxiomsOf ax t raw ∧ Extra raw a := by
  unfold extraAxioms
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x.2, (find_axioms ax t x.2).mp (by simp [hx]), extra_ascending x.2⟩
  · rintro ⟨raw, hr, he⟩
    obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp ((find_axioms ax t raw).mpr hr)
    rw [hx]
    subst e
    exact congrArg some (extra_unique (extra_ascending x.2) he)

theorem extraAxioms_none (ax : List (Name × List Name)) (t : Name) :
    extraAxioms ax t = none ↔ ∀ x ∈ ax, x.1 ≠ t := by simp [extraAxioms, List.find?_eq_none]

theorem axiomsOf_mem {ax : List (Name × List Name)} {t : Name} {raw : List Name}
    (h : AxiomsOf ax t raw) : (t, raw) ∈ ax := by
  obtain ⟨pre, post, e, _⟩ := h
  simp [e]

theorem axiomStatus_iff (a : List String) (s : Status) : axiomStatus a = s ↔ StatusOf a s := by
  unfold axiomStatus StatusOf
  by_cases h₁ : "sorryAx" ∈ a <;> cases a <;> cases s <;> simp_all

/-! ## A mapped theorem's outcome -/

theorem outcome_sound (F : Facts) (ax : List (Name × List Name)) (t : Name) (ok : Expr → Bool)
    (Ok : Expr → Prop) (hok : ∀ ty, ok ty = true ↔ Ok ty) (r : Status × List String × Option Why)
    (h : outcome F ax t ok = .ok r) : Judged F ax t Ok r := by
  unfold outcome judge at h
  cases hd : F.decls.find? (·.name == t) with
  | none =>
    simp only [hd, opened, Except.ok.injEq] at h
    subst h
    exact .absent ((find_none F t).mp hd)
  | some d =>
    have hD := (find_some F t d).mp hd
    simp only [hd] at h
    cases hk : d.kind == .thm <;> cases hm : d.module.getRoot == `FvdepProofs <;>
      cases ho : ok d.type <;>
      simp only [hk, hm, ho, opened, Except.ok.injEq] at h
    · subst h
      exact .notTheorem hD (by simpa using hk)
    · subst h
      exact .notTheorem hD (by simpa using hk)
    · subst h
      exact .notTheorem hD (by simpa using hk)
    · subst h
      exact .notTheorem hD (by simpa using hk)
    · subst h
      exact .outside hD (by simpa using hk) (by simpa using hm)
    · subst h
      exact .outside hD (by simpa using hk) (by simpa using hm)
    · subst h
      exact
        .other hD (by simpa using hk) (by simpa using hm) fun hp => by simp [(hok _).mpr hp] at ho
    · cases hx : extraAxioms ax t with
      | none => simp [hx] at h
      | some a =>
        simp only [hx, Except.ok.injEq] at h
        subst h
        obtain ⟨raw, hr, he⟩ := (extraAxioms_iff ax t a).mp hx
        exact
          .counted hD (by simpa using hk) (by simpa using hm) ((hok _).mp ho) hr he
            ((axiomStatus_iff a _).mp rfl)

theorem judged_unique {F : Facts} {ax : List (Name × List Name)} {t : Name} {Ok : Expr → Prop}
    {r r' : Status × List String × Option Why} (h : Judged F ax t Ok r) (h' : Judged F ax t Ok r') :
    r = r' := by
  cases h with
  | absent ha =>
    cases h' with
    | absent _ => rfl
    | notTheorem hd _
    | outside hd _ _
    | other hd _ _ _
    | counted hd _ _ _ _ _ _ => exact absurd (declOf_mem hd).2 (ha _ (declOf_mem hd).1)
  | notTheorem hd hk =>
    cases h' with
    | absent ha => exact absurd (declOf_mem hd).2 (ha _ (declOf_mem hd).1)
    | notTheorem _ _ => rfl
    | outside hd' hk' _
    | other hd' hk' _ _
    | counted hd' hk' _ _ _ _ _ => exact absurd (declOf_unique hd hd' ▸ hk') hk
  | outside hd hk hm =>
    cases h' with
    | absent ha => exact absurd (declOf_mem hd).2 (ha _ (declOf_mem hd).1)
    | notTheorem hd' hk' => exact absurd (declOf_unique hd hd' ▸ hk) hk'
    | outside _ _ _ => rfl
    | other hd' _ hm' _
    | counted hd' _ hm' _ _ _ _ => exact absurd (declOf_unique hd hd' ▸ hm') hm
  | other hd hk hm ho =>
    cases h' with
    | absent ha => exact absurd (declOf_mem hd).2 (ha _ (declOf_mem hd).1)
    | notTheorem hd' hk' => exact absurd (declOf_unique hd hd' ▸ hk) hk'
    | outside hd' _ hm' => exact absurd (declOf_unique hd hd' ▸ hm) hm'
    | other _ _ _ _ => rfl
    | counted hd' _ _ ho' _ _ _ => exact absurd (declOf_unique hd hd' ▸ ho') ho
  | counted hd hk hm ho hr he hs =>
    cases h' with
    | absent ha => exact absurd (declOf_mem hd).2 (ha _ (declOf_mem hd).1)
    | notTheorem hd' hk' => exact absurd (declOf_unique hd hd' ▸ hk) hk'
    | outside hd' _ hm' => exact absurd (declOf_unique hd hd' ▸ hm) hm'
    | other hd' _ _ ho' => exact absurd (declOf_unique hd hd' ▸ ho) ho'
    | counted _ _ _ _ hr' he' hs' =>
      have e₁ := axiomsOf_unique hr hr'
      subst e₁
      have e₂ := extra_unique he he'
      subst e₂
      rw [← (axiomStatus_iff _ _).mpr hs, ← (axiomStatus_iff _ _).mpr hs']

theorem outcome_error (F : Facts) (ax : List (Name × List Name)) (t : Name) (ok : Expr → Bool)
    (Ok : Expr → Prop) (hok : ∀ ty, ok ty = true ↔ Ok ty) (t' : Name)
    (h : outcome F ax t ok = .error t') (r : Status × List String × Option Why) :
    ¬Judged F ax t Ok r := by
  intro hj
  unfold outcome judge at h
  cases hd : F.decls.find? (·.name == t) with
  | none => simp [hd, opened] at h
  | some d =>
    have hD := (find_some F t d).mp hd
    simp only [hd] at h
    cases hk : d.kind == .thm <;> cases hm : d.module.getRoot == `FvdepProofs <;>
      cases ho : ok d.type <;>
      simp only [hk, hm, ho, opened, reduceCtorEq] at h
    cases hx : extraAxioms ax t with
    | some a => simp [hx] at h
    | none =>
      cases hj with
      | absent ha => exact absurd (declOf_mem hD).2 (ha _ (declOf_mem hD).1)
      | notTheorem hd' hk' => exact absurd (declOf_unique hD hd' ▸ (by simpa using hk)) hk'
      | outside hd' _ hm' => exact absurd (declOf_unique hD hd' ▸ (by simpa using hm)) hm'
      | other hd' _ _ ho' => exact absurd (declOf_unique hD hd' ▸ (hok _).mp ho) ho'
      | counted _ _ _ _ hr _ _ =>
        exact absurd (axiomsOf_mem hr) fun hmem => (extraAxioms_none ax t).mp hx _ hmem rfl

theorem outcome_iff (F : Facts) (ax : List (Name × List Name)) (t : Name) (ok : Expr → Bool)
    (Ok : Expr → Prop) (hok : ∀ ty, ok ty = true ↔ Ok ty) (r : Status × List String × Option Why) :
    outcome F ax t ok = .ok r ↔ Judged F ax t Ok r := by
  refine ⟨outcome_sound F ax t ok Ok hok r, fun hj => ?_⟩
  cases ho : outcome F ax t ok with
  | error t' => exact absurd hj (outcome_error F ax t ok Ok hok t' ho r)
  | ok r' => rw [judged_unique (outcome_sound F ax t ok Ok hok r' ho) hj]

end FvdepAudit.Index.Statuses.Proof
