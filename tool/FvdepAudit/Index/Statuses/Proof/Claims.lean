import FvdepAudit.Index.Rules.Proof.Claims
import FvdepAudit.Index.Statuses.Proof.Basic
import FvdepAudit.Registry.Proof.Claims

/-! The statuses against the spec written apart: the proof registry (`RegistryOf`), an obligation's
+ the compat edge's outcome, an entry (`EntrySpec`), every entry of a validated registry
(`StatusesSpec`); the digest's framed input (C4). Headers of the claims = the ledger statements. -/

namespace FvdepAudit.Index.Statuses.Proof

open Lean FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepAudit.Index.Statuses.Spec FvdepAudit.Registry.Spec FvdepAudit.Registry.Proof
open FvdepAudit.Index.Rules.Spec FvdepAudit.Index.Rules.Proof

/-! ## The proof registry -/

theorem proofRegistry_spec (F : Facts) (e : Entry) : RegistryOf F e (proofRegistry F e) := by
  simp only [proofRegistry]
  cases hd : F.decls.find? (·.name == proofsName e.module) with
  | none => exact .absent ((find_none F _).mp hd)
  | some
    d =>
    have hm : ∃ d ∈ F.decls, d.name = proofsName e.module :=
      ⟨d, (declOf_mem ((find_some F _ d).mp hd)).1, (declOf_mem ((find_some F _ d).mp hd)).2⟩
    cases hp : readProofs F (proofsName e.module) with
    | ok p => exact .read hm ((registry_proofs F _ p).mp hp)
    | error _ => exact .unreadable hm fun p hp' => by simp [(registry_proofs F _ p).mpr hp'] at hp

theorem registryOf_unique {F : Facts} {e : Entry} {pr pr' : Except Why Proofs}
    (h : RegistryOf F e pr) (h' : RegistryOf F e pr') : pr = pr' := by
  cases h with
  | absent ha =>
    cases h' with
    | absent _ => rfl
    | unreadable hm _
    | read hm _ =>
      obtain ⟨d, hd, hn⟩ := hm
      exact absurd hn (ha d hd)
  | unreadable hm hn =>
    cases h' with
    | absent ha =>
      obtain ⟨d, hd, hn'⟩ := hm
      exact absurd hn' (ha d hd)
    | unreadable _ _ => rfl
    | read _ hp => exact absurd hp (hn _)
  | read hm hp =>
    cases h' with
    | absent ha =>
      obtain ⟨d, hd, hn'⟩ := hm
      exact absurd hn' (ha d hd)
    | unreadable _ hn => exact absurd hp (hn _)
    | read _ hp' =>
      rw [← registry_proofs] at hp hp'
      rw [hp] at hp'
      cases hp'
      rfl

/-! ## An obligation, the compat edge -/

theorem erase_const (o : Name) : erase (.const o []) = .const o [] := by simp [erase]

theorem obligation_ok (o : Name) (ty : Expr) :
    alphaEq ty (.const o []) = true ↔ ObligationOk o ty := by
  rw [alphaEq_iff, erase_const]
  rfl

theorem obligationOutcome_iff (F : Facts) (ax : List (Name × List Name)) (pr : Except Why Proofs)
    (o : Name) (r : Status × List String × Option Why) :
    obligationOutcome F ax pr o = .ok r ↔ ObligationJudged F ax o pr r := by
  cases pr with
  | error w =>
    simp only [obligationOutcome, opened, Except.ok.injEq]
    constructor
    · rintro rfl
      exact .registry
    · intro h
      cases h
      rfl
  | ok p =>
    simp only [obligationOutcome]
    have hcount := List.countP_eq_length_filter (p := (·.1 == o)) (l := p.obligations)
    cases hf : p.obligations.filter (·.1 == o) with
    | nil =>
      have hu : ∀ x ∈ p.obligations, x.1 ≠ o := by
        intro x hx e
        have : x ∈ p.obligations.filter (·.1 == o) := List.mem_filter.mpr ⟨hx, by simp [e]⟩
        simp [hf] at this
      rw [hf] at hcount
      simp only [opened, Except.ok.injEq]
      constructor
      · rintro rfl
        exact .unmapped hu
      · intro h
        cases h with
        | unmapped _ => rfl
        | twice h2 => simp [hcount] at h2
        | one h1 _ _ => simp [hcount] at h1
    | cons x
      xs =>
      have hx : x ∈ p.obligations ∧ x.1 = o := by
        have : x ∈ p.obligations.filter (·.1 == o) := by simp [hf]
        simpa using List.mem_filter.mp this
      cases xs with
      | nil =>
        rw [hf] at hcount
        simp only
        rw [outcome_iff F ax x.2 _ (ObligationOk o) (obligation_ok o) r]
        constructor
        · intro hj
          refine .one (by simp [hcount]) ?_ hj
          have e : x = (o, x.2) := by
            obtain ⟨a, b⟩ := x
            simp only at hx
            simp [hx.2]
          rw [← e]
          exact hx.1
        · intro h
          cases h with
          | unmapped hu => exact absurd hx.2 (hu x hx.1)
          | twice h2 => simp [hcount] at h2
          | @one _ t _ _ hmem
            hj =>
            have : (o, t) ∈ p.obligations.filter (·.1 == o) := List.mem_filter.mpr ⟨hmem, by simp⟩
            rw [hf] at this
            simp only [List.mem_singleton] at this
            rw [← this]
            exact hj
      | cons y ys =>
        rw [hf] at hcount
        simp only [opened, Except.ok.injEq]
        constructor
        · rintro rfl
          exact .twice (by simp [hcount])
        · intro h
          cases h with
          | unmapped hu => exact absurd hx.2 (hu x hx.1)
          | twice _ => rfl
          | one h1 _ _ => simp [hcount] at h1

theorem compat_ok (T : Expr) (new old : Name) (ty : Expr) :
    compatStatement T new old ty = true ↔ CompatOk T new old ty := by
  unfold compatStatement CompatOk
  constructor
  · intro h
    cases hl : eqLevel? (erase ty) with
    | none => simp [hl] at h
    | some u =>
      simp only [hl, alphaEq_iff] at h
      exact ⟨u, h⟩
  · rintro ⟨u, hu⟩
    have hl : eqLevel? (erase ty) = some u := by
      rw [hu]
      rfl
    simp only [hl, alphaEq_iff]
    exact hu

theorem compatOutcome_iff (F : Facts) (ax : List (Name × List Name)) (T : Expr) (new old : Name)
    (pr : Except Why Proofs) (r : Status × List String × Option Why) :
    compatOutcome F ax T new old pr = .ok r ↔ CompatJudged F ax T new old pr r := by
  cases pr with
  | error w =>
    simp only [compatOutcome, opened, Except.ok.injEq]
    constructor
    · rintro rfl
      exact .registry
    · intro h
      cases h
      rfl
  | ok p =>
    simp only [compatOutcome]
    cases hc : p.compat with
    | none =>
      simp only [opened, Except.ok.injEq]
      constructor
      · rintro rfl
        exact .unmapped hc
      · intro h
        cases h with
        | unmapped _ => rfl
        | one hc' _ => simp [hc] at hc'
    | some t =>
      simp only
      rw [outcome_iff F ax t _ (CompatOk T new old) (compat_ok T new old) r]
      constructor
      · intro hj
        exact .one hc hj
      · intro h
        cases h with
        | unmapped hc' => simp [hc] at hc'
        | one hc' hj =>
          rw [hc] at hc'
          cases hc'
          exact hj

theorem outcomes_iff (F : Facts) (ax : List (Name × List Name)) (pr : Except Why Proofs) :
    ∀ (os : List Name) (rs : List (Status × List String × Option Why)),
      outcomes F ax pr os = .ok rs ↔
        os.length = rs.length ∧ ∀ x ∈ os.zip rs, ObligationJudged F ax x.1 pr x.2
  | [], rs => by cases rs <;> simp [outcomes]
  | o :: os, rs => by
    simp only [outcomes]
    cases ho : obligationOutcome F ax pr o with
    | error t =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨hl, hall⟩
      cases rs with
      | nil => simp at hl
      | cons r rs =>
        have := (obligationOutcome_iff F ax pr o r).mpr (hall (o, r) (by simp))
        rw [ho] at this
        cases this
    | ok r =>
      cases hs : outcomes F ax pr os with
      | error t =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨hl, hall⟩
        cases rs with
        | nil => simp at hl
        | cons r'
          rs' =>
          have :=
            (outcomes_iff F ax pr os rs').mpr
              ⟨by simpa using hl, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩
          rw [hs] at this
          cases this
      | ok rs' =>
        simp only [Except.ok.injEq]
        have ih := (outcomes_iff F ax pr os rs').mp hs
        constructor
        · rintro rfl
          refine ⟨by simp [ih.1], fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact (obligationOutcome_iff F ax pr o r).mp ho
          · exact ih.2 x hx
        · rintro ⟨hl, hall⟩
          cases rs with
          | nil => simp at hl
          | cons r₂
            rs₂ =>
            have h₁ := (obligationOutcome_iff F ax pr o r₂).mpr (hall (o, r₂) (by simp))
            rw [ho] at h₁
            cases h₁
            have h₂ :=
              (outcomes_iff F ax pr os rs₂).mpr
                ⟨by simpa using hl, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩
            rw [hs] at h₂
            cases h₂
            rfl

/-! ## The compat edge, the ignored compat theorem, an entry -/

/-- What `validate` guarantees a declared compat edge: the entry's spec declaration + the listed
entry of the compat version. -/
def CompatResolved (F : Facts) (l : Lists) (e : Entry) : Prop :=
  ∀ c, e.compat = some c → (∃ d, libDecl? F e.spec = some d) ∧ ∃ old, listedAt? l e.id c = some old

theorem compatEdge_iff (F : Facts) (ax : List (Name × List Name)) (l : Lists) (e : Entry)
    (pr : Except Why Proofs) (hc : CompatResolved F l e)
    (edge : Option (String × Status × List String × Option Why)) :
    compatEdge F ax l e pr = .ok edge ↔
      (e.compat = none ∧ edge = none ∨
        ∃ c d old r,
          e.compat = some c ∧
            libDecl? F e.spec = some d ∧
            listedAt? l e.id c = some old ∧
            CompatJudged F ax d.type e.spec old.spec pr r ∧ edge = some (c, r)) := by
  unfold compatEdge
  cases hce : e.compat with
  | none =>
    simp only [Except.ok.injEq, true_and, reduceCtorEq, false_and, exists_false, or_false]
    exact eq_comm
  | some c =>
    obtain ⟨⟨d, hd⟩, old, hold⟩ := hc c hce
    simp only [hd, hold, Option.map, Option.getD, reduceCtorEq, false_and, false_or]
    constructor
    · intro h
      cases ho : compatOutcome F ax d.type e.spec old.spec pr with
      | error t => simp [ho, Except.map] at h
      | ok r =>
        simp only [ho, Except.map, Except.ok.injEq] at h
        exact ⟨c, d, old, r, rfl, rfl, hold, (compatOutcome_iff F ax _ _ _ pr r).mp ho, h.symm⟩
    · rintro ⟨c', d', old', r, hc', hd', hold', hj, rfl⟩
      have e₁ := Option.some.inj hc'
      subst e₁
      have e₂ := Option.some.inj hd'
      have e₃ := Option.some.inj (hold.symm.trans hold')
      subst e₂ e₃
      simp [(compatOutcome_iff F ax _ _ _ pr r).mpr hj, Except.map]

theorem ignoredWarnings_iff (e : Entry) (pr : Except Why Proofs) (ignored : List Warning) :
    ignoredWarnings e pr = ignored ↔
      (e.compat = none ∧
          (∃ p t,
            pr = .ok p ∧ p.compat = some t ∧ ignored = [.ignored (subject e.id e.version) t]) ∨
        ¬(e.compat = none ∧ ∃ p t, pr = .ok p ∧ p.compat = some t) ∧ ignored = []) := by
  unfold ignoredWarnings
  cases hce : e.compat with
  | some c => simp [eq_comm]
  | none =>
    cases pr with
    | error w => simp [eq_comm]
    | ok p =>
      cases hp : p.compat with
      | none => simp [hp, eq_comm]
      | some t => simp [hp, eq_comm]

theorem entryStatus_iff (F : Facts) (ax : List (Name × List Name)) (l : Lists) (e : Entry)
    (hc : CompatResolved F l e) (s : EntryStatus) :
    entryStatus F ax l e = .ok s ↔ EntrySpec F ax l e s := by
  unfold entryStatus EntrySpec
  dsimp only
  constructor
  · intro h
    cases hos : outcomes F ax (proofRegistry F e) e.obligations with
    | error t => simp [hos] at h
    | ok rs =>
      cases hed : compatEdge F ax l e (proofRegistry F e) with
      | error t => simp [hos, hed] at h
      | ok edge =>
        simp only [hos, hed, Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hall⟩ := (outcomes_iff F ax _ e.obligations rs).mp hos
        exact
          ⟨proofRegistry F e, proofRegistry_spec F e, rs, hl, hall, rfl, edge,
            (compatEdge_iff F ax l e _ hc edge).mp hed, rfl, ignoredWarnings e (proofRegistry F e),
            (ignoredWarnings_iff e _ _).mp rfl, rfl⟩
  · rintro ⟨pr, hpr, rs, hl, hall, hobl, edge, hedge, hcompat, ignored, hign, hwarn⟩
    have e₁ := registryOf_unique hpr (proofRegistry_spec F e)
    subst e₁
    have hos := (outcomes_iff F ax _ e.obligations rs).mpr ⟨hl, hall⟩
    have hed := (compatEdge_iff F ax l e _ hc edge).mpr hedge
    have hi := (ignoredWarnings_iff e _ ignored).mpr hign
    simp only [hos, hed, Except.ok.injEq]
    obtain ⟨o, c, w⟩ := s
    dsimp only at hobl hcompat hwarn
    subst hobl hcompat hwarn
    simp only [warningsOf, hi]

/-! ## Every entry of a validated registry -/

theorem entryRows_hold {F : Facts} {l : Lists} (hv : RegistryValid F l) {e : Entry}
    (he : e ∈ l.entries) : ∃ i, ∀ r ∈ entryRows F l i e, r.1 := by
  have hm : e ∈ l.entries.zipIdx.map Prod.fst := by
    rw [List.zipIdx_map_fst]
    exact he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  exact
    ⟨p.2, fun r hr =>
      hv r
        (List.mem_append_left _
          (List.mem_append_left _
            (List.mem_append_left _
              (List.mem_append_left _
                (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hr⟩))))))⟩

theorem compatResolved_of_valid {F : Facts} {l : Lists} (hv : RegistryValid F l) {e : Entry}
    (he : e ∈ l.entries) : CompatResolved F l e := by
  obtain ⟨i, h⟩ := entryRows_hold hv he
  have hspec :=
    h _
      (List.mem_append_left _
        (List.mem_append_left _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
  have hearlier :=
    h _
      (List.mem_append_right _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
  obtain ⟨_, _, d, hd, _⟩ := hspec
  intro c hce
  obtain ⟨_, _, _, _, _, _, hl⟩ := hearlier c hce
  exact ⟨⟨d, hd⟩, Option.ne_none_iff_exists'.mp hl⟩

theorem statusesGo_iff (F : Facts) (ax : List (Name × List Name)) (l : Lists) :
    ∀ (es : List Entry) (_hc : ∀ e ∈ es, CompatResolved F l e) (rs : List (Entry × EntryStatus)),
      statuses.go F ax l es = .ok rs ↔
        es.length = rs.length ∧ ∀ x ∈ es.zip rs, x.2.1 = x.1 ∧ EntrySpec F ax l x.1 x.2.2
  | [], _, rs => by cases rs <;> simp [statuses.go]
  | e :: es, hc, rs => by
    have hce := hc e (List.mem_cons_self ..)
    have ih := statusesGo_iff F ax l es fun x hx => hc x (List.mem_cons_of_mem _ hx)
    simp only [statuses.go]
    cases hs : entryStatus F ax l e with
    | error t =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨hl, hall⟩
      cases rs with
      | nil => simp at hl
      | cons r rs =>
        obtain ⟨_, h₂⟩ := hall (e, r) (by simp)
        have := (entryStatus_iff F ax l e hce r.2).mpr h₂
        rw [hs] at this
        cases this
    | ok s =>
      cases hg : statuses.go F ax l es with
      | error f =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨hl, hall⟩
        cases rs with
        | nil => simp at hl
        | cons r
          rs =>
          have := (ih rs).mpr ⟨by simpa using hl, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩
          rw [hg] at this
          cases this
      | ok rest =>
        simp only [Except.ok.injEq]
        have hr := (ih rest).mp hg
        constructor
        · rintro rfl
          refine ⟨by simp [hr.1], fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨rfl, (entryStatus_iff F ax l e hce s).mp hs⟩
          · exact hr.2 x hx
        · rintro ⟨hl, hall⟩
          cases rs with
          | nil => simp at hl
          | cons r rs =>
            obtain ⟨h₁, h₂⟩ := hall (e, r) (by simp)
            have hs' := (entryStatus_iff F ax l e hce r.2).mpr h₂
            rw [hs] at hs'
            cases hs'
            have hg' :=
              (ih rs).mpr ⟨by simpa using hl, fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩
            rw [hg] at hg'
            cases hg'
            obtain ⟨a, b⟩ := r
            simp only at h₁
            subst h₁
            rfl

/-- U4 C5 + C9 + C8 `StatusExact`: after `validate` accepted the lists, `statuses` = the entries'
statuses + warnings written apart, in `modules` order. -/
theorem statuses_exact (F : Facts) (ax : List (Name × List Name)) (l : Lists)
    (hv : validate F l = none) (rs : List (Entry × EntryStatus)) :
    statuses F ax l = .ok rs ↔ StatusesSpec F ax l rs := by
  have hr := (validate_accepts F l).mp hv
  exact statusesGo_iff F ax l l.entries (fun e he => compatResolved_of_valid hr he) rs

end FvdepAudit.Index.Statuses.Proof
