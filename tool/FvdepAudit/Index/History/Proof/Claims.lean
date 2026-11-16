import FvdepAudit.Index.History.Spec

/-! `history` against the checks written apart (`HistorySpec`): each Bool test equals its
proposition (first match, membership, list prefix, divergence), then each layer — the witness, one
operation's line, one baseline's lines, the whole list. Header = the ledger statement. -/

namespace FvdepAudit.Index.History.Proof

open Classical FvdepCore.Ids FvdepCore.Index FvdepCore.Index.History FvdepAudit.Index.History.Spec

/-! ## Bool tests = their propositions -/

theorem find_first {α : Type} (xs : List α) (p : α → Bool) (P : α → Prop)
    (hp : ∀ x, p x = true ↔ P x) (x : α) : xs.find? p = some x ↔ FirstIn xs P x := by
  rw [List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨h, pre, post, e, hpre⟩
    refine ⟨pre, post, e, (hp x).mp h, fun y hy hP => ?_⟩
    have := hpre y hy
    rw [(hp y).mpr hP] at this
    simp at this
  · rintro ⟨pre, post, e, h, hpre⟩
    refine ⟨(hp x).mpr h, pre, post, e, fun y hy => ?_⟩
    cases hpy : p y
    · rfl
    · exact absurd ((hp y).mp hpy) (hpre y hy)

theorem firstIn_unique {α : Type} {xs : List α} {P : α → Prop} {x y : α} (hx : FirstIn xs P x)
    (hy : FirstIn xs P y) : x = y := by
  have e₁ := (find_first xs (fun z => decide (P z)) P (by simp) x).mpr hx
  have e₂ := (find_first xs (fun z => decide (P z)) P (by simp) y).mpr hy
  rw [e₁] at e₂
  exact Option.some.inj e₂

theorem find_none_iff {α : Type} (xs : List α) (p : α → Bool) (P : α → Prop)
    (hp : ∀ x, p x = true ↔ P x) : xs.find? p = none ↔ ¬∃ x, FirstIn xs P x := by
  constructor
  · rintro h ⟨x, hx⟩
    rw [(find_first xs p P hp x).mpr hx] at h
    cases h
  · intro h
    cases hf : xs.find? p with
    | none => rfl
    | some x => exact absurd ⟨x, (find_first xs p P hp x).mp hf⟩ h

theorem decoded_eq (b : Baseline) :
    b.decoded =
      match b.index with
      | some (.ok i) => some i
      | _ => none := by
  unfold Baseline.decoded
  rcases b with ⟨_, _ | _ | _⟩ <;> rfl

theorem listsOp_iff (b : Baseline) (id : ModuleId) (v : EntryVersion) :
    ((b.decoded.map fun i => listsOp i id v) == some true) = true ↔ ListsOp b id v := by
  unfold ListsOp listsOp
  rw [decoded_eq]
  rcases b with ⟨c, _ | ⟨_ | i⟩⟩ <;> simp

theorem listsOp_false (b : Baseline) (id : ModuleId) (v : EntryVersion) (h : ¬ListsOp b id v) :
    ((b.decoded.map fun i => listsOp i id v) == some true) = false :=
  Bool.eq_false_iff.mpr fun h' => h ((listsOp_iff b id v).mp h')

theorem holds_iff (b : Baseline) (id : ModuleId) (v : EntryVersion) :
    ((b.decoded.map fun i => holdsRemoved i id v) == some true) = true ↔ HoldsRemoved b id v := by
  unfold HoldsRemoved holdsRemoved
  rw [decoded_eq]
  rcases b with ⟨c, _ | ⟨_ | i⟩⟩ <;> simp

theorem diverge_iff {α : Type} [DecidableEq α] (xs : List (List α)) :
    diverge xs = true ↔ Diverge xs := by
  unfold diverge Diverge
  simp [Bool.eq_false_iff, List.isPrefixOf_iff_prefix]

theorem holding_eq (parents : List Baseline) (id : ModuleId) (v : EntryVersion) :
    (parents.filter fun p => (p.decoded.map fun i => listsOp i id v) == some true) =
      parents.filter fun p => decide (ListsOp p id v) := by
  apply List.filter_congr
  intro p _
  exact Bool.eq_iff_iff.mpr (by rw [listsOp_iff, decide_eq_true_iff])

/-! ## Each layer -/

theorem witness_eq (head : Baseline) (parents : List Baseline) (b : Baseline) (ib : IndexFile)
    (o : Operation) (r : Removed) :
    witnessLine head parents b ib o r = WitnessSpec head parents b ib o r := by
  unfold witnessLine WitnessSpec
  rw [holding_eq]
  by_cases h₁ : ListsOp head o.id o.version
  · simp only [(listsOp_iff head o.id o.version).mpr h₁, h₁, ↓reduceIte]
  · simp only [listsOp_false head o.id o.version h₁, h₁, Bool.false_eq_true, ↓reduceIte]
    by_cases h₂ : ∃ p ∈ parents, HoldsRemoved p o.id o.version
    · have h₂' :
        (parents.any fun p => (p.decoded.map fun i => holdsRemoved i o.id o.version) == some true) =
          true := by
        rw [List.any_eq_true]
        obtain ⟨p, hp, hh⟩ := h₂
        exact ⟨p, hp, (holds_iff p o.id o.version).mpr hh⟩
      simp only [h₂, h₂', ↓reduceIte]
    · have h₂' :
        (parents.any fun p => (p.decoded.map fun i => holdsRemoved i o.id o.version) == some true) =
          false := by
        rw [← Bool.not_eq_true, List.any_eq_true]
        rintro ⟨p, hp, hh⟩
        exact h₂ ⟨p, hp, (holds_iff p o.id o.version).mp hh⟩
      simp only [h₂, h₂', Bool.false_eq_true, ↓reduceIte]
      have hfirst :=
        find_first (parents.filter fun p => decide (ListsOp p o.id o.version))
          (fun p => p.commit == toString r.lastCommit) (fun p => p.commit = toString r.lastCommit)
          (by simp)
      cases hf :
        (parents.filter fun p => decide (ListsOp p o.id o.version)).find?
          (fun p => p.commit == toString r.lastCommit) with
      | some p =>
        have hp := (hfirst p).mp hf
        have hex :
          ∃ q,
            FirstIn (parents.filter fun p => decide (ListsOp p o.id o.version))
              (fun p => p.commit = toString r.lastCommit) q :=
          ⟨p, hp⟩
        by_cases hb : p.commit = b.commit
        · have hq :
            ∃ q,
              FirstIn (parents.filter fun p => decide (ListsOp p o.id o.version))
                  (fun p => p.commit = toString r.lastCommit) q ∧
                q.commit = b.commit :=
            ⟨p, hp, hb⟩
          simp only [hex, hq, hb, ↓reduceIte]
        · have hq :
            ¬∃ q,
                FirstIn (parents.filter fun p => decide (ListsOp p o.id o.version))
                    (fun p => p.commit = toString r.lastCommit) q ∧
                  q.commit = b.commit := by
            rintro ⟨q, hq, hqb⟩
            exact hb (firstIn_unique hp hq ▸ hqb)
          simp only [hex, hq, hb, ↓reduceIte]
      | none =>
        have hn :=
          (find_none_iff (parents.filter fun p => decide (ListsOp p o.id o.version))
                (fun p => p.commit == toString r.lastCommit)
                (fun p => p.commit = toString r.lastCommit) (by simp)).mp
            hf
        simp only [hn, ↓reduceIte]
        cases hh : (parents.filter fun p => decide (ListsOp p o.id o.version)).head? with
        | none => simp
        | some p =>
          by_cases hb : p.commit = b.commit
          · simp [hb]
          · simp [hb]

theorem opLine_eq (w : IndexFile) (head : Baseline) (parents : List Baseline) (b : Baseline)
    (ib : IndexFile) (o : Operation) :
    opLine w head parents b ib o = OpLineSpec w head parents b ib o := by
  unfold opLine OpLineSpec
  have hops :=
    find_first w.operations (fun x => x.id == o.id && x.version == o.version)
      (fun x => x.id = o.id ∧ x.version = o.version) (by simp)
  have hrem :=
    find_first w.removed (fun x => x.id == o.id && x.version == o.version)
      (fun x => x.id = o.id ∧ x.version = o.version) (by simp)
  cases hx : w.operations.find? (fun x => x.id == o.id && x.version == o.version) with
  | some x =>
    have hxf := (hops x).mp hx
    have hex : ∃ y, FirstIn w.operations (fun x => x.id = o.id ∧ x.version = o.version) y :=
      ⟨x, hxf⟩
    by_cases hd : x.digest = o.digest
    · have hy :
        ∃ y,
          FirstIn w.operations (fun x => x.id = o.id ∧ x.version = o.version) y ∧
            y.digest = o.digest :=
        ⟨x, hxf, hd⟩
      simp only [hex, hy, hd, ↓reduceIte]
    · have hy :
        ¬∃ y,
            FirstIn w.operations (fun x => x.id = o.id ∧ x.version = o.version) y ∧
              y.digest = o.digest := by
        rintro ⟨y, hy, hyd⟩
        exact hd (firstIn_unique hxf hy ▸ hyd)
      simp only [hex, hy, hd, ↓reduceIte]
  | none =>
    have hn :=
      (find_none_iff w.operations (fun x => x.id == o.id && x.version == o.version)
            (fun x => x.id = o.id ∧ x.version = o.version) (by simp)).mp
        hx
    simp only [hn, ↓reduceIte]
    cases hr : w.removed.find? (fun x => x.id == o.id && x.version == o.version) with
    | some r =>
      have hrf := (hrem r).mp hr
      have hex : ∃ y, FirstIn w.removed (fun r => r.id = o.id ∧ r.version = o.version) y := ⟨r, hrf⟩
      by_cases hd : r.digest = o.digest
      · have hnd :
          ¬∃ y,
              FirstIn w.removed (fun r => r.id = o.id ∧ r.version = o.version) y ∧
                y.digest ≠ o.digest := by
          rintro ⟨y, hy, hyd⟩
          exact hyd (firstIn_unique hrf hy ▸ hd)
        simp only [hex, hnd, hd, ne_eq, not_true_eq_false, ↓reduceIte, ↓reduceDIte]
        by_cases ht : w.toolchain = ib.toolchain
        · simp only [ht, ↓reduceIte]
        · simp only [ht, ↓reduceIte]
          rw [firstIn_unique (Classical.choose_spec hex) hrf]
          exact witness_eq head parents b ib o r
      · have hy :
          ∃ y,
            FirstIn w.removed (fun r => r.id = o.id ∧ r.version = o.version) y ∧
              y.digest ≠ o.digest :=
          ⟨r, hrf, hd⟩
        simp only [hex, hy, hd, ne_eq, not_false_eq_true, ↓reduceIte]
    | none =>
      have hn' :=
        (find_none_iff w.removed (fun x => x.id == o.id && x.version == o.version)
              (fun x => x.id = o.id ∧ x.version = o.version) (by simp)).mp
          hr
      simp only [hn', ↓reduceIte]

theorem baseline_eq (w : IndexFile) (head : Baseline) (parents : List Baseline) (b : Baseline) :
    baselineLines w head parents b = BaselineSpec w head parents b := by
  unfold baselineLines BaselineSpec
  rcases b with ⟨c, _ | ⟨reason | ib⟩⟩
  · rfl
  · rfl
  · have hf :
      (opLine w head parents ⟨c, some (.ok ib)⟩ ib) =
        OpLineSpec w head parents ⟨c, some (.ok ib)⟩ ib :=
      funext fun o => opLine_eq _ _ _ _ _ o
    simp only [hf, List.isPrefixOf_iff_prefix]

theorem ite_diverge {α β : Type} [DecidableEq α] (xs : List (List α)) (a b : β) :
    (if diverge xs = true then a else b) = if Diverge xs then a else b := by
  by_cases h : Diverge xs
  · simp only [(diverge_iff xs).mpr h, h, ↓reduceIte]
  · simp only [Bool.eq_false_iff.mpr fun h' => h ((diverge_iff xs).mp h'), h, Bool.false_eq_true,
      ↓reduceIte]

/-- U4 C7 + C9 + C8 `HistoryExact`: `history` = the violations written apart, in C9's order. -/
theorem history_exact (work : Except String (Option IndexFile)) (head : Baseline)
    (parents : List Baseline) : history work head parents = HistorySpec work head parents := by
  unfold history HistorySpec
  cases work with
  | error reason => rfl
  | ok
    wo =>
    have hdec :
      (Baseline.decoded) = fun p =>
        match p.index with
        | some (.ok i) => some i
        | _ => none :=
      funext decoded_eq
    have hbase :
      baselineLines (wo.getD emptyIndex) head parents =
        BaselineSpec (wo.getD emptyIndex) head parents :=
      funext (baseline_eq _ head parents)
    simp only [hdec, hbase, ite_diverge]
    congr

end FvdepAudit.Index.History.Proof
