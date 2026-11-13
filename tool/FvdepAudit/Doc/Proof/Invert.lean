import FvdepAudit.Doc.Proof.Walk

/-! Inverting the walk: what a value with no violations looks like (shape lemmas the documents'
`SchemaExact` proofs destructure with). -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepAudit.Doc.Spec

theorem string_lt_irrefl (s : String) : ¬s < s := fun h => String.lt_asymm h h

/-- Two strictly ascending lists with the same members are equal. -/
theorem sorted_eq :
    ∀ l₁ l₂ : List String,
      l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) List.not_mem_nil
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      apply Classical.byContradiction
      intro hne
      have ha : a ∈ l₂ := by
        rcases List.mem_cons.mp ((h a).mp List.mem_cons_self) with e | e
        · exact absurd e hne
        · exact e
      have hb : b ∈ l₁ := by
        rcases List.mem_cons.mp ((h b).mpr List.mem_cons_self) with e | e
        · exact absurd e.symm hne
        · exact e
      exact String.lt_asymm (h₁.1 b hb) (h₂.1 a ha)
    subst hab
    congr 1
    apply sorted_eq l₁ l₂ h₁.2 h₂.2
    intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
      · subst e
        exact absurd (h₁.1 _ hx) (string_lt_irrefl _)
      · exact e
    · intro hx
      rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
      · subst e
        exact absurd (h₂.1 _ hx) (string_lt_irrefl _)
      · exact e

theorem map_fst_cons {β : Type} {ms : List (String × β)} {k : String} {ks : List String}
    (h : ms.map (·.1) = k :: ks) : ∃ x rest, ms = (k, x) :: rest ∧ rest.map (·.1) = ks := by
  cases ms with
  | nil => simp at h
  | cons m rest =>
    obtain ⟨k', x⟩ := m
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, hr⟩ := h
    exact ⟨x, rest, rfl, hr⟩

theorem lookup_mem {β : Type} {ms : List (String × β)} {k : String} (h : ms.lookup k ≠ none) :
    k ∈ ms.map (·.1) := by
  induction ms with
  | nil => simp [List.lookup] at h
  | cons m ms ih =>
    obtain ⟨a, b⟩ := m
    by_cases hk : k = a
    · simp [hk]
    · have h' : (k == a) = false := by simpa [beq_iff_eq] using hk
      simp only [List.lookup, h'] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem disc_ok_none {tag tag' : String} {p : List PathSeg} {ms : List (String × Value)}
    {extra : List String} (h : discSpec tag p ms none = .ok (tag', extra)) :
    tag' = tag ∧ extra = [] := by
  simp only [discSpec, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem disc_ok_int {tag tag' : String} {p : List PathSeg} {ms : List (String × Value)} {k : String}
    {n : Int} {extra : List String} (h : discSpec tag p ms (some (.int k n)) = .ok (tag', extra)) :
    ms.lookup k = some (.int n) ∧ tag' = tag ∧ extra = [k] := by
  simp only [discSpec] at h
  cases hl : ms.lookup k with
  | none => simp [hl] at h
  | some x =>
    simp only [hl] at h
    by_cases hx : x = .int n
    · subst hx
      simp [kindOf] at h
      exact ⟨rfl, h.1.symm, h.2.symm⟩
    · cases x <;> simp_all [kindOf]

theorem disc_ok_str {tag tag' : String} {p : List PathSeg} {ms : List (String × Value)} {k : String}
    {xs : List String} {extra : List String}
    (h : discSpec tag p ms (some (.str k xs)) = .ok (tag', extra)) :
    ms.lookup k = some (.str tag') ∧ tag' ∈ xs ∧ extra = [k] := by
  simp only [discSpec] at h
  cases hl : ms.lookup k with
  | none => simp [hl] at h
  | some x =>
    simp only [hl] at h
    cases x <;> simp at h
    rename_i s
    by_cases hs : s ∈ xs
    · simp only [hs, ite_true, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hs, rfl⟩
    · simp [hs] at h

theorem leaf_nil {ks : List JKind} {r : Rule} {p : List PathSeg} {v : Value}
    (h : leafSpec ks r p v = []) : kindOf v ∈ ks ∧ ruleHolds r v := by
  unfold leafSpec at h
  by_cases hk : kindOf v ∈ ks
  · by_cases hr : ruleHolds r v
    · exact ⟨hk, hr⟩
    · simp [hk, hr] at h
  · simp [hk] at h

theorem viol_scalar {tag : String} {t : Ty} {ks : List JKind} {r : Rule} {p : List PathSeg}
    (ht : resolveSpec tag t = .scalar ks r) (v : Value) :
    violations tag t p v = leafSpec ks r p v := by cases v <;> simp [violations, ht]

theorem viol_obj {tag : String} {t : Ty} {d : Option Disc} {fs : List (String × Ty)}
    {p : List PathSeg} {v : Value} (ht : resolveSpec tag t = .obj d fs)
    (h : violations tag t p v = []) :
    ∃ ms,
      v = .obj ms ∧
        ∃ tag' extra,
          discSpec tag p ms d = .ok (tag', extra) ∧
            unknownSpec (extra ++ fs.map (·.1)) p ms = [] ∧
            missingSpec ms p (fs.map (·.1)) = [] ∧ memberViolations tag' fs p ms = [] := by
  cases v with
  | obj ms =>
    refine ⟨ms, rfl, ?_⟩
    simp only [violations, ht] at h
    cases hd : discSpec tag p ms d with
    | error e => simp [hd] at h
    | ok r =>
      obtain ⟨tag', extra⟩ := r
      simp only [hd, List.append_eq_nil_iff] at h
      exact ⟨tag', extra, rfl, h.1.1, h.1.2, h.2⟩
  | _ => simp [violations, ht] at h

theorem viol_arr {tag : String} {t : Ty} {ks : List JKind} {h₀ tl : Ty} {o : Order}
    {p : List PathSeg} {v : Value} (ht : resolveSpec tag t = .arr ks h₀ tl o)
    (h : violations tag t p v = []) :
    ∃ xs, v = .arr xs ∧ elemViolations tag h₀ tl p 0 xs = [] ∧ orderSpec p xs o = [] := by
  cases v with
  | arr xs =>
    simp only [violations, ht, List.append_eq_nil_iff] at h
    exact ⟨xs, rfl, h.1, h.2⟩
  | _ =>
    simp [violations, ht, kindMissSpec] at h; split at h <;> simp at h

/-- An object with no unknown + no missing member + strictly ascending keys holds exactly its
schema's keys, in their sorted order `K`. -/
theorem obj_keys {p : List PathSeg} {fs : List (String × Ty)} {ms : List (String × Value)}
    {extra : List String} (hd : ∀ k ∈ extra, ms.lookup k ≠ none)
    (hu : unknownSpec (extra ++ fs.map (·.1)) p ms = []) (hm : missingSpec ms p (fs.map (·.1)) = [])
    (K : List String) (hK : K.Pairwise (· < ·)) (hKm : ∀ k, k ∈ K ↔ k ∈ extra ++ fs.map (·.1))
    (hasc : (ms.map (·.1)).Pairwise (· < ·)) : ms.map (·.1) = K := by
  apply sorted_eq _ _ hasc hK
  intro x
  rw [hKm]
  constructor
  · intro hx
    obtain ⟨⟨k, v⟩, hmem, rfl⟩ := List.mem_map.mp hx
    simp only [unknownSpec, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq,
      Classical.not_not] at hu
    exact hu (k, v) hmem
  · intro hx
    rcases List.mem_append.mp hx with hx | hx
    · exact lookup_mem (hd x hx)
    · simp only [missingSpec, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq] at hm
      exact lookup_mem (hm x hx)

end FvdepAudit.Doc.Proof
