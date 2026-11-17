import FvdepAudit.Build.Spec

/-! Proofs of K5's eviction + K6's validation claims (contract `docs/contracts/U5-sandbox.md` K5,
K6; statements = `FvdepLedger.Rows.BuildClaims`). -/

namespace FvdepAudit.Build.Proof

open FvdepCore.Build FvdepAudit.Build.Spec

theorem charged_cons (e : Entry) (es : List Entry) : charged (e :: es) = e.bytes + charged es := by
  simp [charged]

theorem foldl_bytes (es : List Entry) (n : Nat) : es.foldl (· + ·.bytes) n = n + charged es := by
  induction es generalizing n with
  | nil => simp [charged]
  | cons e es ih =>
    rw [List.foldl_cons, ih, charged_cons]; omega

theorem takeWhileOver_spec (target : Nat) :
    ∀ (cs : List Entry) (total : Nat),
      ∃ n,
        takeWhileOver target total cs = (cs.take n).map (·.key) ∧
          (n = cs.length ∨ total - charged (cs.take n) ≤ target) ∧
          ∀ j < n, target < total - charged (cs.take j)
  | [], total => ⟨0, by simp [takeWhileOver], Or.inl rfl, fun j hj => absurd hj (by omega)⟩
  | e :: rest, total => by
    unfold takeWhileOver
    by_cases ht : target < total
    · simp only [ht, ↓reduceIte]
      obtain ⟨n, hres, hstop, hmin⟩ := takeWhileOver_spec target rest (total - e.bytes)
      refine ⟨n + 1, by simp [hres], ?_, fun j hj => ?_⟩
      · rcases hstop with h | h
        · exact Or.inl (by simp [h])
        · refine Or.inr ?_
          simp only [List.take_succ_cons, charged_cons]
          omega
      · cases j with
        | zero => simpa [charged] using ht
        | succ j =>
          have := hmin j (by omega)
          simp only [List.take_succ_cons, charged_cons]
          omega
    · simp only [ht, ↓reduceIte]
      exact
        ⟨0, by simp,
          Or.inr
            (by
              simp [charged]; omega),
          fun j hj => absurd hj (by omega)⟩

theorem before_lru {a b : Entry} (h : before a b = true) : LruBefore a b := by
  simp only [before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2⟩

theorem before_trans (a b c : Entry) (h1 : before a b = true) (h2 : before b c = true) :
    before a c = true := by
  have := before_lru h1
  have := before_lru h2
  simp only [before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  unfold LruBefore at *
  rcases ‹a.used < b.used ∨ _› with h | ⟨h, hk⟩ <;> rcases ‹b.used < c.used ∨ _› with h' | ⟨h', hk'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, String.le_trans hk hk'⟩

theorem before_total (a b : Entry) : (before a b || before b a) = true := by
  simp only [before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  rcases Nat.lt_trichotomy a.used b.used with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases String.le_total a.key b.key with hk | hk
    · exact Or.inl (Or.inr ⟨h, hk⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hk⟩)
  · exact Or.inr (Or.inl h)

/-- K5: the plan takes, from the unpinned entries in (used, key) order, the shortest prefix that
brings the charged total to the target or under it — every one when none does. -/
theorem evict_exact (entries : List Entry) (target : Nat) :
    ∃ cands : List Entry,
      cands.Perm (entries.filter (!·.pinned)) ∧
        cands.Pairwise LruBefore ∧
        ∃ n,
          evictPlan entries target = (cands.take n).map (·.key) ∧
            (n = cands.length ∨ charged entries - charged (cands.take n) ≤ target) ∧
            ∀ j < n, target < charged entries - charged (cands.take j) := by
  refine ⟨(entries.filter (!·.pinned)).mergeSort before, List.mergeSort_perm _ _, ?_, ?_⟩
  · exact (List.pairwise_mergeSort before_trans before_total _).imp before_lru
  · have :=
      takeWhileOver_spec target ((entries.filter (!·.pinned)).mergeSort before)
        (entries.foldl (· + ·.bytes) 0)
    rw [foldl_bytes, Nat.zero_add] at this
    simpa [evictPlan, foldl_bytes] using this

/-- K6: `validate` accepts exactly the valid entries. -/
theorem validate_exact (h : ByteArray → String) (dir : String) (m : Manifest)
    (files : List FileRec) : validate h dir m files = true ↔ EntryValid h dir m files := by
  simp only [validate, keyOf, metadata, EntryValid, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.any_eq_false, List.all_eq_true, List.any_eq_true, List.mem_map, List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨hm, hu⟩⟩, h4⟩, h5⟩
    refine ⟨h1, h2, fun a ha => ?_, hm, hu, fun a ha => ?_, fun f hf => ?_⟩
    · have := h3 a.path ⟨a, ha, rfl⟩
      simpa [not_or] using this
    · obtain ⟨f, hf, hfa⟩ := h4 a ha
      rw [← hfa]; exact hf
    · rcases h5 f hf with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · obtain ⟨a, ha, hap⟩ := h
        exact Or.inr (Or.inr ⟨a, ha, hap⟩)
  · rintro ⟨h1, h2, h3, hm, hu, h4, h5⟩
    refine
      ⟨⟨⟨⟨⟨h1, h2⟩, fun p ⟨a, ha, hap⟩ => ?_⟩, ⟨hm, hu⟩⟩, fun a ha => ⟨a, h4 a ha, rfl⟩⟩,
        fun f hf => ?_⟩
    · subst hap; simpa [not_or] using h3 a ha
    · rcases h5 f hf with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

end FvdepAudit.Build.Proof
