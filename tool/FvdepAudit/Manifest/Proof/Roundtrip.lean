import FvdepAudit.Manifest.Proof.Refuse

/-! T5 `ValidateWellFormed` + `TreeRoundTrip`: an accepted manifest is well formed; the tree a
well-formed manifest prints to validates back to it. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

/-- T5 `ValidateWellFormed`. -/
theorem validate_wellFormed (t : Tree) (m : ManifestFile) (h : validate t = .ok m) :
    WellFormed m := ((validate_ok t m).mp h).1

/-- Two member lists with distinct keys, the same keys + the same value at each key, are
permutations of each other. -/
theorem perm_of_keys {ms ns : List (String × Tree)} (hm : (ms.map (·.1)).Nodup)
    (hk : (ms.map (·.1)).Perm (ns.map (·.1))) (h : ∀ k ∈ ms.map (·.1), ms.lookup k = ns.lookup k) :
    ms.Perm ns := by
  have hn : (ns.map (·.1)).Nodup := hk.nodup_iff.mp hm
  apply perm_of_lookup hm hn
  intro k
  by_cases hkm : k ∈ ms.map (·.1)
  · exact h k hkm
  · rw [lookup_none_iff.mpr hkm, lookup_none_iff.mpr fun hn' => hkm (hk.mem_iff.mpr hn')]

/-- A well-formed entry's printed members = its layout, reordered. -/
theorem entryMembers_perm {e : Entry} (hw : EntryWF e) : (entryMembers e).Perm (entryLayout e) := by
  obtain ⟨⟨module, version, shape, kind, impl, proof, adapter⟩, im, pm⟩ := e
  obtain ⟨_, _, hk⟩ := hw
  cases kind with
  | proof =>
    obtain ⟨hsh, ⟨i, rfl, _⟩, ⟨x, rfl, _⟩, rfl, _, _, _⟩ := hk
    obtain ⟨sh, rfl⟩ := Option.ne_none_iff_exists'.mp hsh
    apply
      perm_of_keys (by simp [entryMembers])
        (by
          simp [entryMembers, entryLayout]; decide)
    intro k hk
    simp only [entryMembers, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> cases sh <;>
      simp [entryMembers, entryLayout, List.lookup, shapeText, shapeWord]
  | differential =>
    obtain ⟨rfl, rfl, rfl, ⟨argv, rfl, _⟩, rfl, rfl⟩ := hk
    apply
      perm_of_keys (by simp [entryMembers])
        (by
          simp [entryMembers, entryLayout]; decide)
    intro k hk
    simp only [entryMembers, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [entryMembers, entryLayout, List.lookup]

theorem policyText_eq (p : Policy) : policyText p = policyWord p := by cases p <;> rfl

/-- The tree `toTree m` spells `m`. -/
theorem toTree_spells {m : ManifestFile} (hw : WellFormed m) : Spells (toTree m) m := by
  obtain ⟨lib, pol, mods⟩ := m
  obtain ⟨hwe, hasc⟩ := hw
  simp only at hwe hasc
  have hids := nodup_of_lt hasc
  by_cases hm : mods = []
  · subst hm
    refine ⟨_, rfl, by simp, by simp, by simp, by simp [List.lookup], ?_, ?_⟩
    · right; right
      simp [List.lookup, policyText_eq]
    · left
      simp
  · have hne : mods.isEmpty = false := by simpa using hm
    let es := mods.map fun e => (toString e.decl.module, Tree.tbl (entryMembers e))
    have hkeys : es.map (·.1) = mods.map entryId := by simp [es, entryId]
    refine ⟨_, rfl, ?_, ?_, by simp [hne], by simp [hne, List.lookup], ?_, ?_⟩
    · simp [hne]
    · intro k hk
      simp [hne] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hk with rfl | rfl | rfl | rfl <;> simp
    · right; right
      simp [hne, List.lookup, policyText_eq]
    · right
      refine ⟨es, by simp [hne, es, List.lookup], by rw [hkeys], fun e he => ?_⟩
      refine ⟨entryMembers e, ?_, entryMembers_perm (hwe e he)⟩
      apply
        lookup_of_mem
          (by
            rw [hkeys]; exact hids)
      exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- T5 `TreeRoundTrip`. -/
theorem tree_roundtrip (m : ManifestFile) (hw : WellFormed m) : validate (toTree m) = .ok m :=
  (validate_ok _ _).mpr ⟨hw, toTree_spells hw⟩

end FvdepAudit.Manifest.Proof
