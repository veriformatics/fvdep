import FvdepAudit.Manifest.Proof.Entry

/-! T5 `ValidateExact` (acceptance): `validate` accepts exactly the trees that spell a well-formed
manifest, returning that manifest. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

theorem check_none_iff {t : Tree} :
    check t = none ↔
      ∃ ms,
        t = .tbl ms ∧
          (ms.map (·.1)).Nodup ∧
          ms.lookup "schema" = some (.int 1) ∧
          (∀ m ∈ ms, m.1 ∈ rootKeys) ∧
          "library" ∈ ms.map (·.1) ∧ ∀ m ∈ ms, rootValue m.1 m.2 = none := by
  cases t with
  | tbl ms =>
    simp only [check, Tree.tbl.injEq, exists_eq_left']
    cases hr : repeatedKey ms with
    | some k =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hd
      simp [(repeatedKey_none_iff ms).mpr hd] at hr
    | none =>
      have hd := (repeatedKey_none_iff ms).mp hr
      simp only [hd, true_and]
      cases hs : ms.lookup "schema" with
      | none => simp
      | some v =>
        cases v with
        | int n =>
          by_cases hn : n = 1
          · subst hn
            simp only [beq_self_eq_true, ite_true, orElse_eq, Option.or_eq_none_iff, true_and]
            rw [firstKey_none_iff, firstMissing_none_iff, valuesCheck_none_iff]
            have hkeys : ∀ k, k ∈ (byKey ms).map (·.1) ↔ k ∈ ms.map (·.1) := fun k =>
              ((byKey_perm ms).map (·.1)).mem_iff
            constructor
            · rintro ⟨h1, h2, h3⟩
              refine
                ⟨fun m hm => by simpa using h1 m (mem_byKey.mpr hm),
                  (hkeys "library").mp (h2 "library" (by simp)), fun m hm =>
                  h3 m (mem_byKey.mpr hm)⟩
            · rintro ⟨h1, h2, h3⟩
              refine
                ⟨fun m hm => by simpa using h1 m (mem_byKey.mp hm), fun k hk => ?_, fun m hm =>
                  h3 m (mem_byKey.mp hm)⟩
              simp only [List.mem_singleton] at hk
              subst hk
              exact (hkeys "library").mpr h2
          · have : (n == 1) = false := by simpa using hn
            simp [this, hn]
        | _ => simp
  | _ => simp [check]

theorem rootValue_library (v : Tree) :
    rootValue "library" v = tableCheck "commit" true isCommit [.key "library"] v := by
  simp [rootValue]

theorem rootValue_modules (v : Tree) : rootValue "modules" v = modulesCheck [.key "modules"] v := by
  simp [rootValue]

theorem rootValue_policy (v : Tree) :
    rootValue "policy" v = tableCheck "proof" false isPolicy [.key "policy"] v := by
  simp [rootValue]

theorem rootValue_schema (v : Tree) : rootValue "schema" v = none := by simp [rootValue]

theorem modulesCheck_none_iff {p : List PathSeg} {v : Tree} :
    modulesCheck p v = none ↔
      ∃ es,
        v = .tbl es ∧
          (es.map (·.1)).Nodup ∧
          ∀ m ∈ es, isModuleId m.1 = true ∧ entryCheck (p ++ [.key m.1]) m.2 = none := by
  cases v with
  | tbl es =>
    simp only [modulesCheck, Tree.tbl.injEq, exists_eq_left']
    cases hr : repeatedKey es with
    | some k =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hd
      simp [(repeatedKey_none_iff es).mpr hd] at hr
    | none =>
      have hd := (repeatedKey_none_iff es).mp hr
      simp only [hd, true_and]
      rw [valuesCheck_none_iff]
      constructor
      · intro h m hm
        have := h m (mem_byKey.mpr hm)
        by_cases hid : isModuleId m.1 = true
        · simp only [hid, ite_true] at this
          exact ⟨hid, this⟩
        · simp [hid] at this
      · intro h m hm
        obtain ⟨hid, he⟩ := h m (mem_byKey.mp hm)
        simp [hid, he]
  | _ => simp [modulesCheck]

theorem entryCheck_tbl {p : List PathSeg} {v : Tree} (h : entryCheck p v = none) :
    ∃ fs, v = .tbl fs := by
  cases v with
  | tbl fs => exact ⟨fs, rfl⟩
  | _ => simp [entryCheck] at h

theorem entryId_entryOf {k : String} (h : isModuleId k = true) (v : Tree) :
    entryId (entryOf k v) = k := by
  obtain ⟨m, hm, hmk, _⟩ := moduleId_of h
  simp [entryId, entryOf, hm, hmk]

/-- The extracted `[modules]` list, entry by entry, from a list holding the same ids in order. -/
theorem map_entries {L : List (String × Tree)} {es : List Entry} (hk : L.map (·.1) = es.map entryId)
    (h : ∀ x ∈ L, ∀ e ∈ es, x.1 = entryId e → entryOf x.1 x.2 = e) :
    L.map (fun x => entryOf x.1 x.2) = es := by
  induction L generalizing es with
  | nil =>
    cases es with
    | nil => rfl
    | cons _ _ => simp at hk
  | cons x L ih =>
    cases es with
    | nil => simp at hk
    | cons e es =>
      simp only [List.map_cons, List.cons.injEq] at hk ⊢
      obtain ⟨hk1, hk2⟩ := hk
      exact
        ⟨h x (by simp) e (by simp) hk1, ih hk2 fun y hy f hf => h y (by simp [hy]) f (by simp [hf])⟩

/-- B, `[policy]`: the accepted member spells the extracted policy. -/
theorem accept_policy {ms : List (String × Tree)}
    (hrv : ∀ k v, ms.lookup k = some v → rootValue k v = none) :
    PolicySpells (ms.lookup "policy") (extract (.tbl ms)).policy := by
  cases hp : ms.lookup "policy" with
  | none =>
    left
    simp [extract, tableOf, hp, strOpt]
  | some pv =>
    have := hrv _ _ hp
    rw [rootValue_policy, tableCheck_none_iff] at this
    rcases this with ⟨rfl, _⟩ | ⟨w, rfl, hw⟩
    · right; left
      simp [extract, tableOf, hp, strOpt]
    · right; right
      have hw' := (isPolicy_iff w).mp hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl <;> simp [extract, tableOf, hp, strOpt, policyWord]

/-- B, `[modules]`: the accepted member spells the extracted entries, each well formed, ids
strictly ascending. -/
theorem accept_modules {ms : List (String × Tree)}
    (hrv : ∀ k v, ms.lookup k = some v → rootValue k v = none) :
    ModulesSpell (ms.lookup "modules") (extract (.tbl ms)).modules ∧
      WellFormed (extract (.tbl ms)) := by
  cases hm : ms.lookup "modules" with
  | none =>
    have he : (extract (.tbl ms)).modules = [] := by simp [extract, tableOf, hm, byKey_nil]
    exact ⟨Or.inl ⟨rfl, he⟩, by simp [WellFormed, he]⟩
  | some mv =>
    have := hrv _ _ hm
    rw [rootValue_modules, modulesCheck_none_iff] at this
    obtain ⟨es, rfl, hde, hent⟩ := this
    have he : (extract (.tbl ms)).modules = (byKey es).map fun e => entryOf e.1 e.2 := by
      simp [extract, tableOf, hm]
    have hids : ((byKey es).map fun e => entryOf e.1 e.2).map entryId = (byKey es).map (·.1) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact entryId_entryOf (hent x (mem_byKey.mp hx)).1 x.2
    have hacc :
      ∀ x ∈ byKey es,
        ∃ fs,
          x.2 = .tbl fs ∧ EntryWF (entryOf x.1 x.2) ∧ fs.Perm (entryLayout (entryOf x.1 x.2)) := by
      intro x hx
      obtain ⟨hid, hc⟩ := hent x (mem_byKey.mp hx)
      obtain ⟨fs, hfs⟩ := entryCheck_tbl hc
      rw [hfs] at hc ⊢
      exact ⟨fs, rfl, accept_entry hid hc⟩
    refine ⟨Or.inr ⟨es, rfl, ?_, ?_⟩, ?_⟩
    · rw [he, hids]
      exact ((byKey_perm es).map (·.1)).symm
    · intro e hmem
      rw [he] at hmem
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨fs, hfs, _, hp⟩ := hacc x hx
      refine ⟨fs, ?_, hp⟩
      rw [entryId_entryOf (hent x (mem_byKey.mp hx)).1, ← hfs]
      exact lookup_of_mem hde (mem_byKey.mp hx)
    · refine ⟨fun e hmem => ?_, ?_⟩
      · rw [he] at hmem
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨_, _, hwf, _⟩ := hacc x hx
        exact hwf
      · rw [he, hids]
        exact byKey_keys_lt hde

/-- B: an accepted tree spells the well-formed manifest it denotes. -/
theorem accept_spells {t : Tree} (h : check t = none) : ManifestSpec t (extract t) := by
  obtain ⟨ms, rfl, hd, hs, hroot, hlib, hval⟩ := check_none_iff.mp h
  have hrv : ∀ k v, ms.lookup k = some v → rootValue k v = none := fun k v hk =>
    hval (k, v) (mem_of_lookup hk)
  obtain ⟨lv, hlv⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff.mpr hlib)
  have hl := hrv _ _ hlv
  rw [rootValue_library, tableCheck_none_iff] at hl
  rcases hl with ⟨_, hfalse⟩ | ⟨sc, rfl, hsc⟩
  · exact absurd hfalse (by simp)
  obtain ⟨c, rfl⟩ := (isCommit_iff sc).mp hsc
  have hlib' : (extract (.tbl ms)).library = c := by
    simp [extract, tableOf, hlv, strOpt, Commit.parse_toString]
  have hmods := accept_modules hrv
  refine ⟨hmods.2, ms, rfl, hd, fun k hk => ?_, hs, by rw [hlv, hlib'], accept_policy hrv, hmods.1⟩
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
  simpa [rootKeys] using hroot m hm

/-- Strictly ascending strings are distinct. -/
theorem nodup_of_lt {l : List String} (h : l.Pairwise (· < ·)) : l.Nodup :=
  show l.Pairwise (fun a b => a ≠ b) from
    h.imp fun {a b} hab he => by
      subst he
      exact Std.lt_irrefl hab

theorem eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'
      exact absurd hab.symm (hn.1 b hb')
    · subst hb'
      exact absurd hab (hn.1 a ha')
    · exact eq_of_map_nodup hn.2 ha' hb' hab

theorem entryId_isModuleId {e : Entry} (hw : EntryWF e) : isModuleId (entryId e) = true :=
  (isModuleId_iff _).mpr ⟨e.decl.module, rfl, hw.1⟩

/-- C, `[modules]`: a spelled member passes the check + reads back as the entries. -/
theorem spelled_modules {es : List (String × Tree)} {mods : List Entry} (hw : ∀ e ∈ mods, EntryWF e)
    (hasc : (mods.map entryId).Pairwise (· < ·)) (hk : (es.map (·.1)).Perm (mods.map entryId))
    (he : ∀ e ∈ mods, ∃ fs, es.lookup (entryId e) = some (.tbl fs) ∧ fs.Perm (entryLayout e)) :
    modulesCheck [.key "modules"] (.tbl es) = none ∧
      (byKey es).map (fun x => entryOf x.1 x.2) = mods := by
  have hids : (mods.map entryId).Nodup := nodup_of_lt hasc
  have hde : (es.map (·.1)).Nodup := hk.nodup_iff.mpr hids
  have hmem :
    ∀ x ∈ es, ∃ e ∈ mods, entryId e = x.1 ∧ ∃ fs, x.2 = .tbl fs ∧ fs.Perm (entryLayout e) := by
    intro x hx
    obtain ⟨e, he', hex⟩ := List.mem_map.mp (hk.mem_iff.mp (List.mem_map.mpr ⟨x, hx, rfl⟩))
    obtain ⟨fs, hfs, hp⟩ := he e he'
    refine ⟨e, he', hex, fs, ?_, hp⟩
    have := lookup_of_mem hde hx
    rw [← hex, hfs] at this
    exact (Option.some.inj this).symm
  refine ⟨modulesCheck_none_iff.mpr ⟨es, rfl, hde, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨e, he', hex, fs, hfs, hp⟩ := hmem x hx
    rw [← hex, hfs]
    exact ⟨entryId_isModuleId (hw e he'), (layout_entry (hw e he') hp).1⟩
  · apply map_entries
    · apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
      · intro a b _ _ hab hba
        exact Std.le_antisymm hab hba
      · exact byKey_keys_le es
      · exact hasc.imp Std.le_of_lt
      · exact ((byKey_perm es).map (·.1)).trans hk
    · intro x hx e he' hxe
      obtain ⟨e', he'', hex', fs, hfs, hp⟩ := hmem x (mem_byKey.mp hx)
      have hee : e' = e := eq_of_map_nodup hids he'' he' (hex'.trans hxe)
      subst hee
      rw [hfs, hxe]
      exact (layout_entry (p := []) (hw e' he'') hp).2

/-- C: a tree spelling a well-formed manifest passes the check + reads back as it. -/
theorem spells_check {t : Tree} {m : ManifestFile} (h : ManifestSpec t m) :
    check t = none ∧ extract t = m := by
  obtain ⟨⟨hw, hasc⟩, ms, rfl, hd, hkeys, hs, hl, hp, hm⟩ := h
  obtain ⟨lib, pol, mods⟩ := m
  simp only at hw hasc hl hp hm
  -- the modules member, both ways
  have hmods :
    (∀ v, ms.lookup "modules" = some v → modulesCheck [.key "modules"] v = none) ∧
      (byKey (tableOf (ms.lookup "modules"))).map (fun x => entryOf x.1 x.2) = mods := by
    rcases hm with ⟨hn, rfl⟩ | ⟨es, hes, hk, he⟩
    · refine
        ⟨(fun v hv => by
            rw [hn] at hv; cases hv),
          ?_⟩
      simp [hn, tableOf, byKey_nil]
    · have := spelled_modules hw hasc hk he
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [hes] at hv
        cases hv
        exact this.1
      · simp only [hes, tableOf]
        exact this.2
  have hrv : ∀ x ∈ ms, rootValue x.1 x.2 = none := by
    intro x hx
    obtain ⟨k, v⟩ := x
    have hk := hkeys k (List.mem_map.mpr ⟨(k, v), hx, rfl⟩)
    have hlx : ms.lookup k = some v := lookup_of_mem hd hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [hl] at hlx
      cases hlx
      exact
        (rootValue_library _).trans
          (tableCheck_none_iff.mpr (Or.inr ⟨_, rfl, (isCommit_iff _).mpr ⟨lib, rfl⟩⟩))
    · exact (rootValue_modules v).trans (hmods.1 v hlx)
    · rw [rootValue_policy]
      rcases hp with ⟨hn, _⟩ | ⟨hv, rfl⟩ | hv
      · rw [hn] at hlx
        cases hlx
      · rw [hv] at hlx
        cases hlx
        exact tableCheck_none_iff.mpr (Or.inl ⟨rfl, rfl⟩)
      · rw [hv] at hlx
        cases hlx
        refine tableCheck_none_iff.mpr (Or.inr ⟨_, rfl, (isPolicy_iff _).mpr ?_⟩)
        cases pol <;> simp [policyWord]
    · exact rootValue_schema v
  refine
    ⟨check_none_iff.mpr
        ⟨ms, rfl, hd, hs, fun x hx => ?_,
          lookup_isSome_iff.mp
            (by
              rw [hl]; rfl),
          hrv⟩,
      ?_⟩
  · simpa [rootKeys] using hkeys x.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · simp only [extract, tableOf, ManifestFile.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simp [hl, strOpt, Commit.parse_toString]
    · rcases hp with ⟨hn, rfl⟩ | ⟨hv, rfl⟩ | hv
      · simp [hn, strOpt]
      · simp [hv, strOpt]
      · cases pol <;> simp [hv, strOpt, policyWord]
    · exact hmods.2

/-- T5 `ValidateExact` (acceptance). -/
theorem validate_ok (t : Tree) (m : ManifestFile) : validate t = .ok m ↔ ManifestSpec t m := by
  constructor
  · intro h
    unfold validate at h
    cases hc : check t with
    | some e => simp [hc] at h
    | none =>
      simp only [hc, Except.ok.injEq] at h
      rw [← h]
      exact accept_spells hc
  · intro h
    obtain ⟨hc, he⟩ := spells_check h
    simp [validate, hc, he]

end FvdepAudit.Manifest.Proof
