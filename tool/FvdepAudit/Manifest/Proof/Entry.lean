import FvdepAudit.Manifest.Proof.Fields

/-! One `[modules."<id>"]` entry: the shipped check accepts exactly the tables holding the layout of
a well-formed entry (in any member order), and extraction reads that entry back. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec
variable {β : Type}

theorem nodup_of_keys {ms : List (String × β)} (h : (ms.map (·.1)).Nodup) : ms.Nodup :=
  List.Pairwise.of_map (·.1) (fun _ _ hab hba => hab (hba ▸ rfl)) h

theorem perm_of_lookup {ms ns : List (String × β)} (hm : (ms.map (·.1)).Nodup)
    (hn : (ns.map (·.1)).Nodup) (h : ∀ k, ms.lookup k = ns.lookup k) : ms.Perm ns := by
  apply (List.perm_ext_iff_of_nodup (nodup_of_keys hm) (nodup_of_keys hn)).mpr
  intro x
  obtain ⟨k, v⟩ := x
  rw [← lookup_eq_some_iff_mem hm, ← lookup_eq_some_iff_mem hn, h k]

theorem lookup_eq_of_perm {ms ns : List (String × β)} (hn : (ns.map (·.1)).Nodup) (hp : ms.Perm ns)
    (k : String) : ms.lookup k = ns.lookup k := lookup_perm hn hp k

theorem entryCheck_none_iff {p : List PathSeg} {fs : List (String × Tree)} :
    entryCheck p (.tbl fs) = none ↔
      (fs.map (·.1)).Nodup ∧
        ∃ kind,
          entryKind p fs = .ok kind ∧
            (∀ m ∈ fs, m.1 ∈ entryKeys) ∧
            (∀ m ∈ fs, m.1 ∉ forbiddenKeys kind) ∧
            (∀ k ∈ requiredKeys kind, k ∈ fs.map (·.1)) ∧
            (∀ m ∈ fs, entryValue p m.1 m.2 = none) ∧ overlap p fs = none := by
  simp only [entryCheck]
  cases hr : repeatedKey fs with
  | some k =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hd
    simp [(repeatedKey_none_iff fs).mpr hd] at hr
  | none =>
    have hd := (repeatedKey_none_iff fs).mp hr
    simp only [hd, true_and]
    cases hk : entryKind p fs with
    | error e => simp
    | ok kind =>
      simp only [orElse_eq, Option.or_eq_none_iff, Except.ok.injEq, exists_eq_left']
      rw [firstKey_none_iff, firstKey_none_iff, firstMissing_none_iff, valuesCheck_none_iff]
      have hkeys : ∀ k, k ∈ (byKey fs).map (·.1) ↔ k ∈ fs.map (·.1) := fun k =>
        ((byKey_perm fs).map (·.1)).mem_iff
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine
          ⟨fun m hm => ?_, fun m hm => ?_, fun k hk => (hkeys k).mp (h3 k hk), fun m hm =>
            h4 m (mem_byKey.mpr hm), h5⟩
        · simpa using h1 m (mem_byKey.mpr hm)
        · simpa using h2 m (mem_byKey.mpr hm)
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine
          ⟨fun m hm => ?_, fun m hm => ?_, fun k hk => (hkeys k).mpr (h3 k hk), fun m hm =>
            h4 m (mem_byKey.mp hm), h5⟩
        · simpa using h1 m (mem_byKey.mp hm)
        · simpa using h2 m (mem_byKey.mp hm)

theorem entryKind_ok_iff {p : List PathSeg} {fs : List (String × Tree)} {kind : Kind} :
    entryKind p fs = .ok kind ↔
      kind = .proof ∧ fs.lookup "evidence" = none ∨
        kind = .differential ∧ fs.lookup "evidence" = some (.str "differential") := by
  unfold entryKind
  cases h : fs.lookup "evidence" with
  | none => cases kind <;> simp
  | some w =>
    cases w with
    | str s =>
      by_cases hs : s = "differential"
      · subst hs
        cases kind <;> simp
      · have : (s == "differential") = false := by simpa using hs
        simp [this, hs]
    | _ => simp

theorem entryOf_congr (k0 : String) {fs gs : List (String × Tree)}
    (h : ∀ k, fs.lookup k = gs.lookup k) : entryOf k0 (.tbl fs) = entryOf k0 (.tbl gs) := by
  simp only [entryOf, tableOf, h]
  rfl

/-- A required key's value, accepted by `entryValue`. -/
theorem required_value {p : List PathSeg} {fs : List (String × Tree)} {k : String}
    (hk : k ∈ fs.map (·.1)) (h4 : ∀ m ∈ fs, entryValue p m.1 m.2 = none) :
    ∃ w, fs.lookup k = some w ∧ entryValue p k w = none := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff.mpr hk)
  exact ⟨w, hw, h4 (k, w) (mem_of_lookup hw)⟩

theorem entryValue_version (p : List PathSeg) (w : Tree) :
    entryValue p "version" w = strField isVersion (p ++ [.key "version"]) w := by simp [entryValue]

theorem entryValue_shape (p : List PathSeg) (w : Tree) :
    entryValue p "shape" w = strField isShape (p ++ [.key "shape"]) w := by simp [entryValue]

theorem entryValue_impl (p : List PathSeg) (w : Tree) :
    entryValue p "impl" w = strField isConstName (p ++ [.key "impl"]) w := by simp [entryValue]

theorem entryValue_proof (p : List PathSeg) (w : Tree) :
    entryValue p "proof" w = strField isConstName (p ++ [.key "proof"]) w := by simp [entryValue]

theorem entryValue_implModules (p : List PathSeg) (w : Tree) :
    entryValue p "impl_modules" w =
      arrayCheck (fun _ => isModuleName) true (p ++ [.key "impl_modules"]) w := by
  simp [entryValue]

theorem entryValue_proofModules (p : List PathSeg) (w : Tree) :
    entryValue p "proof_modules" w =
      arrayCheck (fun _ => isModuleName) true (p ++ [.key "proof_modules"]) w := by
  simp [entryValue]

theorem entryValue_adapter (p : List PathSeg) (w : Tree) :
    entryValue p "adapter" w =
      arrayCheck (fun i s => isArg (i == 0) s) false (p ++ [.key "adapter"]) w := by
  simp [entryValue]

theorem elemsOk_const {f : String → Bool} :
    ∀ {i : Nat} {ss : List String}, ElemsOk (fun _ => f) i ss ↔ ∀ s ∈ ss, f s = true
  | _, [] => by simp [ElemsOk]
  | i, s :: ss => by
    simp only [ElemsOk, List.mem_cons, forall_eq_or_imp]
    rw [elemsOk_const]

theorem elemsOk_arg_succ :
    ∀ {i : Nat} {ss : List String},
      ElemsOk (fun i s => isArg (i == 0) s) (i + 1) ss ↔ ∀ s ∈ ss, isArg false s = true
  | _, [] => by simp [ElemsOk]
  | i, s :: ss => by
    simp only [ElemsOk, List.mem_cons, forall_eq_or_imp]
    have : (i + 1 == 0) = false := by simp
    rw [this, elemsOk_arg_succ]

theorem elemsOk_argv {ss : List String} (hne : ss ≠ []) :
    ElemsOk (fun i s => isArg (i == 0) s) 0 ss ↔ Argv ss := by
  cases ss with
  | nil => exact absurd rfl hne
  | cons a
    rest =>
    show isArg (0 == 0) a = true ∧ ElemsOk (fun i s => isArg (i == 0) s) (0 + 1) rest ↔ _
    rw [elemsOk_arg_succ, beq_self_eq_true]
    constructor
    · rintro ⟨ha, hr⟩
      exact
        ⟨a, rest, rfl, (FvdepAudit.Doc.Proof.isArg_iff true a).mp ha, fun x hx =>
          (FvdepAudit.Doc.Proof.isArg_iff false x).mp (hr x hx)⟩
    · rintro ⟨a', rest', he, ha, hr⟩
      cases he
      exact
        ⟨(FvdepAudit.Doc.Proof.isArg_iff true a).mpr ha, fun x hx =>
          (FvdepAudit.Doc.Proof.isArg_iff false x).mpr (hr x hx)⟩

theorem moduleId_of {k : String} (h : isModuleId k = true) :
    ∃ m, ModuleId.parse k = some m ∧ toString m = k ∧ SpellingFits k := by
  obtain ⟨m, rfl, hf⟩ := (isModuleId_iff k).mp h
  exact ⟨m, ModuleId.parse_toString m, rfl, hf⟩

/-- An entry table the check accepts, as its values: a proof entry. -/
theorem accept_proof_entry {p : List PathSeg} {k0 : String} {fs : List (String × Tree)}
    (hid : isModuleId k0 = true) (hd : (fs.map (·.1)).Nodup) (hev : fs.lookup "evidence" = none)
    (h1 : ∀ m ∈ fs, m.1 ∈ entryKeys) (h2 : ∀ m ∈ fs, m.1 ∉ forbiddenKeys .proof)
    (h3 : ∀ k ∈ requiredKeys .proof, k ∈ fs.map (·.1)) (h4 : ∀ m ∈ fs, entryValue p m.1 m.2 = none)
    (h5 : overlap p fs = none) :
    EntryWF (entryOf k0 (.tbl fs)) ∧ fs.Perm (entryLayout (entryOf k0 (.tbl fs))) := by
  obtain ⟨wv, hwv, hv⟩ := required_value (h3 "version" (by simp [requiredKeys])) h4
  rw [entryValue_version, strField_none_iff] at hv
  obtain ⟨sv, rfl, hsv⟩ := hv
  obtain ⟨ver, rfl, hvfit⟩ := (isVersion_iff sv).mp hsv
  obtain ⟨wsh, hwsh, hsh⟩ := required_value (h3 "shape" (by simp [requiredKeys])) h4
  rw [entryValue_shape, strField_none_iff] at hsh
  obtain ⟨ssh, rfl, hssh⟩ := hsh
  obtain ⟨wi, hwi, hi⟩ := required_value (h3 "impl" (by simp [requiredKeys])) h4
  rw [entryValue_impl, strField_none_iff] at hi
  obtain ⟨si, rfl, hsi⟩ := hi
  obtain ⟨wp, hwp, hpr⟩ := required_value (h3 "proof" (by simp [requiredKeys])) h4
  rw [entryValue_proof, strField_none_iff] at hpr
  obtain ⟨sp, rfl, hsp⟩ := hpr
  obtain ⟨wim, hwim, him⟩ := required_value (h3 "impl_modules" (by simp [requiredKeys])) h4
  rw [entryValue_implModules, arrayCheck_none_iff] at him
  obtain ⟨im, rfl, himne, himok, himnd⟩ := him
  obtain ⟨wpm, hwpm, hpm⟩ := required_value (h3 "proof_modules" (by simp [requiredKeys])) h4
  rw [entryValue_proofModules, arrayCheck_none_iff] at hpm
  obtain ⟨pm, rfl, hpmne, hpmok, hpmnd⟩ := hpm
  have hout : ∀ k, k ∉ requiredKeys .proof → fs.lookup k = none := by
    intro k hk
    apply lookup_none_iff.mpr
    intro hm
    obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hm
    have hne : m.1 ≠ "evidence" := fun he' => by
      have := lookup_isSome_iff.mpr (List.mem_map.mpr ⟨m, hm', rfl⟩)
      rw [he', hev] at this
      simp at this
    have he := h1 m hm'
    have hf := h2 m hm'
    simp only [entryKeys, forbiddenKeys, requiredKeys, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at he hf hk
    rcases he with h | h | h | h | h | h | h | h
    · exact hf h
    · exact hne h
    · exact hk.1 h
    · exact hk.2.1 h
    · exact hk.2.2.1 h
    · exact hk.2.2.2.1 h
    · exact hk.2.2.2.2.1 h
    · exact hk.2.2.2.2.2 h
  let L : List (String × Tree) :=
    [("impl", .str si), ("impl_modules", .arr (im.map .str)), ("proof", .str sp),
      ("proof_modules", .arr (pm.map .str)), ("shape", .str ssh), ("version", .str (toString ver))]
  have hL : ∀ k, fs.lookup k = L.lookup k := by
    intro k
    by_cases hk : k ∈ requiredKeys .proof
    · simp only [requiredKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [L, List.lookup, hwi, hwim, hwp, hwpm, hwsh, hwv]
    · rw [hout k hk]
      symm
      apply lookup_none_iff.mpr
      simpa [L, requiredKeys] using hk
  have hLd : (L.map (·.1)).Nodup := by simp [L]
  obtain ⟨mid, hmid, hmids, hmidfit⟩ := moduleId_of hid
  have hshape : ssh = "fn" ∨ ssh = "abi" := by simpa using (isShape_iff ssh).mp hssh
  have hE :
    entryOf k0 (.tbl fs) =
      { decl :=
          { module := mid
            version := ver
            shape := if ssh = "fn" then some .fn else some .abi
            kind := .proof
            impl := some si
            proof := some sp
            adapter := none }
        implModules := im
        proofModules := pm } := by
    rw [entryOf_congr k0 hL]
    rcases hshape with rfl | rfl <;>
      simp [entryOf, tableOf, L, List.lookup, strOpt, listOf, strings_map, hmid,
        EntryVersion.parse_toString]
  rw [hE]
  have hpermL : fs.Perm L := perm_of_lookup hd hLd hL
  refine ⟨?_, ?_⟩
  · have hovl : ∀ y ∈ im, y ∉ pm := by
      have := h5
      simp only [overlap, Option.map_eq_none_iff, List.find?_eq_none, hwim, hwpm, listOf,
        strings_map] at this
      intro y hy hy'
      have := this y hy
      simp [hy'] at this
    refine
      ⟨by
        show SpellingFits (toString mid); rw [hmids]; exact hmidfit, hvfit, ?_⟩
    show _ ∧ _
    refine
      ⟨by split <;> simp, ⟨si, rfl, (isConstName_iff si).mp hsi⟩,
        ⟨sp, rfl, (isConstName_iff sp).mp hsp⟩, rfl,
        ⟨himne, himnd rfl, fun y hy => (isModuleName_iff y).mp (elemsOk_const.mp himok y hy)⟩,
        ⟨hpmne, hpmnd rfl, fun y hy => (isModuleName_iff y).mp (elemsOk_const.mp hpmok y hy)⟩, hovl⟩
  · have :
      entryLayout
          { decl :=
              { module := mid
                version := ver
                shape := if ssh = "fn" then some .fn else some .abi
                kind := .proof
                impl := some si
                proof := some sp
                adapter := none }
            implModules := im
            proofModules := pm } =
        L := by
      rcases hshape with rfl | rfl <;> simp [entryLayout, L, shapeWord]
    rw [this]
    exact hpermL

/-- An entry table the check accepts, as its values: a differential entry. -/
theorem accept_differential_entry {p : List PathSeg} {k0 : String} {fs : List (String × Tree)}
    (hid : isModuleId k0 = true) (hd : (fs.map (·.1)).Nodup)
    (hev : fs.lookup "evidence" = some (.str "differential")) (h1 : ∀ m ∈ fs, m.1 ∈ entryKeys)
    (h2 : ∀ m ∈ fs, m.1 ∉ forbiddenKeys .differential)
    (h3 : ∀ k ∈ requiredKeys .differential, k ∈ fs.map (·.1))
    (h4 : ∀ m ∈ fs, entryValue p m.1 m.2 = none) :
    EntryWF (entryOf k0 (.tbl fs)) ∧ fs.Perm (entryLayout (entryOf k0 (.tbl fs))) := by
  obtain ⟨wv, hwv, hv⟩ := required_value (h3 "version" (by simp [requiredKeys])) h4
  rw [entryValue_version, strField_none_iff] at hv
  obtain ⟨sv, rfl, hsv⟩ := hv
  obtain ⟨ver, rfl, hvfit⟩ := (isVersion_iff sv).mp hsv
  obtain ⟨wa, hwa, ha⟩ := required_value (h3 "adapter" (by simp [requiredKeys])) h4
  rw [entryValue_adapter, arrayCheck_none_iff] at ha
  obtain ⟨argv, rfl, hane, haok, _⟩ := ha
  have hout : ∀ k, k ∉ requiredKeys .differential → fs.lookup k = none := by
    intro k hk
    apply lookup_none_iff.mpr
    intro hm
    obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hm
    have he := h1 m hm'
    have hf := h2 m hm'
    simp only [entryKeys, forbiddenKeys, requiredKeys, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at he hf hk
    rcases he with h | h | h | h | h | h | h | h
    · exact hk.1 h
    · exact hk.2.1 h
    · exact hf.1 h
    · exact hf.2.1 h
    · exact hf.2.2.1 h
    · exact hf.2.2.2.1 h
    · exact hf.2.2.2.2 h
    · exact hk.2.2 h
  let L : List (String × Tree) :=
    [("adapter", .arr (argv.map .str)), ("evidence", .str "differential"),
      ("version", .str (toString ver))]
  have hL : ∀ k, fs.lookup k = L.lookup k := by
    intro k
    by_cases hk : k ∈ requiredKeys .differential
    · simp only [requiredKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [L, List.lookup, hwa, hev, hwv]
    · rw [hout k hk]
      symm
      apply lookup_none_iff.mpr
      simpa [L, requiredKeys] using hk
  have hLd : (L.map (·.1)).Nodup := by simp [L]
  obtain ⟨mid, hmid, hmids, hmidfit⟩ := moduleId_of hid
  have hE :
    entryOf k0 (.tbl fs) =
      { decl :=
          { module := mid
            version := ver
            shape := none
            kind := .differential
            impl := none
            proof := none
            adapter := some argv }
        implModules := []
        proofModules := [] } := by
    rw [entryOf_congr k0 hL]
    simp [entryOf, tableOf, L, List.lookup, strOpt, listOf, strings_map, hmid,
      EntryVersion.parse_toString]
  rw [hE]
  refine ⟨?_, ?_⟩
  · refine
      ⟨by
        show SpellingFits (toString mid); rw [hmids]; exact hmidfit, hvfit, ?_⟩
    show _ ∧ _
    exact ⟨rfl, rfl, rfl, ⟨argv, rfl, (elemsOk_argv hane).mp haok⟩, rfl, rfl⟩
  · have :
      entryLayout
          { decl :=
              { module := mid
                version := ver
                shape := none
                kind := .differential
                impl := none
                proof := none
                adapter := some argv }
            implModules := []
            proofModules := [] } =
        L := by
      simp [entryLayout, L]
    rw [this]
    exact perm_of_lookup hd hLd hL

/-- T3: an entry table the check accepts spells a well-formed entry (its extraction). -/
theorem accept_entry {p : List PathSeg} {k0 : String} {fs : List (String × Tree)}
    (hid : isModuleId k0 = true) (h : entryCheck p (.tbl fs) = none) :
    EntryWF (entryOf k0 (.tbl fs)) ∧ fs.Perm (entryLayout (entryOf k0 (.tbl fs))) := by
  obtain ⟨hd, kind, hk, h1, h2, h3, h4, h5⟩ := entryCheck_none_iff.mp h
  rcases entryKind_ok_iff.mp hk with ⟨rfl, hev⟩ | ⟨rfl, hev⟩
  · exact accept_proof_entry hid hd hev h1 h2 h3 h4 h5
  · exact accept_differential_entry hid hd hev h1 h2 h3 h4

theorem entryLayout_keys_nodup (e : Entry) : ((entryLayout e).map (·.1)).Nodup := by
  obtain ⟨⟨_, _, _, kind, _, _, _⟩, _, _⟩ := e
  cases kind <;> simp [entryLayout]

theorem isVersion_toString (v : EntryVersion) (h : SpellingFits (toString v)) :
    isVersion (toString v) = true := (isVersion_iff _).mpr ⟨v, rfl, h⟩

theorem arrayCheck_modules {im : List String} {p : List PathSeg} (h : ModuleList im) :
    arrayCheck (fun _ => isModuleName) true p (.arr (im.map .str)) = none :=
  arrayCheck_none_iff.mpr
    ⟨im, rfl, h.1, elemsOk_const.mpr fun y hy => (isModuleName_iff y).mpr (h.2.2 y hy), fun _ =>
      h.2.1⟩

/-- T3: a table holding a well-formed entry's layout (any member order) passes the check and reads
back as that entry. -/
theorem layout_entry {p : List PathSeg} {e : Entry} {fs : List (String × Tree)} (hw : EntryWF e)
    (hp : fs.Perm (entryLayout e)) :
    entryCheck p (.tbl fs) = none ∧ entryOf (entryId e) (.tbl fs) = e := by
  have hLd := entryLayout_keys_nodup e
  have hd : (fs.map (·.1)).Nodup := ((hp.map (·.1)).nodup_iff).mpr hLd
  have hlk : ∀ k, fs.lookup k = (entryLayout e).lookup k := lookup_eq_of_perm hLd hp
  have hall : ∀ {q : String × Tree → Prop}, (∀ m ∈ entryLayout e, q m) → ∀ m ∈ fs, q m :=
    fun {q} h m hm => h m (hp.mem_iff.mp hm)
  have hkeys : ∀ k, k ∈ fs.map (·.1) ↔ k ∈ (entryLayout e).map (·.1) := fun k =>
    (hp.map (·.1)).mem_iff
  rw [entryOf_congr _ hlk]
  obtain ⟨⟨module, version, shape, kind, impl, proof, adapter⟩, im, pm⟩ := e
  obtain ⟨hmfit, hvfit, hk⟩ := hw
  cases kind with
  | proof =>
    obtain ⟨hsh, ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl, him, hpm, hdis⟩ := hk
    obtain ⟨sh, rfl⟩ := Option.ne_none_iff_exists'.mp hsh
    refine ⟨entryCheck_none_iff.mpr ⟨hd, .proof, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact
        entryKind_ok_iff.mpr
          (Or.inl
            ⟨rfl, by
              rw [hlk]; simp [entryLayout, List.lookup]⟩)
    · exact hall (by simp [entryLayout, entryKeys])
    · exact hall (by simp [entryLayout, forbiddenKeys])
    · intro k hk'
      rw [hkeys]
      simpa [entryLayout, requiredKeys] using hk'
    · apply hall
      cases sh <;>
        simp [entryLayout, entryValue_version, entryValue_shape, entryValue_impl, entryValue_proof,
          entryValue_implModules, entryValue_proofModules, strField, isVersion_toString _ hvfit,
          (isConstName_iff _).mpr hi, (isConstName_iff _).mpr hx, arrayCheck_modules him,
          arrayCheck_modules hpm, shapeWord, isShape]
    · have hi' : listOf (fs.lookup "impl_modules") = im := by
        rw [hlk]
        simp [entryLayout, List.lookup, listOf, strings_map]
      have hp' : listOf (fs.lookup "proof_modules") = pm := by
        rw [hlk]
        simp [entryLayout, List.lookup, listOf, strings_map]
      simp only [overlap, hi', hp', Option.map_eq_none_iff, List.find?_eq_none]
      intro y hy
      simpa using hdis y hy
    · cases sh <;>
        simp [entryOf, tableOf, entryLayout, List.lookup, strOpt, listOf, strings_map, entryId,
          ModuleId.parse_toString, EntryVersion.parse_toString, shapeWord]
  | differential =>
    obtain ⟨rfl, rfl, rfl, ⟨argv, rfl, hargv⟩, rfl, rfl⟩ := hk
    have hane : argv ≠ [] := by
      obtain ⟨a, rest, rfl, _⟩ := hargv
      simp
    refine ⟨entryCheck_none_iff.mpr ⟨hd, .differential, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact
        entryKind_ok_iff.mpr
          (Or.inr
            ⟨rfl, by
              rw [hlk]; simp [entryLayout, List.lookup]⟩)
    · exact hall (by simp [entryLayout, entryKeys])
    · exact hall (by simp [entryLayout, forbiddenKeys])
    · intro k hk'
      rw [hkeys]
      simpa [entryLayout, requiredKeys] using hk'
    · apply hall
      have ha :
        arrayCheck (fun i s => isArg (i == 0) s) false (p ++ [.key "adapter"])
            (.arr (argv.map .str)) =
          none :=
        arrayCheck_none_iff.mpr ⟨argv, rfl, hane, (elemsOk_argv hane).mpr hargv, nofun⟩
      simp [entryLayout, strField, isVersion_toString _ hvfit, ha, entryValue]
    · simp [overlap, hlk, entryLayout, List.lookup, listOf]
    · simp [entryOf, tableOf, entryLayout, List.lookup, strOpt, listOf, strings_map, entryId,
        ModuleId.parse_toString, EntryVersion.parse_toString]

end FvdepAudit.Manifest.Proof
