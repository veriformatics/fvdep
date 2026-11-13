import FvdepAudit.Manifest.Proof.Print

/-! T5 `PrintDenotes`: the printer's bytes are a document of T4's TOML 1.0 subset that denotes
`toTree m`. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

theorem char_eq {c : Char} {n : Nat} (h : c.toNat = n) (d : Char) (hd : d.toNat = n) : c = d := by
  apply Char.ext
  apply UInt32.toNat_inj.mp
  simp only [Char.toNat] at h hd
  omega

theorem hexDig_hexDigitU : ∀ n : Fin 16, HexDig (hexDigitU n.val) n.val := by
  unfold HexDig
  decide

theorem hexDig_zero : HexDig '0' 0 := by
  unfold HexDig
  decide

/-- Each T4 escape is a `basic-char` denoting its scalar. -/
theorem escSpec_basic (c : Char) : BasicChar (escSpec c) c := by
  unfold escSpec
  split
  · rename_i h
    exact Or.inr (char_eq h '"' rfl ▸ Escaped.quote)
  · rename_i h
    exact Or.inr (char_eq h '\\' rfl ▸ Escaped.backslash)
  · rename_i h
    exact Or.inr (char_eq h '\x08' rfl ▸ Escaped.backspace)
  · rename_i h
    exact Or.inr (char_eq h '\t' rfl ▸ Escaped.tab)
  · rename_i h
    exact Or.inr (char_eq h '\n' rfl ▸ Escaped.lineFeed)
  · rename_i h
    exact Or.inr (char_eq h '\x0c' rfl ▸ Escaped.formFeed)
  · rename_i h
    exact Or.inr (char_eq h '\r' rfl ▸ Escaped.carriageReturn)
  · rename_i n h1 h2 h3 h4 h5 h6 h7
    split
    · rename_i hc
      have hlt : c.toNat < 128 := by omega
      exact
        Or.inr
          (Escaped.u4 (va := 0) (vb := 0) hexDig_zero hexDig_zero
            (hexDig_hexDigitU ⟨c.toNat / 16, by omega⟩) (hexDig_hexDigitU ⟨c.toNat % 16, by omega⟩)
            (by
              simp; omega))
    · rename_i hc
      refine Or.inl ⟨rfl, ?_⟩
      have hlo : 32 ≤ c.toNat := Nat.le_of_not_lt fun h => hc (Or.inl h)
      have hne : c.toNat ≠ 127 := fun h => hc (Or.inr h)
      have hq : c.toNat ≠ 34 := h1
      have hb : c.toNat ≠ 92 := h2
      unfold BasicUnescaped
      rcases Nat.lt_or_ge c.toNat 128 with hlt | hge
      · by_cases e32 : c.toNat = 32
        · exact Or.inl e32
        by_cases e33 : c.toNat = 33
        · exact Or.inr (Or.inr (Or.inl e33))
        by_cases h91 : c.toNat ≤ 91
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h91⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hge))))

theorem quoted_basic (s : String) : BasicString (quoted s) s := by
  refine ⟨s.toList.map escSpec, by simp [quoted, List.flatMap_def], ?_⟩
  induction s.toList with
  | nil => exact Forall2.nil
  | cons c cs ih => exact Forall2.cons (escSpec_basic c) ih

theorem quoted_parts (xs : List String) : Forall2 BasicString (xs.map quoted) xs := by
  induction xs with
  | nil => exact Forall2.nil
  | cons x xs ih => exact Forall2.cons (quoted_basic x) ih

theorem unquoted_of {k : String} (hne : k.toList ≠ [])
    (h : ∀ c ∈ k.toList, Letter c ∨ Digit c ∨ c = '-' ∨ c = '_') : UnquotedKey k.toList k :=
  ⟨hne, rfl, h⟩

theorem keyval_str {k : String} (hk : UnquotedKey k.toList k) (s : String) :
    KeyvalLine (lineSpec k (quoted s)) (k, .str s) :=
  ⟨k.toList, quoted s, by simp [lineSpec], Or.inl hk, Or.inl ⟨s, rfl, quoted_basic s⟩⟩

theorem keyval_arr {k : String} (hk : UnquotedKey k.toList k) (xs : List String) :
    KeyvalLine (lineSpec k (arraySpecText xs)) (k, .arr (xs.map .str)) :=
  ⟨k.toList, arraySpecText xs, by simp [lineSpec], Or.inl hk,
    Or.inr (Or.inr ⟨xs, rfl, xs.map quoted, rfl, quoted_parts xs⟩)⟩

/-- The sections the canonical print holds: `[library]`, `[policy]`, then one per entry. -/
def secsOf (m : ManifestFile) : List (List String × List (String × Tree)) :=
  [(["library"], [("commit", .str (toString m.library))]),
      (["policy"], [("proof", .str (policyText m.policy))])] ++
    m.modules.map fun e => (["modules", entryId e], entryMembers e)

/-- Their texts. -/
def secTextsOf (m : ManifestFile) : List (List Char) :=
  ["\n[library]\ncommit = ".toList ++ quoted (toString m.library) ++ "\n".toList,
      "\n[policy]\nproof = ".toList ++ quoted (policyWord m.policy) ++ "\n".toList] ++
    m.modules.map fun e =>
      "\n[modules.".toList ++ quoted (entryId e) ++ "]\n".toList ++ entryLines e

theorem text_split (m : ManifestFile) :
    canonicalText m = "schema = 1\n".toList ++ (secTextsOf m).flatten := by
  simp [canonicalText, secTextsOf, List.flatMap_def]

theorem keyvals_entry {e : Entry} (hw : EntryWF e) : Keyvals (entryLines e) (entryMembers e) := by
  obtain ⟨⟨module, version, shape, kind, impl, proof, adapter⟩, im, pm⟩ := e
  obtain ⟨_, _, hk⟩ := hw
  cases kind with
  | proof =>
    obtain ⟨hsh, ⟨i, rfl, _⟩, ⟨x, rfl, _⟩, rfl, _, _, _⟩ := hk
    obtain ⟨sh, rfl⟩ := Option.ne_none_iff_exists'.mp hsh
    refine
      ⟨[lineSpec "version" (quoted (toString version)), lineSpec "shape" (quoted (shapeText sh)),
          lineSpec "impl_modules" (arraySpecText im), lineSpec "proof_modules" (arraySpecText pm),
          lineSpec "impl" (quoted i), lineSpec "proof" (quoted x)],
        ?_, ?_⟩
    · cases sh <;> simp [entryLines, shapeWord, shapeText]
    · simp only [entryMembers]
      refine Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) ?_
      refine Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) ?_
      refine Forall2.cons (keyval_arr (unquoted_of (by simp) (by simp [Letter])) _) ?_
      refine Forall2.cons (keyval_arr (unquoted_of (by simp) (by simp [Letter])) _) ?_
      refine Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) ?_
      exact Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) Forall2.nil
  | differential =>
    obtain ⟨rfl, rfl, rfl, ⟨argv, rfl, _⟩, rfl, rfl⟩ := hk
    refine
      ⟨[lineSpec "version" (quoted (toString version)), lineSpec "evidence" (quoted "differential"),
          lineSpec "adapter" (arraySpecText argv)],
        by simp [entryLines], ?_⟩
    simp only [entryMembers]
    refine Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) ?_
    refine Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) ?_
    exact Forall2.cons (keyval_arr (unquoted_of (by simp) (by simp [Letter])) _) Forall2.nil

theorem sections_of {m : ManifestFile} (hw : WellFormed m) :
    Forall2 SectionText (secTextsOf m) (secsOf m) := by
  obtain ⟨lib, pol, mods⟩ := m
  obtain ⟨hwe, -⟩ := hw
  simp only at hwe
  simp only [secTextsOf, secsOf, List.cons_append, List.nil_append]
  refine
    Forall2.cons
      ⟨"[library]\n".toList, lineSpec "commit" (quoted (toString lib)), by simp [lineSpec],
        Or.inl
          ⟨"library".toList, "library", rfl, by simp,
            Or.inl (unquoted_of (by simp) (by simp [Letter]))⟩,
        [lineSpec "commit" (quoted (toString lib))], by simp,
        Forall2.cons (keyval_str (unquoted_of (by simp) (by simp [Letter])) _) Forall2.nil⟩
      ?_
  refine
    Forall2.cons
      ⟨"[policy]\n".toList, lineSpec "proof" (quoted (policyWord pol)), by simp [lineSpec],
        Or.inl
          ⟨"policy".toList, "policy", rfl, by simp,
            Or.inl (unquoted_of (by simp) (by simp [Letter]))⟩,
        [lineSpec "proof" (quoted (policyWord pol))], by simp,
        Forall2.cons
          (by
            rw [policyText_eq]; exact keyval_str (unquoted_of (by simp) (by simp [Letter])) _)
          Forall2.nil⟩
      ?_
  induction mods with
  | nil => exact Forall2.nil
  | cons e es ih =>
    refine
      Forall2.cons
        ⟨'[' :: "modules".toList ++ '.' :: quoted (entryId e) ++ [']', '\n'], entryLines e, by simp,
          Or.inr
            ⟨"modules".toList, quoted (entryId e), "modules", entryId e, rfl, rfl,
              Or.inl (unquoted_of (by simp) (by simp [Letter])), Or.inr (quoted_basic _)⟩,
          keyvals_entry (hwe e (by simp))⟩
        (ih fun x hx => hwe x (by simp [hx]))

theorem docWF_of {m : ManifestFile} (hw : WellFormed m) :
    DocWF [("schema", .int 1)] (secsOf m) := by
  obtain ⟨lib, pol, mods⟩ := m
  obtain ⟨hwe, hasc⟩ := hw
  simp only at hwe hasc
  have hids := nodup_of_lt hasc
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro sec hsec
    simp only [secsOf, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hsec
    rcases hsec with rfl | rfl | ⟨e, he, rfl⟩
    · simp
    · simp
    · exact
        ⟨((entryMembers_perm (hwe e he)).map (·.1)).nodup_iff.mpr (entryLayout_keys_nodup e),
          Or.inr rfl⟩
  · have hmods :
      (mods.map fun e => (["modules", entryId e], entryMembers e)).map (·.1) =
        (mods.map entryId).map fun i => ["modules", i] := by
      simp [List.map_map, Function.comp_def]
    simp only [secsOf, List.cons_append, List.nil_append, List.map_cons, hmods, List.nodup_cons,
      List.mem_cons, List.mem_map]
    refine ⟨by simp, by simp, ?_⟩
    exact List.Pairwise.map _ (fun a b hab h => hab (by simpa using h)) hids
  · intro sec hsec a ha
    simp only [secsOf, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hsec
    rcases hsec with rfl | rfl | ⟨e, _, rfl⟩
    · simp only [List.cons.injEq, and_true] at ha
      subst ha
      refine ⟨by simp, fun sec' hsec' b hb => ?_⟩
      simp only [secsOf, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hsec'
      rcases hsec' with rfl | rfl | ⟨e', _, rfl⟩ <;> simp_all
    · simp only [List.cons.injEq, and_true] at ha
      subst ha
      refine ⟨by simp, fun sec' hsec' b hb => ?_⟩
      simp only [secsOf, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hsec'
      rcases hsec' with rfl | rfl | ⟨e', _, rfl⟩ <;> simp_all
    · simp at ha
  · intro sec hsec a b hab
    simp only [secsOf, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hsec
    rcases hsec with rfl | rfl | ⟨e, _, rfl⟩
    · simp at hab
    · simp at hab
    · simp only [List.cons.injEq, and_true] at hab
      rw [← hab.1]
      simp

/-- The member one `[modules."<id>"]` section adds. -/
def pairOf (e : Entry) : String × Tree := (entryId e, .tbl (entryMembers e))

theorem denote_modules (base : List (String × Tree)) (hb : "modules" ∉ base.map (·.1)) :
    ∀ (acc : List (String × Tree)) (es : List Entry),
      denote (base ++ [("modules", .tbl acc)])
          (es.map fun e => (["modules", entryId e], entryMembers e)) =
        base ++ [("modules", .tbl (acc ++ es.map pairOf))]
  | acc, [] => by simp [denote]
  | acc, e :: es => by
    have hl : (base ++ [("modules", Tree.tbl acc)]).lookup "modules" = some (.tbl acc) := by
      rw [List.lookup_append, lookup_none_iff.mpr hb]
      simp
    have hmap :
      (base ++ [("modules", Tree.tbl acc)]).map
          (fun m =>
            if m.1 = "modules" then
              ("modules", Tree.tbl (acc ++ [(entryId e, .tbl (entryMembers e))]))
            else m) =
        base ++ [("modules", .tbl (acc ++ [pairOf e]))] := by
      have hbase :
        base.map
            (fun m =>
              if m.1 = "modules" then
                ("modules", Tree.tbl (acc ++ [(entryId e, .tbl (entryMembers e))]))
              else m) =
          base := by
        have h :=
          List.map_congr_left (l := base) (g := id) (f := fun m =>
            if m.1 = "modules" then
              ("modules", Tree.tbl (acc ++ [(entryId e, .tbl (entryMembers e))]))
            else m)
            fun m hm => by
            have : m.1 ≠ "modules" := fun h => hb (List.mem_map.mpr ⟨m, hm, h⟩)
            simp [this]
        rw [h, List.map_id]
      rw [List.map_append, hbase]
      simp [pairOf]
    simp only [List.map_cons, denote, hl, hmap]
    rw [denote_modules base hb (acc ++ [pairOf e]) es]
    simp

theorem denote_secs (m : ManifestFile) :
    denote [("schema", .int 1)] (secsOf m) =
      [("schema", .int 1), ("library", .tbl [("commit", .str (toString m.library))]),
          ("policy", .tbl [("proof", .str (policyText m.policy))])] ++
        if m.modules.isEmpty then []
        else
          [("modules",
              .tbl (m.modules.map fun e => (toString e.decl.module, .tbl (entryMembers e))))] := by
  obtain ⟨lib, pol, mods⟩ := m
  simp only [secsOf, List.cons_append, List.nil_append, denote, List.cons_append]
  cases mods with
  | nil => simp [denote]
  | cons e
    es =>
    have hb :
      "modules" ∉
        ([("schema", Tree.int 1), ("library", .tbl [("commit", .str (toString lib))]),
                ("policy", .tbl [("proof", .str (policyText pol))])] :
              List (String × Tree)).map
          (·.1) := by
      simp
    simp only [List.map_cons, denote, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    have hl :
      ([("schema", Tree.int 1), ("library", .tbl [("commit", .str (toString lib))]),
                ("policy", .tbl [("proof", .str (policyText pol))])] :
              List (String × Tree)).lookup
          "modules" =
        none :=
      lookup_none_iff.mpr hb
    simp only [hl]
    have := denote_modules _ hb [(entryId e, .tbl (entryMembers e))] es
    rw [this]
    simp [pairOf, entryId]

/-- T5 `PrintDenotes`. -/
theorem print_denotes (m : ManifestFile) (hw : WellFormed m) :
    TomlText (printManifest m).data.toList (toTree m) := by
  refine
    ⟨"schema = 1\n".toList, [("schema", .int 1)], secTextsOf m, secsOf m, ?_, ?_, sections_of hw,
      docWF_of hw, ?_⟩
  · rw [print_exact m hw, canonicalManifest, text_split]
  · refine ⟨["schema = 1\n".toList], by simp, Forall2.cons ?_ Forall2.nil⟩
    refine
      ⟨"schema".toList, "1".toList, by simp, Or.inl (unquoted_of (by simp) (by simp [Letter])),
        Or.inr (Or.inl ⟨1, rfl, ?_⟩)⟩
    simp [DecInt, Digit]
  · rw [denote_secs]
    rfl

end FvdepAudit.Manifest.Proof
