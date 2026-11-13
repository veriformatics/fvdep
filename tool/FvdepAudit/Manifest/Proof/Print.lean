import FvdepAudit.Manifest.Proof.Roundtrip

/-! T5 `PrintExact`: the printer's bytes = T4's canonical layout, written apart. -/

namespace FvdepAudit.Manifest.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

theorem hexUpper_eq : ∀ n : Fin 16, hexUpper n.val = hexDigitU n.val := by decide

theorem escapeChar_eq (c : Char) : escapeChar c = escSpec c := by
  unfold escapeChar escSpec
  split <;> split <;> simp_all
  exact ⟨hexUpper_eq ⟨c.toNat / 16, by omega⟩, hexUpper_eq ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩⟩

theorem basic_toList (s : String) : (basic s).toList = quoted s := by
  have : escapeChar = escSpec := funext escapeChar_eq
  simp [basic, quoted, this]

theorem toList_join (l : List String) : (String.join l).toList = (l.map String.toList).flatten := by
  induction l with
  | nil => simp
  | cons s l ih => simp [String.join_cons, ih]

theorem tomlValue_str (s : String) : (tomlValue (.str s)).toList = quoted s := by
  simp [tomlValue, basic_toList]

theorem tomlValue_strs (xs : List String) :
    (tomlValue (.arr (xs.map .str))).toList = arraySpecText xs := by
  simp only [tomlValue, List.map_map, arraySpecText, String.toList_append,
    String.toList_intercalate]
  simp [Function.comp_def, basic_toList]

theorem line_text (k : String) (v : Tree) :
    (k ++ " = " ++ tomlValue v ++ "\n").toList =
      k.toList ++ " = ".toList ++ (tomlValue v).toList ++ ['\n'] := by
  simp

theorem entryLines_eq {e : Entry} (hw : EntryWF e) :
    (membersText (entryMembers e)).toList = entryLines e := by
  obtain ⟨⟨module, version, shape, kind, impl, proof, adapter⟩, im, pm⟩ := e
  obtain ⟨_, _, hk⟩ := hw
  cases kind with
  | proof =>
    obtain ⟨hsh, ⟨i, rfl, _⟩, ⟨x, rfl, _⟩, rfl, _, _, _⟩ := hk
    obtain ⟨sh, rfl⟩ := Option.ne_none_iff_exists'.mp hsh
    cases sh <;>
      simp [membersText, entryMembers, entryLines, lineSpec, tomlValue_str, tomlValue_strs,
        shapeText, shapeWord]
  | differential =>
    obtain ⟨rfl, rfl, rfl, ⟨argv, rfl, _⟩, rfl, rfl⟩ := hk
    simp [membersText, entryMembers, entryLines, lineSpec, tomlValue_str, tomlValue_strs]

theorem printText_eq {m : ManifestFile} (hw : WellFormed m) :
    (printText m).toList = canonicalText m := by
  obtain ⟨lib, pol, mods⟩ := m
  obtain ⟨hwe, _⟩ := hw
  simp only at hwe
  have hm :
    ∀ e ∈ mods,
      ("\n[modules." ++ basic (toString e.decl.module) ++ "]\n" ++
            membersText (entryMembers e)).toList =
        "\n[modules.".toList ++ quoted (entryId e) ++ "]\n".toList ++ entryLines e := by
    intro e he
    rw [String.toList_append, String.toList_append, String.toList_append, basic_toList,
      entryLines_eq (hwe e he)]
    rfl
  have hm' :
    (mods.map
          (String.toList ∘ fun e =>
            "\n[modules." ++ basic (toString e.decl.module) ++ "]\n" ++
              membersText (entryMembers e))).flatten =
      mods.flatMap fun e =>
        "\n[modules.".toList ++ quoted (entryId e) ++ "]\n".toList ++ entryLines e := by
    rw [List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun e he => hm e he)
  unfold printText canonicalText
  dsimp only
  rw [String.toList_append, toList_join, List.map_map, hm']
  simp only [String.toList_append, basic_toList, policyText_eq, List.append_assoc]

/-- T5 `PrintExact`. -/
theorem print_exact (m : ManifestFile) (hw : WellFormed m) :
    (printManifest m).data.toList = canonicalManifest m := by
  rw [printManifest, canonicalManifest, ← printText_eq hw, String.ofList_toList]

end FvdepAudit.Manifest.Proof
