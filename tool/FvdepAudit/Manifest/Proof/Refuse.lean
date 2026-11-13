import FvdepAudit.Manifest.Proof.Accept

/-! T5 `ValidateExact` (refusal): the shipped early-exit check reports the first of the spec's
violations, for every tree. -/

namespace FvdepAudit.Manifest.Proof

open Classical
open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepCore.Manifest FvdepAudit.Manifest.Spec FvdepAudit.Doc.Spec

theorem strField_eq {ok : String → Bool} {rule : String → Prop} (h : ∀ s, ok s = true ↔ rule s)
    (p : List PathSeg) (v : Tree) : strField ok p v = (strSpec rule p v).head? := by
  cases v with
  | str s =>
    by_cases hs : rule s
    · simp [strField, strSpec, hs, (h s).mpr hs]
    · have : ok s = false := Bool.eq_false_iff.mpr fun hk => hs ((h s).mp hk)
      simp [strField, strSpec, hs, this]
  | _ => rfl

theorem elemsCheck_eq {ok : Nat → String → Bool} {rule : Nat → String → Prop}
    (h : ∀ i s, ok i s = true ↔ rule i s) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Tree), elemsCheck ok p i xs = (elemsSpec rule p i xs).head?
  | _, [] => rfl
  | i, x :: xs => by
    cases x with
    | str s =>
      by_cases hs : rule i s
      · simp only [elemsCheck, (h i s).mpr hs, ite_true, elemsSpec, hs, List.nil_append]
        exact elemsCheck_eq h p (i + 1) xs
      · have : ok i s = false := Bool.eq_false_iff.mpr fun hk => hs ((h i s).mp hk)
        simp [elemsCheck, elemsSpec, hs, this]
    | _ => rfl

/-- The code's repeat scan over the string payloads = the spec's scan over the elements, when every
element is a string (`seen` ↔ `seenT`: the earlier elements). -/
theorem repeats_eq (p : List PathSeg) :
    ∀ (seen : List String) (seenT : List Tree) (i : Nat) (xs : List Tree),
      (∀ s, Tree.str s ∈ seenT ↔ s ∈ seen) →
        (∀ x ∈ xs, ∃ s, x = .str s) →
        (firstRepeatIndex seen i (strings xs)).map
            (fun j => (⟨p ++ [.index j], .badValue⟩ : ManifestError)) =
          (repeatsSpec p seenT i xs).head?
  | _, _, _, [], _, _ => rfl
  | seen, seenT, i, x :: xs, hs, hx => by
    obtain ⟨s, rfl⟩ := hx x (by simp)
    have hrest : ∀ y ∈ xs, ∃ t, y = .str t := fun y hy => hx y (by simp [hy])
    have hstr : strings (.str s :: xs) = s :: strings xs := by simp [strings]
    rw [hstr]
    by_cases hm : s ∈ seen
    · have hm' : Tree.str s ∈ seenT := (hs s).mpr hm
      simp [firstRepeatIndex, repeatsSpec, hm, hm']
    · have hm' : Tree.str s ∉ seenT := fun h => hm ((hs s).mp h)
      have hc : seen.contains s = false := by simpa using hm
      simp only [firstRepeatIndex, hc, Bool.false_eq_true, ite_false, repeatsSpec, hm', ite_false,
        List.nil_append]
      have hs' : ∀ t, Tree.str t ∈ seenT ++ [.str s] ↔ t ∈ s :: seen := by
        intro t
        simp only [List.mem_append, List.mem_cons, Tree.str.injEq, List.not_mem_nil, or_false, hs]
        exact Or.comm
      exact repeats_eq p (s :: seen) (seenT ++ [.str s]) (i + 1) xs hs' hrest

theorem arrayCheck_eq {ok : Nat → String → Bool} {rule : Nat → String → Prop}
    (h : ∀ i s, ok i s = true ↔ rule i s) (unique : Bool) (p : List PathSeg) (v : Tree) :
    arrayCheck ok unique p v = (arraySpec rule unique p v).head? := by
  cases v with
  | arr xs =>
    cases xs with
    | nil => rfl
    | cons x
      xs =>
      simp only [arrayCheck, List.isEmpty_cons, Bool.false_eq_true, ite_false, arraySpec, orElse_eq,
        head?_append']
      rw [elemsCheck_eq h p 0]
      cases he : (elemsSpec rule p 0 (x :: xs)).head? with
      | some e => rfl
      | none =>
        cases unique with
        | false => rfl
        | true =>
          simp only [ite_true, Option.none_or]
          have hall : ∀ y ∈ x :: xs, ∃ s, y = .str s := by
            have hn : elemsCheck ok p 0 (x :: xs) = none := by rw [elemsCheck_eq h p 0, he]
            obtain ⟨ss, hss, _⟩ := elemsCheck_none_iff.mp hn
            intro y hy
            rw [hss] at hy
            obtain ⟨s, _, rfl⟩ := List.mem_map.mp hy
            exact ⟨s, rfl⟩
          exact repeats_eq p [] [] 0 (x :: xs) (by simp) hall
  | _ => rfl

theorem firstKey_unknown (known : List String) (p : List PathSeg) (ms : List (String × Tree)) :
    firstKey (!known.contains ·) .unknownField p (byKey ms) =
      (unknownMembers known p ms).head? := by
  rw [firstKey_eq, byKey_eq_sorted]
  unfold unknownMembers
  congr 3

theorem firstKey_forbidden (forbidden : List String) (p : List PathSeg)
    (ms : List (String × Tree)) :
    firstKey forbidden.contains .forbiddenField p (byKey ms) =
      (forbiddenSpec forbidden p ms).head? := by
  rw [firstKey_eq, byKey_eq_sorted]
  unfold forbiddenSpec
  congr 3

theorem missingKey_eq {ms : List (String × Tree)} (hd : (ms.map (·.1)).Nodup) (p : List PathSeg)
    (req : List String) : missingKey (byKey ms) p req = (missingMembers req p ms).head? := by
  rw [firstMissing_eq]
  unfold missingMembers
  congr 3
  funext k
  rw [lookup_perm hd (byKey_perm ms) k]

theorem tableCheck_eq {ok : String → Bool} {rule : String → Prop} (h : ∀ s, ok s = true ↔ rule s)
    (key : String) (required : Bool) (p : List PathSeg) (v : Tree) :
    tableCheck key required ok p v = (plainSpec key required rule p v).head? := by
  cases v with
  | tbl ms =>
    simp only [tableCheck, plainSpec]
    rw [← repeatedKey_dup p ms]
    cases hr : repeatedKey ms with
    | some k => rfl
    | none =>
      have hd := (repeatedKey_none_iff ms).mp hr
      simp only [Option.map_none, orElse_eq, head?_append']
      have hu :
        firstKey (· != key) .unknownField p (byKey ms) = (unknownMembers [key] p ms).head? := by
        rw [← firstKey_unknown]
        congr 1
        funext k
        rw [Bool.eq_iff_iff]
        simp [bne]
      rw [hu, missingKey_eq hd,
        valuesCheck_eq _ (fun m => if m.1 = key then strSpec rule (p ++ [.key m.1]) m.2 else [])]
      · rw [byKey_eq_sorted]
        simp only [Option.or_assoc]
      · intro m _
        by_cases hk : m.1 = key
        · simp [hk, strField_eq h]
        · simp [hk]
  | _ => rfl

theorem entryKind_eq (p : List PathSeg) (fs : List (String × Tree)) :
    entryKind p fs = evidenceSpec p fs := by
  unfold entryKind evidenceSpec
  cases fs.lookup "evidence" with
  | none => rfl
  | some w =>
    cases w with
    | str s => by_cases hs : s = "differential" <;> simp [hs]
    | _ => rfl

theorem entryValue_eq (p : List PathSeg) (k : String) (v : Tree) :
    entryValue p k v = (entryValueSpec p k v).head? := by
  by_cases h1 : k = "adapter"
  · subst h1
    rw [entryValue_adapter]
    simp only [entryValueSpec, ite_true]
    exact
      arrayCheck_eq
        (fun i s => by
          rw [show (i == 0) = decide (i = 0) by cases i <;> rfl]
          exact FvdepAudit.Doc.Proof.isArg_iff _ s)
        _ _ _
  by_cases h2 : k = "impl"
  · subst h2
    rw [entryValue_impl]
    simp only [entryValueSpec]
    simp [strField_eq isConstName_iff]
  by_cases h3 : k = "proof"
  · subst h3
    rw [entryValue_proof]
    simp only [entryValueSpec]
    simp [strField_eq isConstName_iff]
  by_cases h4 : k = "impl_modules"
  · subst h4
    rw [entryValue_implModules]
    simp only [entryValueSpec]
    simp [arrayCheck_eq (fun _ s => isModuleName_iff s)]
  by_cases h5 : k = "proof_modules"
  · subst h5
    rw [entryValue_proofModules]
    simp only [entryValueSpec]
    simp [arrayCheck_eq (fun _ s => isModuleName_iff s)]
  by_cases h6 : k = "shape"
  · subst h6
    rw [entryValue_shape]
    simp only [entryValueSpec]
    have hsh : ∀ s, isShape s = true ↔ (s = "fn" ∨ s = "abi") := fun s => by simp [isShape]
    simp [strField_eq hsh]
  by_cases h7 : k = "version"
  · subst h7
    rw [entryValue_version]
    simp only [entryValueSpec]
    simp [strField_eq isVersion_iff]
  have : entryValue p k v = none := by
    unfold entryValue
    split <;> simp_all
  rw [this]
  simp [entryValueSpec, h1, h2, h3, h4, h5, h6, h7]

theorem overlap_eq (p : List PathSeg) (fs : List (String × Tree)) :
    overlap p fs = (overlapSpec p fs).head? := by
  have hl : ∀ o : Option Tree, listOf o = stringsSpec o := by
    intro o
    rcases o with _ | (_ | _ | _ | xs | _ | _) <;> rfl
  simp only [overlap, overlapSpec, hl, List.head?_map, List.head?_filter]
  congr 2

theorem entryCheck_eq (p : List PathSeg) (v : Tree) : entryCheck p v = (entrySpec p v).head? := by
  cases v with
  | tbl fs =>
    simp only [entryCheck, entrySpec]
    rw [← repeatedKey_dup p fs]
    cases hr : repeatedKey fs with
    | some k => rfl
    | none =>
      have hd := (repeatedKey_none_iff fs).mp hr
      simp only [Option.map_none]
      rw [entryKind_eq]
      cases evidenceSpec p fs with
      | error e => rfl
      | ok kind =>
        simp only [orElse_eq, head?_append']
        have hk : entryKeys = entryKeySet := rfl
        have hf : forbiddenKeys kind = forbiddenFor kind := by cases kind <;> rfl
        have hq : requiredKeys kind = requiredFor kind := by cases kind <;> rfl
        rw [hk, hf, hq, firstKey_unknown, firstKey_forbidden, missingKey_eq hd,
          valuesCheck_eq (entryValue p) (fun m => entryValueSpec p m.1 m.2) _
            (fun m _ => entryValue_eq p m.1 m.2),
          byKey_eq_sorted, overlap_eq]
        simp only [Option.or_assoc]
  | _ => rfl

theorem modulesCheck_eq (p : List PathSeg) (v : Tree) :
    modulesCheck p v = (modulesSpec p v).head? := by
  cases v with
  | tbl es =>
    simp only [modulesCheck, modulesSpec]
    rw [← repeatedKey_dup p es]
    cases repeatedKey es with
    | some k => rfl
    | none =>
      simp only [Option.map_none]
      rw [valuesCheck_eq _
          (fun m =>
            if IdText m.1 then entrySpec (p ++ [.key m.1]) m.2 else [⟨p ++ [.key m.1], .badValue⟩]),
        byKey_eq_sorted]
      intro m _
      by_cases hi : IdText m.1
      · simp [hi, (isModuleId_iff m.1).mpr hi, entryCheck_eq]
      · have : isModuleId m.1 = false := Bool.eq_false_iff.mpr fun h => hi ((isModuleId_iff _).mp h)
        simp [hi, this]
  | _ => rfl

theorem rootValue_eq (k : String) (v : Tree) : rootValue k v = (rootValueSpec k v).head? := by
  by_cases h1 : k = "library"
  · subst h1
    rw [rootValue_library]
    simp only [rootValueSpec, ite_true]
    exact tableCheck_eq isCommit_iff _ _ _ _
  by_cases h2 : k = "modules"
  · subst h2
    rw [rootValue_modules]
    simp only [rootValueSpec]
    simp [modulesCheck_eq]
  by_cases h3 : k = "policy"
  · subst h3
    rw [rootValue_policy]
    simp only [rootValueSpec]
    have hpo : ∀ s, isPolicy s = true ↔ (s = "required" ∨ s = "development") := fun s => by
      simp [isPolicy]
    simp [tableCheck_eq hpo]
  have : rootValue k v = none := by
    unfold rootValue
    split <;> simp_all
  rw [this]
  simp [rootValueSpec, h1, h2, h3]

/-- T5 `ValidateExact` (refusal): the check = the first of the spec's violations. -/
theorem check_eq (t : Tree) : check t = FvdepAudit.Manifest.Spec.firstViolation t := by
  unfold FvdepAudit.Manifest.Spec.firstViolation
  cases t with
  | tbl ms =>
    simp only [check, allViolations]
    rw [← repeatedKey_dup [] ms]
    cases hr : repeatedKey ms with
    | some k => rfl
    | none =>
      have hd := (repeatedKey_none_iff ms).mp hr
      simp only [Option.map_none]
      cases ms.lookup "schema" with
      | none => rfl
      | some w =>
        cases w with
        | int n =>
          by_cases hn : n = 1
          · subst hn
            simp only [beq_self_eq_true, ite_true, orElse_eq, head?_append']
            have hk : rootKeys = ["library", "modules", "policy", "schema"] := rfl
            rw [hk, firstKey_unknown, missingKey_eq hd,
              valuesCheck_eq rootValue (fun m => rootValueSpec m.1 m.2) _
                (fun m _ => rootValue_eq m.1 m.2),
              byKey_eq_sorted]
            simp only [Option.or_assoc]
          · have : (n == 1) = false := by simpa using hn
            simp [this, hn]
        | _ => rfl
  | _ => rfl

theorem validate_error (t : Tree) (e : ManifestError) :
    validate t = .error e ↔ FvdepAudit.Manifest.Spec.firstViolation t = some e := by
  rw [← check_eq]
  unfold validate
  cases check t <;> simp

end FvdepAudit.Manifest.Proof
