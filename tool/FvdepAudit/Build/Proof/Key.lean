import FvdepAudit.Build.Spec
import FvdepAudit.Json.Proof.Corollaries

/-! Proof of K1's key claim (contract `docs/contracts/U5-sandbox.md` K1; statement =
`FvdepLedger.Rows.BuildClaims.preimageInjective`): within the JSON profile's bounds, distinct key
inputs have distinct preimages, so two inputs share a key only through a SHA-256 collision. -/

namespace FvdepAudit.Build.Proof

open FvdepCore.Build FvdepAudit.Json.Spec FvdepAudit.Build.Spec
open FvdepCore.Json (Value)

/-! ## Validity of mapped lists -/

theorem stringsFitList_map {α : Type} (f : α → Value) :
    ∀ xs : List α, (∀ x ∈ xs, stringsFit (f x) = true) → stringsFitList (xs.map f) = true
  | [], _ => by simp [stringsFitList]
  | x :: xs, h => by
    simp only [List.map_cons, stringsFitList, Bool.and_eq_true]
    exact
      ⟨h x List.mem_cons_self, stringsFitList_map f xs fun y hy => h y (List.mem_cons_of_mem x hy)⟩

theorem intsFitList_map {α : Type} (f : α → Value) :
    ∀ xs : List α, (∀ x ∈ xs, intsFit (f x) = true) → intsFitList (xs.map f) = true
  | [], _ => by simp [intsFitList]
  | x :: xs, h => by
    simp only [List.map_cons, intsFitList, Bool.and_eq_true]
    exact ⟨h x List.mem_cons_self, intsFitList_map f xs fun y hy => h y (List.mem_cons_of_mem x hy)⟩

theorem keysAscendList_map {α : Type} (f : α → Value) :
    ∀ xs : List α, (∀ x ∈ xs, keysAscend (f x) = true) → keysAscendList (xs.map f) = true
  | [], _ => by simp [keysAscendList]
  | x :: xs, h => by
    simp only [List.map_cons, keysAscendList, Bool.and_eq_true]
    exact
      ⟨h x List.mem_cons_self, keysAscendList_map f xs fun y hy => h y (List.mem_cons_of_mem x hy)⟩

theorem depthList_map {α : Type} (f : α → Value) (c : Nat) :
    ∀ xs : List α, (∀ x ∈ xs, depth (f x) ≤ c) → depthList (xs.map f) ≤ c
  | [], _ => by simp [depthList]
  | x :: xs, h => by
    simp only [List.map_cons, depthList]
    exact
      Nat.max_le.mpr
        ⟨h x List.mem_cons_self, depthList_map f c xs fun y hy => h y (List.mem_cons_of_mem x hy)⟩

theorem importValue_ok (i : Import) (hs : i.module.utf8ByteSize ≤ maxStringBytes)
    (hk : i.key.utf8ByteSize ≤ maxStringBytes) :
    intsFit (importValue i) = true ∧
      stringsFit (importValue i) = true ∧
      depth (importValue i) ≤ 1 ∧ keysAscend (importValue i) = true := by
  have hs' : i.module.utf8ByteSize ≤ 65536 := hs
  have hk' : i.key.utf8ByteSize ≤ 65536 := hk
  simp [importValue, intsFit, intsFitMembers, stringsFit, stringsFitMembers, depth, depthMembers,
    keysAscend, keysAscendMembers, maxStringBytes, hs', hk']
  decide

theorem strs_ok (xs : List String) (h : ∀ x ∈ xs, x.utf8ByteSize ≤ maxStringBytes) :
    intsFitList (xs.map .str) = true ∧
      stringsFitList (xs.map .str) = true ∧
      depthList (xs.map .str) ≤ 0 ∧ keysAscendList (xs.map .str) = true :=
  ⟨intsFitList_map _ xs fun _ _ => by simp [intsFit],
    stringsFitList_map _ xs fun x hx => by simp [stringsFit, h x hx],
    depthList_map _ 0 xs fun _ _ => by simp [depth],
    keysAscendList_map _ xs fun _ _ => by simp [keysAscend]⟩

theorem pairs_ok (xs : List (String × String)) (h1 : ∀ x ∈ xs, x.1.utf8ByteSize ≤ maxStringBytes)
    (h2 : ∀ x ∈ xs, x.2.utf8ByteSize ≤ maxStringBytes) :
    intsFitList (xs.map fun e => .arr [.str e.1, .str e.2]) = true ∧
      stringsFitList (xs.map fun e => .arr [.str e.1, .str e.2]) = true ∧
      depthList (xs.map fun e => .arr [.str e.1, .str e.2]) ≤ 1 ∧
      keysAscendList (xs.map fun e => .arr [.str e.1, .str e.2]) = true :=
  ⟨intsFitList_map _ xs fun _ _ => by simp [intsFit, intsFitList],
    stringsFitList_map _ xs fun x hx => by simp [stringsFit, stringsFitList, h1 x hx, h2 x hx],
    depthList_map _ 1 xs fun _ _ => by simp [depth, depthList],
    keysAscendList_map _ xs fun _ _ => by simp [keysAscend, keysAscendList]⟩

theorem recipe_ok (r : Recipe) (hid : Fits r.id) (hrel : Fits r.release) (hfp : Fits r.fingerprint)
    (hargv : ∀ s ∈ r.argv, Fits s) (hlp : ∀ s ∈ r.leanPath, Fits s) (hopt : ∀ s ∈ r.options, Fits s)
    (henv : ∀ e ∈ r.env, Fits e.1 ∧ Fits e.2) (ht : r.threads ≤ maxInt) :
    intsFit (recipeValue r) = true ∧
      stringsFit (recipeValue r) = true ∧
      depth (recipeValue r) ≤ 3 ∧ keysAscend (recipeValue r) = true := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := strs_ok r.argv hargv
  obtain ⟨hl1, hl2, hl3, hl4⟩ := strs_ok r.leanPath hlp
  obtain ⟨ho1, ho2, ho3, ho4⟩ := strs_ok r.options hopt
  obtain ⟨he1, he2, he3, he4⟩ :=
    pairs_ok r.env (fun x hx => (henv x hx).1) (fun x hx => (henv x hx).2)
  simp only [Fits, maxStringBytes, maxInt] at hid hrel hfp ht ha2 hl2 ho2 he2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) [recipeValue, intsFit, intsFitMembers, maxInt, ha1, hl1,
      ho1, he1, ht]
  · simp (config := { decide := true }) [recipeValue, stringsFit, stringsFitMembers, maxStringBytes,
      ha2, hl2, ho2, he2, hid, hrel, hfp]
  · simp only [recipeValue, depth, depthMembers]
    omega
  · simp (config := { decide := true }) [recipeValue, keysAscend, keysAscendMembers, ha4, hl4, ho4,
      he4]

theorem keyValue_valid (k : KeyInput) (h : Bounded k) : Valid (keyValue k) := by
  obtain ⟨hstr, hargv, hlp, hopt, henv, himp, ht⟩ := h
  have hid := hstr k.recipe.id (by simp)
  have hrel := hstr k.recipe.release (by simp)
  have hfp := hstr k.recipe.fingerprint (by simp)
  have hmod := hstr k.module (by simp)
  have hpath := hstr k.path (by simp)
  have hsrc := hstr k.source (by simp)
  obtain ⟨hr1, hr2, hr3, hr4⟩ := recipe_ok k.recipe hid hrel hfp hargv hlp hopt henv ht
  have hi1 :=
    intsFitList_map importValue k.imports fun i hi =>
      (importValue_ok i (himp i hi).1 (himp i hi).2).1
  have hi2 :=
    stringsFitList_map importValue k.imports fun i hi =>
      (importValue_ok i (himp i hi).1 (himp i hi).2).2.1
  have hi3 :=
    depthList_map importValue 1 k.imports fun i hi =>
      (importValue_ok i (himp i hi).1 (himp i hi).2).2.2.1
  have hi4 :=
    keysAscendList_map importValue k.imports fun i hi =>
      (importValue_ok i (himp i hi).1 (himp i hi).2).2.2.2
  simp only [Fits, maxStringBytes] at hmod hpath hsrc
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) [keyValue, intsFit, intsFitMembers, hi1, hr1]
  · simp (config := { decide := true }) [keyValue, stringsFit, stringsFitMembers, maxStringBytes,
      hi2, hr2, hmod, hpath, hsrc]
  · simp only [keyValue, depth, depthMembers, maxDepth]
    omega
  · simp (config := { decide := true }) [keyValue, keysAscend, keysAscendMembers, hi4, hr4]

theorem map_inj {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ xs ys : List α, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf x y h.1, map_inj f hf xs ys h.2]

theorem keyValue_inj (a b : KeyInput) (h : keyValue a = keyValue b) : a = b := by
  have hstr : ∀ x y : String, Value.str x = Value.str y → x = y := fun _ _ h => by
    cases h; rfl
  have hpair :
    ∀ x y : String × String,
      (Value.arr [.str x.1, .str x.2] : Value) = .arr [.str y.1, .str y.2] → x = y := by
    intro x y h
    simp only [Value.arr.injEq, List.cons.injEq, Value.str.injEq, and_true] at h
    exact Prod.ext h.1 h.2
  have himp : ∀ x y : Import, importValue x = importValue y → x = y := by
    intro x y h
    simp only [importValue, Value.obj.injEq, List.cons.injEq, Prod.mk.injEq, Value.bool.injEq,
      Value.str.injEq, true_and, and_true] at h
    cases x; cases y; simp_all
  obtain ⟨ra, ma, pa, sa, ia⟩ := a
  obtain ⟨rb, mb, pb, sb, ib⟩ := b
  obtain ⟨ida, rela, fpa, argva, lpa, enva, opta, tha⟩ := ra
  obtain ⟨idb, relb, fpb, argvb, lpb, envb, optb, thb⟩ := rb
  simp only [keyValue, recipeValue, Value.obj.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.arr.injEq, Value.str.injEq, Value.int.injEq, true_and, and_true] at h
  obtain ⟨hi, hm, hp, ⟨hargv, henv, hfp, hid, hlp, hopt, hrel, hth⟩, hs⟩ := h
  have := map_inj _ himp ia ib hi
  have := map_inj _ hstr argva argvb hargv
  have := map_inj _ hpair enva envb henv
  have := map_inj _ hstr lpa lpb hlp
  have := map_inj _ hstr opta optb hopt
  simp_all [Int.ofNat_inj]

/-- K1: within the JSON profile's bounds, distinct key inputs have distinct preimages. -/
theorem preimage_injective (a b : KeyInput) (ha : Bounded a) (hb : Bounded b)
    (h : preimage a = preimage b) : a = b := by
  have hda := FvdepAudit.Json.Proof.print_decode (keyValue a) (keyValue_valid a ha)
  have hdb := FvdepAudit.Json.Proof.print_decode (keyValue b) (keyValue_valid b hb)
  unfold preimage at h
  rw [h, hdb] at hda
  exact keyValue_inj a b (Except.ok.inj hda).symm

end FvdepAudit.Build.Proof
