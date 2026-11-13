import FvdepAudit.Json.Proof.Decode.Post

/-! J3's duplicate-key site: the decoder's pre-order walk (`dupSite`) names exactly the spec's
`FvdepAudit.Json.Spec.site`. -/

namespace FvdepAudit.Json.Proof

open FvdepCore.Json

/-! ## One object: the first repeat of the sorted keys = the least repeated key -/

private theorem sorted_keys (xs : List String) : (xs.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
  suffices h : (xs.mergeSort (· ≤ ·)).Pairwise (fun a b => decide (a ≤ b) = true) by simpa using h
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simpa using Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
  · intro a b
    simpa using (Std.le_total (a := a) (b := b))

/-- In an ascending list, a head unequal to its successor occurs nowhere after it. -/
private theorem head_not_mem {a b : String} {rest : List String}
    (hs : (a :: b :: rest).Pairwise (· ≤ ·)) (hne : a ≠ b) : a ∉ b :: rest := by
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hne he
  · have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
    have hba : b ≤ a := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 a hm
    exact hne (Std.le_antisymm hab hba)

/-- No repeat found in an ascending list ⇒ every key occurs at most once. -/
theorem firstRepeat_none {l : List String} (hs : l.Pairwise (· ≤ ·)) (h : firstRepeat l = none) :
    ∀ x, l.count x ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil =>
      intro x
      rw [List.count_cons]
      split <;> simp
    | cons b
      rest =>
      have hne : a ≠ b := by
        intro he
        simp [firstRepeat, he] at h
      have h' : firstRepeat (b :: rest) = none := by simpa [firstRepeat, hne] using h
      have ih := ih (List.pairwise_cons.mp hs).2 h'
      intro x
      rw [List.count_cons]
      by_cases hx : a = x
      · subst hx
        have h0 := List.count_eq_zero.mpr (head_not_mem hs hne)
        simp [h0]
      · have hb : (a == x) = false := by simpa using hx
        simp [hb, ih x]

/-- A repeat found in an ascending list occurs twice + lies at or below every key occurring
twice. -/
theorem firstRepeat_some {l : List String} (hs : l.Pairwise (· ≤ ·)) {k : String}
    (h : firstRepeat l = some k) : 2 ≤ l.count k ∧ ∀ x, 2 ≤ l.count x → k ≤ x := by
  induction l with
  | nil => simp [firstRepeat] at h
  | cons a l ih =>
    cases l with
    | nil => simp [firstRepeat] at h
    | cons b rest =>
      by_cases hab : a = b
      · subst hab
        have hk : a = k := by simpa [firstRepeat] using h
        subst hk
        have hhead : ∀ y ∈ a :: rest, a ≤ y := (List.pairwise_cons.mp hs).1
        refine ⟨by simp, fun x hx => ?_⟩
        have hm : x ∈ a :: a :: rest := List.count_pos_iff.mp (by omega)
        rcases List.mem_cons.mp hm with he | hm
        · exact he ▸ hhead a (by simp)
        · exact hhead x hm
      · have h' : firstRepeat (b :: rest) = some k := by simpa [firstRepeat, hab] using h
        rcases ih (List.pairwise_cons.mp hs).2 h' with ⟨h2, hmin⟩
        refine ⟨?_, fun x hx => hmin x ?_⟩
        · rw [List.count_cons]
          omega
        · by_cases hxa : a = x
          · subst hxa
            have h0 := List.count_eq_zero.mpr (head_not_mem hs hab)
            rw [List.count_cons, h0] at hx
            simp at hx
          · have hb : (a == x) = false := by simpa using hxa
            rw [List.count_cons] at hx
            simpa [hb] using hx

theorem least_mem (a : String) (ks : List String) : FvdepAudit.Json.Spec.least a ks ∈ a :: ks := by
  induction ks generalizing a with
  | nil => simp [FvdepAudit.Json.Spec.least]
  | cons k ks ih =>
    by_cases hk : k < a
    · have hm := ih k
      simp only [FvdepAudit.Json.Spec.least, hk, ↓reduceIte]
      exact List.mem_cons_of_mem a hm
    · have hm := ih a
      simp only [FvdepAudit.Json.Spec.least, hk, ↓reduceIte]
      rcases List.mem_cons.mp hm with he | hm
      · rw [he]
        simp
      · exact List.mem_cons_of_mem a (List.mem_cons_of_mem k hm)

theorem least_le (a : String) (ks : List String) :
    ∀ x ∈ a :: ks, FvdepAudit.Json.Spec.least a ks ≤ x := by
  induction ks generalizing a with
  | nil =>
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact (Std.le_total (a := x) (b := x)).elim id id
  | cons k ks ih =>
    intro x hx
    by_cases hk : k < a
    · simp only [FvdepAudit.Json.Spec.least, hk, ↓reduceIte]
      rcases List.mem_cons.mp hx with he | hm
      · subst he
        exact Std.le_trans (ih k k (by simp)) (show k ≤ x from String.lt_asymm hk)
      · exact ih k x hm
    · simp only [FvdepAudit.Json.Spec.least, hk, ↓reduceIte]
      rcases List.mem_cons.mp hx with he | hm
      · subst he
        exact ih x x (by simp)
      · rcases List.mem_cons.mp hm with he | hm
        · subst he
          exact Std.le_trans (ih a a (by simp)) (String.not_lt.mp hk)
        · exact ih a x (List.mem_cons_of_mem a hm)

/-- The decoder's per-object report = the spec's least repeated key. -/
theorem firstRepeat_sort (ms : List (String × Value)) :
    firstRepeat ((ms.map (·.1)).mergeSort (· ≤ ·)) =
      match FvdepAudit.Json.Spec.repeatedKeys ms with
      | k :: ks => some (FvdepAudit.Json.Spec.least k ks)
      | [] => none := by
  have hs := sorted_keys (ms.map (·.1))
  have hp := List.mergeSort_perm (ms.map (·.1)) (fun a b => decide (a ≤ b))
  have hmem : ∀ x, x ∈ FvdepAudit.Json.Spec.repeatedKeys ms ↔ 2 ≤ (ms.map (·.1)).count x := by
    intro x
    simp only [FvdepAudit.Json.Spec.repeatedKeys, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨List.count_pos_iff.mp (by omega), h⟩
  cases h : firstRepeat ((ms.map (·.1)).mergeSort (· ≤ ·)) with
  | none =>
    have hle := firstRepeat_none hs h
    have hnil : FvdepAudit.Json.Spec.repeatedKeys ms = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have h2 := (hmem x).mp hx
      have h1 := hle x
      rw [hp.count_eq] at h1
      omega
    rw [hnil]
  | some k =>
    rcases firstRepeat_some hs h with ⟨h2, hmin⟩
    rw [hp.count_eq] at h2
    have hk : k ∈ FvdepAudit.Json.Spec.repeatedKeys ms := (hmem k).mpr h2
    cases hr : FvdepAudit.Json.Spec.repeatedKeys ms with
    | nil =>
      rw [hr] at hk
      simp at hk
    | cons k' ks =>
      rw [hr] at hk
      have hl := least_mem k' ks
      rw [← hr] at hl
      simp only [Option.some.injEq]
      apply Std.le_antisymm
      · apply hmin
        rw [hp.count_eq]
        exact (hmem _).mp hl
      · exact least_le k' ks k hk

/-! ## The walk -/

/-- One object's report as the decoder computes it, its path prefixed by `rp` reversed. -/
def report (rp : List PathSeg) (o : List PathSeg × List (String × Value)) :
    Option (List PathSeg × String) :=
  (firstRepeat ((o.2.map (·.1)).mergeSort (· ≤ ·))).map fun k => (rp.reverse ++ o.1, k)

mutual
theorem dupSite_walk (rp : List PathSeg) (v : Value) :
    dupSite rp v = (FvdepAudit.Json.Spec.objects v).findSome? (report rp) := by
  cases v with
  | arr xs =>
    rw [dupSite, FvdepAudit.Json.Spec.objects]
    exact dupSiteList_walk rp 0 xs
  | obj ms =>
    rw [dupSite, FvdepAudit.Json.Spec.objects, List.findSome?_cons]
    simp only [report, List.append_nil]
    cases firstRepeat ((ms.map (·.1)).mergeSort (· ≤ ·)) with
    | some k => rfl
    | none => exact dupSiteMembers_walk rp ms
  | null => rfl
  | bool _ => rfl
  | int _ => rfl
  | str _ => rfl
theorem dupSiteList_walk (rp : List PathSeg) (i : Nat) (xs : List Value) :
    dupSiteList rp i xs = (FvdepAudit.Json.Spec.objectsList i xs).findSome? (report rp) := by
  cases xs with
  | nil => rfl
  | cons v
    vs =>
    have hf : (report rp ∘ fun o => (PathSeg.index i :: o.1, o.2)) = report (.index i :: rp) := by
      funext o
      simp [report, List.reverse_cons, List.append_assoc]
    rw [dupSiteList, FvdepAudit.Json.Spec.objectsList, List.findSome?_append, List.findSome?_map,
      hf, ← dupSite_walk (.index i :: rp) v, ← dupSiteList_walk rp (i + 1) vs]
    cases dupSite (.index i :: rp) v <;> rfl
theorem dupSiteMembers_walk (rp : List PathSeg) (ms : List (String × Value)) :
    dupSiteMembers rp ms = (FvdepAudit.Json.Spec.objectsMembers ms).findSome? (report rp) := by
  cases ms with
  | nil => rfl
  | cons p ms =>
    rcases p with ⟨k, v⟩
    have hf : (report rp ∘ fun o => (PathSeg.key k :: o.1, o.2)) = report (.key k :: rp) := by
      funext o
      simp [report, List.reverse_cons, List.append_assoc]
    rw [dupSiteMembers, FvdepAudit.Json.Spec.objectsMembers, List.findSome?_append,
      List.findSome?_map, hf, ← dupSite_walk (.key k :: rp) v, ← dupSiteMembers_walk rp ms]
    cases dupSite (.key k :: rp) v <;> rfl
end

theorem findSome?_find? {α β : Type} (f : α → Option β) (p : α → Bool) (h : ∀ a, (f a).isSome = p a)
    (l : List α) : l.findSome? f = (l.find? p).bind f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases hf : f a with
    | some
      b =>
      have hp : p a = true := by
        rw [← h a, hf]; rfl
      simp [hp, hf]
    | none =>
      have hp : p a = false := by
        rw [← h a, hf]; rfl
      simp [hp, ih]

theorem report_nil (o : List PathSeg × List (String × Value)) :
    report [] o =
      match FvdepAudit.Json.Spec.repeatedKeys o.2 with
      | k :: ks => some (o.1, FvdepAudit.Json.Spec.least k ks)
      | [] => none := by
  rw [report, firstRepeat_sort]
  cases FvdepAudit.Json.Spec.repeatedKeys o.2 <;> simp

/-- The decoder's site = the spec's, on every value (`([], "")` when no object repeats a key). -/
theorem dupSite_site (v : Value) : (dupSite [] v).getD ([], "") = FvdepAudit.Json.Spec.site v := by
  have hP : ∀ o, (report [] o).isSome = !(FvdepAudit.Json.Spec.repeatedKeys o.2).isEmpty := by
    intro o
    rw [report_nil]
    cases FvdepAudit.Json.Spec.repeatedKeys o.2 <;> rfl
  rw [dupSite_walk, findSome?_find? _ _ hP, FvdepAudit.Json.Spec.site]
  cases hf :
    (FvdepAudit.Json.Spec.objects v).find?
      (fun o => !(FvdepAudit.Json.Spec.repeatedKeys o.2).isEmpty) with
  | none => rfl
  | some o =>
    have hp := List.find?_some hf
    show
      (report [] o).getD ([], "") =
        (match FvdepAudit.Json.Spec.repeatedKeys o.2 with
        | k :: ks => (o.1, FvdepAudit.Json.Spec.least k ks)
        | [] => (o.1, ""))
    rw [report_nil]
    cases hr : FvdepAudit.Json.Spec.repeatedKeys o.2 with
    | nil => simp [hr] at hp
    | cons k ks => rfl

end FvdepAudit.Json.Proof
