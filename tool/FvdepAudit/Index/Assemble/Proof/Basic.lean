import FvdepAudit.Index.Assemble.Spec
import FvdepAudit.Index.Statuses.Proof.Claims

/-! The assembly helpers against the layout written apart: the toolchain trim, the key order's
laws + the sort, the validation facts the assembly reads (V1 canonical versions, V2 distinct
entries, V4 obligation shapes), the statuses' structure, each layout node. -/

namespace FvdepAudit.Index.Assemble.Proof

open Lean FvdepCore.Json FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses FvdepCore.Index.Assemble
open FvdepAudit.Doc.Spec FvdepAudit.Index.Spec FvdepAudit.Index.Rules.Spec
open FvdepAudit.Index.Statuses.Spec FvdepAudit.Index.Assemble.Spec
open FvdepAudit.Index.Statuses.Proof

/-! ## The toolchain trim -/

theorem trimText_trimmed (raw : String) : Trimmed raw (trimText raw) := by
  let ws := Char.isWhitespace
  let L := raw.toList
  let M := L.dropWhile ws
  have hL : L = L.takeWhile ws ++ M := List.takeWhile_append_dropWhile.symm
  have hM : M = (M.reverse.dropWhile ws).reverse ++ (M.reverse.takeWhile ws).reverse := by
    rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  have ht : (trimText raw).toList = (M.reverse.dropWhile ws).reverse := by simp [trimText, M, L, ws]
  refine ⟨L.takeWhile ws, (M.reverse.takeWhile ws).reverse, ?_, ?_, ?_, ?_⟩
  · rw [ht, List.append_assoc, ← hM]
    exact hL
  · intro c hc
    have := List.all_takeWhile (p := ws) (l := L)
    exact (List.all_eq_true.mp this) c hc
  · intro c hc
    rw [List.mem_reverse] at hc
    have := List.all_takeWhile (p := ws) (l := M.reverse)
    exact (List.all_eq_true.mp this) c hc
  · intro c hc
    rw [ht] at hc
    rcases hc with hc | hc
    · -- the head of the trimmed text = the head of `M`
      have hne : (M.reverse.dropWhile ws).reverse ≠ [] := by
        intro e
        rw [e] at hc
        simp at hc
      have hhead : M.head? = some c := by
        rw [hM]
        obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hne
        rw [hd] at hc ⊢
        simpa using hc
      have := List.head?_dropWhile_not ws L
      simp only [M] at hhead
      rw [hhead] at this
      exact this
    · rw [List.getLast?_reverse] at hc
      have := List.head?_dropWhile_not ws M.reverse
      rw [hc] at this
      exact this

theorem dropWhile_all {p : Char → Bool} :
    ∀ (xs : List Char), (∀ c ∈ xs, p c = true) → xs.dropWhile p = []
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.dropWhile_cons_of_pos (h x (List.mem_cons_self ..))]
    exact dropWhile_all xs fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem trimmed_eq {raw t : String} (h : Trimmed raw t) : t = trimText raw := by
  obtain ⟨pre, post, hraw, hpre, hpost, hends⟩ := h
  rw [← String.toList_inj]
  simp only [trimText, String.toList_ofList]
  rw [hraw]
  cases ht : t.toList with
  | nil =>
    rw [List.append_nil,
      dropWhile_all _ fun c hc => (List.mem_append.mp hc).elim (hpre c) (hpost c)]
    simp
  | cons c cs =>
    have hc : c.isWhitespace = false := hends c (.inl (by simp [ht]))
    rw [List.append_assoc, List.dropWhile_append_of_pos (fun c hc => hpre c hc), List.cons_append,
      List.dropWhile_cons_of_neg (by simp [hc]), ← List.cons_append, List.reverse_append,
      List.dropWhile_append_of_pos (fun d hd => hpost d (List.mem_reverse.mp hd))]
    cases hr : (c :: cs).reverse with
    | nil => simp at hr
    | cons d
      ds =>
      have hd : d.isWhitespace = false := by
        apply hends d (.inr _)
        rw [ht, ← List.head?_reverse, hr]
        rfl
      rw [List.dropWhile_cons_of_neg (by simp [hd]), ← hr, List.reverse_reverse]

theorem trimmed_unique {raw t t' : String} (h : Trimmed raw t) (h' : Trimmed raw t') : t = t' :=
  (trimmed_eq h).trans (trimmed_eq h').symm

/-! ## The key order + the sort -/

theorem cmp_ne_gt_iff (x y : EntryVersion) : ¬x.cmp y = .gt ↔ x.le y := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  have h1 := cmp3_spec a d
  have h2 := cmp3_spec b e
  have h3 := cmp3_spec c f
  unfold EntryVersion.cmp EntryVersion.le
  simp only
  cases ha : cmp3 a d <;> cases hb : cmp3 b e <;> cases hc : cmp3 c f <;> simp_all

theorem keyLe_iff (a b : String × EntryVersion) :
    keyLe a b = true ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2.le b.2 := by
  unfold keyLe
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    cmp_ne_gt_iff]

theorem keyLe_total (a b : String × EntryVersion) : (keyLe a b || keyLe b a) = true := by
  rw [Bool.or_eq_true, keyLe_iff, keyLe_iff]
  by_cases h₁ : a.1 < b.1
  · exact .inl (.inl h₁)
  · by_cases h₂ : b.1 < a.1
    · exact .inr (.inl h₂)
    · have e := str_eq_of_not_lt h₁ h₂
      rcases EntryVersion.le_total a.2 b.2 with h | h
      · exact .inl (.inr ⟨e, h⟩)
      · exact .inr (.inr ⟨e.symm, h⟩)

theorem keyLe_trans (a b c : String × EntryVersion) (h₁ : keyLe a b = true)
    (h₂ : keyLe b c = true) : keyLe a c = true := by
  rw [keyLe_iff] at *
  rcases h₁ with h₁ | ⟨e₁, l₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, l₂⟩
  · exact .inl (str_lt_trans h₁ h₂)
  · exact
      .inl
        (by
          rw [← e₂]; exact h₁)
  · exact
      .inl
        (by
          rw [e₁]; exact h₂)
  · exact .inr ⟨e₁.trans e₂, EntryVersion.le_trans _ _ _ l₁ l₂⟩

theorem sortOps_perm (rs : List (Entry × EntryStatus)) : (sortOps rs).Perm rs :=
  List.mergeSort_perm rs _

theorem sortOps_keyed (rs : List (Entry × EntryStatus)) :
    (sortOps rs).Pairwise fun a b => keyLe (opKey a.1) (opKey b.1) = true := by
  have htrans :
    ∀ a b c : Entry × EntryStatus,
      keyLe (opKey a.1) (opKey b.1) = true →
        keyLe (opKey b.1) (opKey c.1) = true → keyLe (opKey a.1) (opKey c.1) = true :=
    fun a b c => keyLe_trans (opKey a.1) (opKey b.1) (opKey c.1)
  have htotal :
    ∀ a b : Entry × EntryStatus,
      (keyLe (opKey a.1) (opKey b.1) || keyLe (opKey b.1) (opKey a.1)) = true :=
    fun a b => keyLe_total (opKey a.1) (opKey b.1)
  exact List.pairwise_mergeSort htrans htotal rs

theorem before_of_le_ne {x y : EntryVersion} (h : x.le y) (hne : x ≠ y) : VersionBefore x y := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  unfold EntryVersion.le at h
  unfold VersionBefore
  simp only [ne_eq, EntryVersion.mk.injEq] at hne h ⊢
  omega

/-- Canonical versions + distinct (id, version) strings: the key order is C6's strict order. -/
theorem before_of_keyLe {a b : Entry} (ha : EntryVersion.parse a.version ≠ none)
    (hb : EntryVersion.parse b.version ≠ none) (hne : (a.id, a.version) ≠ (b.id, b.version))
    (h : keyLe (opKey a) (opKey b) = true) : IdVersionBefore a.id a.version b.id b.version := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp ha
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hb
  rw [keyLe_iff] at h
  simp only [opKey, hx, hy, Option.getD_some] at h
  unfold IdVersionBefore
  rw [hx, hy]
  rcases h with h | ⟨e, hle⟩
  · exact .inl h
  · refine .inr ⟨e, before_of_le_ne hle fun exy => hne ?_⟩
    have h₁ := EntryVersion.toString_parse hx
    have h₂ := EntryVersion.toString_parse hy
    rw [exy] at h₁
    rw [e, ← h₁, h₂]

theorem before_asymm {ia va ib vb : String} (h : IdVersionBefore ia va ib vb) :
    ¬IdVersionBefore ib vb ia va := by
  unfold IdVersionBefore at *
  intro h'
  rcases h with h | ⟨e, hv⟩ <;> rcases h' with h' | ⟨e', hv'⟩
  · exact str_lt_asymm h h'
  · rw [e'] at h
    exact str_lt_irrefl _ h
  · rw [e] at h'
    exact str_lt_irrefl _ h'
  · cases hx : EntryVersion.parse va <;> cases hy : EntryVersion.parse vb <;>
      simp only [hx, hy] at hv hv'
    rename_i x y
    unfold VersionBefore at hv hv'
    omega

/-! ## Validation facts -/

theorem entryRows_at {F : Facts} {l : Lists} (hv : RegistryValid F l) {e : Entry} {i : Nat}
    (h : (e, i) ∈ l.entries.zipIdx) : ∀ r ∈ entryRows F l i e, r.1 := fun r hr =>
  hv r
    (List.mem_append_left _
      (List.mem_append_left _
        (List.mem_append_left _
          (List.mem_append_left _
            (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(e, i), h, hr⟩))))))

/-- V1: a listed entry's version is canonical. -/
theorem version_canonical {F : Facts} {l : Lists} (hv : RegistryValid F l) {e : Entry}
    (he : e ∈ l.entries) : EntryVersion.parse e.version ≠ none := by
  obtain ⟨i, h⟩ := entryRows_hold hv he
  exact
    h _
      (List.mem_append_left _
        (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- V4: each obligation of a listed entry is `S.<name>`. -/
theorem obligation_shape {F : Facts} {l : Lists} (hv : RegistryValid F l) {e : Entry}
    (he : e ∈ l.entries) : ∀ o ∈ e.obligations, ∃ name, o = .str (specModule e) name := by
  obtain ⟨i, h⟩ := entryRows_hold hv he
  have h4 := h _ (List.mem_append_right _ (List.mem_cons_self ..))
  intro o ho
  obtain ⟨_, hs, _⟩ := h4 o ho
  exact hs

/-- V2: no (id, version) is listed twice. -/
theorem entries_distinct {F : Facts} {l : Lists} (hv : RegistryValid F l) :
    (l.entries.map fun e => (e.id, e.version)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  have hmem : (l.entries[j], j) ∈ l.entries.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (by simp)
  have h2 :=
    entryRows_at hv hmem _
      (List.mem_append_left _
        (List.mem_append_left _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  have hin : l.entries[i] ∈ l.entries.take j := by
    rw [List.mem_iff_getElem]
    exact
      ⟨i, by
        simp; omega, by simp⟩
  simp only [Prod.mk.injEq] at heq
  exact h2 _ hin heq

/-! ## The statuses' structure -/

theorem zip_fst {α β : Type} :
    ∀ (es : List α) (rs : List (α × β)),
      es.length = rs.length → (∀ x ∈ es.zip rs, x.2.1 = x.1) → rs.map (·.1) = es
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | e :: es, r :: rs, hl, h => by
    have h₁ := h (e, r) (by simp)
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h₁, zip_fst es rs (by simpa using hl) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem statuses_fst {F : Facts} {ax : List (Name × List Name)} {l : Lists}
    {rs : List (Entry × EntryStatus)} (h : StatusesSpec F ax l rs) : rs.map (·.1) = l.entries :=
  zip_fst l.entries rs h.1 fun x hx => (h.2 x hx).1

theorem statuses_member {F : Facts} {ax : List (Name × List Name)} {l : Lists}
    {rs : List (Entry × EntryStatus)} (h : StatusesSpec F ax l rs) {x : Entry × EntryStatus}
    (hx : x ∈ rs) : x.1 ∈ l.entries ∧ EntrySpec F ax l x.1 x.2 := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hx
  have hn' : n < l.entries.length := by
    rw [h.1]; exact hn
  have hm : (l.entries[n], rs[n]) ∈ l.entries.zip rs := by
    rw [List.mem_iff_getElem]
    exact
      ⟨n, by
        simp; omega, by simp⟩
  obtain ⟨e₁, e₂⟩ := h.2 _ hm
  refine ⟨?_, ?_⟩
  · rw [e₁]
    exact List.getElem_mem hn'
  · rw [e₁]
    exact e₂

theorem entrySpec_names {F : Facts} {ax : List (Name × List Name)} {l : Lists} {e : Entry}
    {s : EntryStatus} (h : EntrySpec F ax l e s) : s.obligations.map (·.1) = e.obligations := by
  obtain ⟨_, _, rs, hl, _, hobl, _⟩ := h
  rw [hobl, List.map_map]
  exact List.map_fst_zip (by omega)

/-! ## Layout nodes -/

theorem statusText_eq (s : FvdepCore.Index.Status) : statusText s = s.text := by cases s <;> rfl

theorem names_eq (xs : List String) : NamesV xs = namesValue xs := rfl

theorem obligationV_iff {S : Name} {x : Name × FvdepCore.Index.Status × List String}
    (hx : ∃ name, x.1 = .str S name) (v : Value) : ObligationV S x v ↔ v = obligationValue x := by
  obtain ⟨name, hn⟩ := hx
  unfold ObligationV obligationValue
  constructor
  · rintro ⟨name', hn', rfl⟩
    rw [hn] at hn'
    simp only [Name.str.injEq, true_and] at hn'
    subst hn'
    simp [hn, lastName, statusText_eq, names_eq]
  · rintro rfl
    exact ⟨name, hn, by simp [hn, lastName, statusText_eq, names_eq]⟩

theorem compat_eq (c : Option (String × FvdepCore.Index.Status × List String)) :
    CompatV c = compatValue c := by cases c <;> simp [CompatV, compatValue, statusText_eq, names_eq]

theorem zip_map_self {α β : Type} (g : α → β) :
    ∀ (xs : List α), ∀ p ∈ xs.zip (xs.map g), p.1 ∈ xs ∧ p.2 = g p.1
  | [] => by simp
  | x :: xs => by
    intro p hp
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨List.mem_cons_self .., rfl⟩
    · obtain ⟨h₁, h₂⟩ := zip_map_self g xs p hp
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩

theorem operationV_iff (h : ByteArray → String) (F : Facts) (x : Entry × EntryStatus)
    (hx : ∀ o ∈ x.2.obligations.map (·.1), ∃ name, o = .str (specModule x.1) name) (v : Value) :
    OperationV h F x v ↔ v = operationValue h F x := by
  have hframe :
    FvdepCore.Hash.frame "fvdep/entry/1" (closureFiles F x.1.module) = entryFrame F x.1.module :=
    rfl
  unfold OperationV
  constructor
  · rintro ⟨obs, hl, hall, rfl⟩
    have hobs : obs = x.2.obligations.map obligationValue := by
      apply List.ext_getElem (by simp [hl])
      intro n h₁ h₂
      have hm : (x.2.obligations[n]'(by omega), obs[n]) ∈ x.2.obligations.zip obs := by
        rw [List.mem_iff_getElem]
        exact
          ⟨n, by
            simp; omega, by simp⟩
      have hs : ∃ name, (x.2.obligations[n]'(by omega)).1 = .str (specModule x.1) name :=
        hx _ (List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)
      have := (obligationV_iff hs _).mp (hall _ hm)
      simpa using this
    rw [hobs, hframe, compat_eq]
    rfl
  · rintro rfl
    refine ⟨x.2.obligations.map obligationValue, by simp, fun p hp => ?_, ?_⟩
    · obtain ⟨hp₁, hp₂⟩ := zip_map_self obligationValue x.2.obligations p hp
      rw [hp₂]
      exact (obligationV_iff (hx _ (List.mem_map.mpr ⟨_, hp₁, rfl⟩)) _).mpr rfl
    · rw [hframe, compat_eq]
      rfl

end FvdepAudit.Index.Assemble.Proof
