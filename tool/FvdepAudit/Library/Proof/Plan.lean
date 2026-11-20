import FvdepAudit.Library.Proof.Tables

/-! Proofs: the tree policy (contract `docs/contracts/U5b-oracle.md` L4, L10 `planTreeExact`):
`planTree` accepts exactly the listings the policy allows + plans their blobs in listing order. -/

namespace FvdepAudit.Library.Proof

open FvdepCore.Library FvdepAudit.Library.Spec

theorem dots : ".".toList.head? = some '.' ∧ "..".toList.head? = some '.' := by decide

theorem plain_iff (c : String) :
    ((c != "" && c != "." && c != "..") && plainComponent c) = true ↔
      c ≠ "" ∧ c.toList.head? ≠ some '.' := by
  unfold plainComponent
  constructor
  · intro h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨h.2.1, h.2.2⟩
  · rintro ⟨h1, h2⟩
    have h3 : c ≠ "." := fun e => h2 (e ▸ dots.1)
    have h4 : c ≠ ".." := fun e => h2 (e ▸ dots.2)
    simp [h1, h2, h3, h4]

theorem pathOk_iff (caps : Caps) (p : String) : pathOk caps p = true ↔ PathOk caps p := by
  unfold pathOk PathOk components FvdepCore.Step.safePath
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := h
    refine
      ⟨by simpa using h1, by simpa [String.contains] using h2, fun c hc => (plain_iff c).1 ?_, h5,
        h6⟩
    simp only [Bool.and_eq_true]
    exact
      ⟨by simpa only [Bool.and_eq_true] using List.all_eq_true.1 h3 c hc,
        List.all_eq_true.1 h4 c hc⟩
  · rintro ⟨h1, h2, h3, h5, h6⟩
    have hp := fun c hc => (plain_iff c).2 (h3 c hc)
    simp only [Bool.and_eq_true] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact
      ⟨⟨⟨⟨by simpa using h1, by simpa [String.contains] using h2⟩,
            List.all_eq_true.2 fun c hc => by simpa only [Bool.and_eq_true] using (hp c hc).1⟩,
          List.all_eq_true.2 fun c hc => (hp c hc).2⟩,
        h5, h6⟩

theorem modes :
    modeTree = ascii "040000" ∧ modeFile = ascii "100644" ∧ modeExec = ascii "100755" := by decide

theorem roots : rootDirs = rootDirsSpec ∧ rootFiles = rootFilesSpec ∧ required = requiredSpec :=
  ⟨rfl, rfl, rfl⟩

theorem isDir_iff (e : TreeEntry) : isDir e = true ↔ IsDir e := by simp [isDir, IsDir, modes.1]

theorem isFile_iff (e : TreeEntry) : isFile e = true ↔ IsFile e := by
  simp [isFile, IsFile, modes.2.1, modes.2.2]

theorem placed_iff (e : TreeEntry) : placed e = true ↔ Placed e := by
  have hd := isDir_iff e
  have hf := isFile_iff e
  unfold placed Placed components
  cases h : e.path.splitOn "/" with
  | nil => simp
  | cons r t =>
    cases t with
    | nil =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, roots.1, roots.2.1, hd,
        hf]
    | cons y ys =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, roots.1, hd, hf]

/-- An entry's own check = the spec's path + placement. -/
theorem entryRefusal_none (caps : Caps) (e : TreeEntry) :
    entryRefusal caps e = none ↔ PathOk caps e.path ∧ Placed e := by
  unfold entryRefusal
  by_cases h1 : pathOk caps e.path = true
  · have hp := (pathOk_iff _ _).1 h1
    by_cases h2 : placed e = true
    · simp [h1, h2, hp, (placed_iff _).1 h2]
    · have hn : ¬Placed e := fun h => h2 ((placed_iff _).2 h)
      simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hn, and_false, iff_false]
      split
      · simp
      · split
        · simp
        · split <;> simp
  · have hn : ¬PathOk caps e.path := fun h => h1 ((pathOk_iff _ _).2 h)
    simp [h1, hn]

theorem blobSize_eq (e : TreeEntry) :
    (if (e.kind == .blob) = true then e.size.getD 0 else 0) = blobSize e := by simp [blobSize]

/-- `planFrom`'s running caps = the totals over the rest of the listing. -/
theorem planFrom_ok (caps : Caps) :
    ∀ (es : List TreeEntry) (n paths total : Nat) (acc bs : List Blob),
      n ≤ caps.entries →
        paths ≤ caps.pathTotal →
        total ≤ caps.totalBytes →
        (planFrom caps n paths total acc es = .ok bs ↔
          (∀ e ∈ es, PathOk caps e.path ∧ Placed e ∧ blobSize e ≤ caps.fileBytes) ∧
            n + es.length ≤ caps.entries ∧
            paths + (es.map fun e => e.path.utf8ByteSize).sum ≤ caps.pathTotal ∧
            total + (es.map blobSize).sum ≤ caps.totalBytes ∧ bs = acc.reverse ++ blobsOf es)
  | [], n, paths, total, acc, bs, hn, hp, ht => by
    simp only [planFrom, Except.ok.injEq, List.not_mem_nil, false_implies, implies_true,
      List.length_nil, Nat.add_zero, List.map_nil, List.sum_nil, true_and, blobsOf,
      List.filterMap_nil, List.append_nil]
    constructor
    · rintro rfl
      exact ⟨hn, hp, ht, rfl⟩
    · rintro ⟨-, -, -, rfl⟩
      rfl
  | e :: es, n, paths, total, acc, bs, hn, hp, ht => by
    have hr := entryRefusal_none caps e
    simp only [planFrom]
    cases he : entryRefusal caps e with
    | some why =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨hall, -⟩
      have := hr.2 ⟨(hall e (by simp)).1, (hall e (by simp)).2.1⟩
      rw [he] at this
      cases this
    | none =>
      have hpl := hr.1 he
      simp only [blobSize_eq]
      by_cases h1 : caps.entries < n + 1 ∨ caps.pathTotal < paths + e.path.utf8ByteSize
      · have h1' :
          (decide (caps.entries < n + 1) || decide (caps.pathTotal < paths + e.path.utf8ByteSize)) =
            true := by
          simpa using h1
        simp only [h1', ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨-, h2, h3, -⟩
        simp only [List.length_cons, List.map_cons, List.sum_cons] at h2 h3
        omega
      · have h1' :
          (decide (caps.entries < n + 1) || decide (caps.pathTotal < paths + e.path.utf8ByteSize)) =
            false := by
          simpa using h1
        simp only [h1', Bool.false_eq_true, ↓reduceIte]
        by_cases h2 :
          (e.kind == .blob &&
              (decide (caps.fileBytes < blobSize e) ||
                decide (caps.totalBytes < total + blobSize e))) =
            true
        · simp only [h2, ↓reduceIte, reduceCtorEq, false_iff]
          rintro ⟨hall, -, -, h4, -⟩
          have hfb := (hall e (by simp)).2.2
          simp only [List.map_cons, List.sum_cons] at h4
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h2
          omega
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          have hfile : blobSize e ≤ caps.fileBytes ∧ total + blobSize e ≤ caps.totalBytes := by
            by_cases hb : e.kind = .blob
            · simp only [hb, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq,
                not_or, Nat.not_lt] at h2
              exact h2
            · simp only [blobSize, hb, ↓reduceIte]
              omega
          rw [planFrom_ok caps es (n + 1) (paths + e.path.utf8ByteSize) (total + blobSize e) _ bs
              (by omega) (by omega) hfile.2]
          have hacc :
            (if (e.kind == .blob) = true then (⟨e.path, e.oid, blobSize e⟩ :: acc)
                  else acc).reverse ++
                blobsOf es =
              acc.reverse ++ blobsOf (e :: es) := by
            by_cases hb : e.kind = .blob
            · simp [hb, blobsOf, blobSize]
            · simp [hb, blobsOf]
          rw [hacc]
          simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.map_cons,
            List.sum_cons]
          constructor
          · rintro ⟨hall, h3, h4, h5, rfl⟩
            exact ⟨⟨⟨hpl.1, hpl.2, hfile.1⟩, hall⟩, by omega, by omega, by omega, rfl⟩
          · rintro ⟨⟨-, hall⟩, h3, h4, h5, rfl⟩
            exact ⟨hall, by omega, by omega, by omega, rfl⟩

theorem blobsOf_any (p : String) :
    ∀ es : List TreeEntry,
      (blobsOf es).any (fun x => x.path == p) = true ↔ ∃ e ∈ es, e.kind = .blob ∧ e.path = p
  | [] => by simp [blobsOf]
  | e :: es => by
    have ih := blobsOf_any p es
    by_cases hb : e.kind = .blob
    · have he : blobsOf (e :: es) = ⟨e.path, e.oid, e.size.getD 0⟩ :: blobsOf es := by
        simp [blobsOf, hb]
      rw [he, List.any_cons, Bool.or_eq_true, ih]
      simp [hb]
    · have he : blobsOf (e :: es) = blobsOf es := by simp [blobsOf, hb]
      rw [he, ih]
      simp [hb]

/-- L4: `planTree` accepts exactly the listings the policy allows; its plan = their blobs in
listing order. -/
theorem planTree_exact (caps : Caps) (es : List TreeEntry) (bs : List Blob) :
    planTree caps es = .ok bs ↔ Policy caps es ∧ bs = blobsOf es := by
  unfold planTree Policy
  cases hp : planFrom caps 0 0 0 [] es with
  | error
    e =>
    have hf := planFrom_ok caps es 0 0 0 [] bs (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    simp only [Nat.zero_add, List.reverse_nil, List.nil_append] at hf
    rw [hp] at hf
    simp only [bind, Except.bind, reduceCtorEq, false_iff]
    rintro ⟨⟨h1, h2, h3, h4, -⟩, h5⟩
    exact absurd (hf.2 ⟨h1, h2, h3, h4, h5⟩) (by simp)
  | ok
    blobs =>
    have hf := planFrom_ok caps es 0 0 0 [] blobs (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    simp only [Nat.zero_add, List.reverse_nil, List.nil_append] at hf
    rw [hp] at hf
    obtain ⟨h1, h2, h3, h4, rfl⟩ := hf.1 rfl
    simp only [bind, Except.bind]
    have hreq :
      (required.find? fun p => !(blobsOf es).any (·.path == p)) = none ↔
        ∀ p ∈ requiredSpec, ∃ e ∈ es, e.kind = .blob ∧ e.path = p := by
      rw [List.find?_eq_none, roots.2.2]
      apply forall_congr'
      intro p
      apply imp_congr_right
      intro _
      rw [← blobsOf_any p es]
      simp
    cases hq : required.find? fun p => !(blobsOf es).any (·.path == p) with
    | some p =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨⟨-, -, -, -, h5⟩, -⟩
      rw [hreq.2 h5] at hq
      cases hq
    | none =>
      simp only [Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨⟨h1, h2, h3, h4, hreq.1 hq⟩, rfl⟩
      · rintro ⟨-, rfl⟩
        rfl

end FvdepAudit.Library.Proof
