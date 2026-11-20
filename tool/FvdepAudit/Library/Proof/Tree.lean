import FvdepAudit.Library.Proof.Record

/-! Proofs: a whole `ls-tree -z -l` listing (contract `docs/contracts/U5b-oracle.md` L4):
`parseTree` accepts exactly the NUL-terminated layouts of well-formed entries, in order. -/

namespace FvdepAudit.Library.Proof

open FvdepCore.Library FvdepAudit.Library.Spec FvdepAudit.Hash.Spec

theorem drop_cons' (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.data.toList.drop i = b[i] :: b.data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  rfl

theorem nulEnd_eq (b : ByteArray) (i : Nat) (hi : i ≤ b.size) :
    nulEnd b i = i + ((b.data.toList.drop i).takeWhile (· != 0)).length := by
  unfold nulEnd
  split
  · rename_i h
    rw [drop_cons' b i h]
    split
    · rename_i hl
      have hl' : b[i] = 0 := by simpa using hl
      simp [hl']
    · rename_i hl
      have hl' : b[i] ≠ 0 := by simpa using hl
      rw [nulEnd_eq b (i + 1) h]
      simp [hl']
      omega
  · rename_i h
    have : i = b.size := by omega
    subst this
    simp [List.drop_eq_nil_of_le (show b.data.toList.length ≤ b.size by simp)]
termination_by b.size - i

theorem extract_eq' (b : ByteArray) (i e : Nat) :
    (b.extract i e).data.toList = (b.data.toList.drop i).take (e - i) := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

/-- The bytes from `i` = the segment before the first NUL, then (when one exists) the NUL and the
rest; no NUL ⇒ `nulEnd` = the end. -/
theorem nul_split (b : ByteArray) (i : Nat) (hi : i < b.size) :
    0 ∉ (b.extract i (nulEnd b i)).data.toList ∧
      (nulEnd b i < b.size →
        b.data.toList.drop i =
          (b.extract i (nulEnd b i)).data.toList ++ 0 :: b.data.toList.drop (nulEnd b i + 1)) ∧
      (¬nulEnd b i < b.size → 0 ∉ b.data.toList.drop i) := by
  have he := nulEnd_eq b i (Nat.le_of_lt hi)
  have hsplit :=
    List.takeWhile_append_dropWhile (p := fun x : UInt8 => x != 0) (l := b.data.toList.drop i)
  generalize hl : b.data.toList.drop i = l at hsplit he
  generalize hs : l.takeWhile (fun x : UInt8 => x != 0) = s at hsplit he
  generalize hr : l.dropWhile (fun x : UInt8 => x != 0) = r at hsplit
  have hseg : (b.extract i (nulEnd b i)).data.toList = s := by
    rw [extract_eq', he, Nat.add_sub_cancel_left, hl, ← hsplit]
    exact List.take_left' rfl
  have hno : 0 ∉ s := fun hm => by
    rw [← hs] at hm
    have := List.all_eq_true.1 (List.all_takeWhile (p := fun x : UInt8 => x != 0) (l := l)) _ hm
    simp at this
  have hrest : b.data.toList.drop (nulEnd b i) = r := by
    rw [he, ← List.drop_drop, hl, ← hsplit]
    exact List.drop_left' rfl
  refine ⟨hseg ▸ hno, fun hlt => ?_, fun hge => ?_⟩
  · cases r with
    | nil =>
      have : b.data.toList.drop (nulEnd b i) ≠ [] := by
        simp [List.drop_eq_nil_iff]
        exact hlt
      exact absurd hrest this
    | cons c
      rest =>
      have hc : c = 0 := by
        have h1 :=
          List.head_dropWhile_not (fun x : UInt8 => x != 0) (l := l)
            (by
              rw [hr]; exact List.cons_ne_nil _ _)
        simp only [hr, List.head_cons] at h1
        simpa using h1
      subst hc
      have hend : b.data.toList.drop (nulEnd b i + 1) = rest := by
        rw [← List.drop_drop, hrest]
        rfl
      rw [← hsplit, hseg, hend]
  · cases r with
    | nil =>
      rw [← hsplit, List.append_nil]
      exact hno
    | cons c
      rest =>
      have : b.data.toList.drop (nulEnd b i) ≠ [] := by
        rw [hrest]
        exact List.cons_ne_nil _ _
      simp [List.drop_eq_nil_iff] at this
      exact absurd this hge

/-- Two NUL-terminated first segments agree. -/
theorem nul_unique :
    ∀ {a c : List UInt8} {b d : List UInt8},
      0 ∉ a → 0 ∉ c → a ++ 0 :: b = c ++ 0 :: d → a = c ∧ b = d
  | [], [], _, _, _, _, h => by simpa using h
  | [], y :: ys, _, _, _, hc, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) hc
  | x :: xs, [], _, _, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) ha
  | x :: xs, y :: ys, _, _, ha, hc, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have :=
      nul_unique (fun m => ha (List.mem_cons_of_mem _ m)) (fun m => hc (List.mem_cons_of_mem _ m)) h
    exact ⟨by rw [this.1], this.2⟩

theorem record_no_nul (e : TreeEntry) (hw : EntryWF e) : 0 ∉ recordLayout e := by
  obtain ⟨-, hmo, -, hoh, -, -, hp0⟩ := hw
  have h1 : 0 ∉ e.mode := fun h => absurd (hmo 0 h).1 (by decide)
  have h2 : 0 ∉ kindName e.kind := by cases e.kind <;> simp [kindName, ascii_names]
  have h3 : 0 ∉ e.oid := fun h => by
    rcases hoh 0 h with h | h
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
  have h4 : 0 ∉ sizeColumn e.size := by
    rw [sizeColumn_eq]
    intro h
    simp only [pad7, List.mem_append, List.mem_replicate] at h
    rcases h with ⟨-, h⟩ | h
    · exact absurd h (by decide)
    · cases hs : e.size with
      | none =>
        rw [hs] at h
        simp [sizeText, ascii_names] at h
      | some n =>
        rw [hs, sizeText, decimalBytes_eq] at h
        have := digits_isDigit n 0 h
        simp [isDigitByte] at this
  simp [recordLayout, h1, h2, h3, h4, hp0]

theorem listing_cons (e : TreeEntry) (es : List TreeEntry) :
    listing (e :: es) = recordLayout e ++ 0 :: listing es := by simp [listing]

theorem listing_ne_nil {es : List TreeEntry} (h : es ≠ []) : listing es ≠ [] := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es => simp [listing_cons]

/-- `parseTreeFrom` from a record's start = the listing's layout from there. -/
theorem parseTreeFrom_exact (b : ByteArray) (i : Nat) (acc es : List TreeEntry) :
    parseTreeFrom b i acc = some es ↔
      ∃ es',
        es = acc.reverse ++ es' ∧ b.data.toList.drop i = listing es' ∧ ∀ e ∈ es', EntryWF e := by
  rw [parseTreeFrom]
  by_cases hi : i < b.size
  · have hle := le_nulEnd b i (Nat.le_of_lt hi)
    obtain ⟨hno, hsome, hnone⟩ := nul_split b i hi
    simp only [hi, ↓reduceDIte]
    by_cases he : nulEnd b i < b.size
    · simp only [he, ↓reduceIte]
      have hd := hsome he
      cases hr : parseRecord (b.extract i (nulEnd b i)).data.toList with
      | none =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨es', -, hl, hw⟩
        cases es' with
        | nil =>
          rw [hd] at hl
          simp [listing] at hl
        | cons x xs =>
          rw [hd, listing_cons] at hl
          have hu := nul_unique hno (record_no_nul x (hw x (by simp))) hl
          have := (parseRecord_exact _ x).2 ⟨hu.1, hw x (by simp)⟩
          rw [hr] at this
          cases this
      | some x =>
        simp only
        rw [parseTreeFrom_exact b (nulEnd b i + 1) (x :: acc) es]
        have hx := (parseRecord_exact _ x).1 hr
        constructor
        · rintro ⟨es', rfl, hl, hw⟩
          refine ⟨x :: es', by simp, ?_, ?_⟩
          · rw [hd, listing_cons, hx.1, hl]
          · intro e he'
            simp only [List.mem_cons] at he'
            rcases he' with rfl | he'
            · exact hx.2
            · exact hw e he'
        · rintro ⟨es', rfl, hl, hw⟩
          cases es' with
          | nil =>
            rw [hd] at hl
            simp [listing] at hl
          | cons y ys =>
            rw [hd, listing_cons] at hl
            have hu := nul_unique hno (record_no_nul y (hw y (by simp))) hl
            have hy := (parseRecord_exact _ y).2 ⟨hu.1, hw y (by simp)⟩
            rw [hr] at hy
            cases hy
            exact ⟨ys, by simp, hu.2, fun e he' => hw e (by simp [he'])⟩
    · simp only [he, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨es', -, hl, hw⟩
      have hne : es' ≠ [] := by
        rintro rfl
        have : b.data.toList.drop i ≠ [] := by
          simp [List.drop_eq_nil_iff]
          exact hi
        exact this (by simpa [listing] using hl)
      cases es' with
      | nil => exact hne rfl
      | cons x xs =>
        apply hnone he
        rw [hl, listing_cons]
        simp
  · simp only [hi, ↓reduceDIte, Option.some.injEq]
    have hd : b.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hi)
    rw [hd]
    constructor
    · rintro rfl
      exact ⟨[], by simp, by simp [listing], by simp⟩
    · rintro ⟨es', rfl, hl, -⟩
      cases es' with
      | nil => simp
      | cons x xs => exact absurd hl.symm (listing_ne_nil (by simp))
termination_by b.size - i

/-- L4: `parseTree` accepts exactly the listings of well-formed entries + returns them in order. -/
theorem parseTree_exact (b : ByteArray) (es : List TreeEntry) :
    parseTree b = some es ↔ b.data.toList = listing es ∧ ∀ e ∈ es, EntryWF e := by
  rw [parseTree, parseTreeFrom_exact]
  simp

end FvdepAudit.Library.Proof
