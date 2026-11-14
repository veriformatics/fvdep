import FvdepAudit.Index.Proof.Nodes
import FvdepAudit.Index.Proof.Valid
import FvdepAudit.Json.Proof.Corollaries

/-! `index.json` (contract U4 C6 + C8): extraction inverts the layout, the relational check = its
written-apart violation list, and the document + byte claims. -/

namespace FvdepAudit.Index.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepCore.Index
open FvdepAudit.Doc.Spec FvdepAudit.Doc.Proof FvdepAudit.Index.Spec
open FvdepAudit.Json.Spec (keysAscend keysAscendMembers keysAscendList)

/-! ## Extraction inverts the layout (every record, no premise) -/

theorem strsAt_names (xs : List String) : strsAt (some (namesLayout xs)) = xs := by
  simp [strsAt, namesLayout, strsOf_map]

theorem statusOf_text (s : Status) : statusOf (statusText s) = s := by cases s <;> rfl

theorem map_extract {α : Type} (lay : α → Value) (ext : Value → α) (h : ∀ x, ext (lay x) = x) :
    ∀ xs : List α, (xs.map lay).map ext = xs
  | [] => rfl
  | x :: xs => by simp [h, map_extract lay ext h xs]

theorem obligation_extract (o : Obligation) : obligationOfValue (obligationLayout o) = o := by
  rcases o with ⟨n, s, axs⟩
  simp [obligationOfValue, obligationLayout, membersOf, member?, textOf, statusOf_text,
    strsAt_names]

theorem compat_extract (c : Option Compat) : compatOfValue (some (compatLayout c)) = c := by
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨x, s, axs⟩
    simp [compatOfValue, compatLayout, member?, textOf, versionAt, EntryVersion.parse_toString,
      statusOf_text, strsAt_names]

theorem operation_extract (o : Operation) : operationOfValue (operationLayout o) = o := by
  rcases o with ⟨m, x, d, obs, c⟩
  simp [operationOfValue, operationLayout, membersOf, member?, textOf, moduleAt, versionAt,
    ModuleId.parse_toString, EntryVersion.parse_toString,
    map_extract obligationLayout obligationOfValue obligation_extract, compat_extract]

theorem notice_extract (n : Notice) : noticeOfValue (noticeLayout n) = n := by
  rcases n with ⟨m, x, r, rep⟩
  cases rep <;>
    simp [noticeOfValue, noticeLayout, replacementLayout, membersOf, member?, textOf, textOpt,
      moduleAt, versionAt, ModuleId.parse_toString, EntryVersion.parse_toString]

theorem removed_extract (r : Removed) : removedOfValue (removedLayout r) = r := by
  rcases r with ⟨m, x, d, c, t⟩
  simp [removedOfValue, removedLayout, membersOf, member?, textOf, moduleAt, versionAt,
    ModuleId.parse_toString, EntryVersion.parse_toString, Commit.parse_toString]

theorem index_extract (i : IndexFile) : indexOfValue (indexLayout i) = i := by
  rcases i with ⟨tc, ops, ns, rs⟩
  simp [indexOfValue, indexLayout, membersOf, member?, textOf, arrAt,
    map_extract operationLayout operationOfValue operation_extract,
    map_extract noticeLayout noticeOfValue notice_extract,
    map_extract removedLayout removedOfValue removed_extract]

theorem layout_injective {i i' : IndexFile} (h : indexLayout i = indexLayout i') : i = i' := by
  rw [← index_extract i, h, index_extract]

/-! ## The relational clauses -/

theorem mem_known (i : IndexFile) (m : ModuleId) (v : EntryVersion) :
    (m, v) ∈ known i ↔ Listed i m v := by
  simp only [known, List.mem_append, List.mem_map, Prod.mk.injEq, Listed]

theorem noticeOk_iff (i : IndexFile) (n : Notice) : noticeOk i n = true ↔ NoticeRel i n := by
  rcases n with ⟨m, x, r, rep⟩
  cases rep <;> simp [noticeOk, NoticeRel, mem_known]

theorem removedOk_iff (i : IndexFile) (earlier : List Removed) (r : Removed) :
    removedOk i earlier r = true ↔ RemovedRel i earlier r := by
  simp [removedOk, RemovedRel, and_assoc]

theorem firstNotice_eq (i : IndexFile) :
    ∀ (k : Nat) (ns : List Notice), firstNotice i k ns = (noticeViolations i k ns).head?
  | _, [] => rfl
  | k, n :: ns => by
    by_cases h : NoticeRel i n
    · simp [firstNotice, noticeViolations, (noticeOk_iff i n).mpr h, h, firstNotice_eq i (k + 1) ns]
    · have h' : noticeOk i n = false := by
        cases hh : noticeOk i n
        · rfl
        · exact absurd ((noticeOk_iff i n).mp hh) h
      simp [firstNotice, noticeViolations, h', h]
      rfl

theorem firstRemoved_eq (i : IndexFile) :
    ∀ (k : Nat) (earlier rs : List Removed),
      firstRemoved i k earlier rs = (removedViolations i k earlier rs).head?
  | _, _, [] => rfl
  | k, earlier, r :: rs => by
    by_cases h : RemovedRel i earlier r
    · simp [firstRemoved, removedViolations, (removedOk_iff i earlier r).mpr h, h,
        firstRemoved_eq i (k + 1) (earlier ++ [r]) rs]
    · have h' : removedOk i earlier r = false := by
        cases hh : removedOk i earlier r
        · rfl
        · exact absurd ((removedOk_iff i earlier r).mp hh) h
      simp [firstRemoved, removedViolations, h', h]
      rfl

theorem relational_eq (i : IndexFile) : relational i = (relationViolations i).head? := by
  simp only [relational, relationViolations, orElse_eq, head?_append', firstNotice_eq,
    firstRemoved_eq]

theorem notices_nil_iff (i : IndexFile) :
    ∀ (k : Nat) (ns : List Notice), noticeViolations i k ns = [] ↔ ∀ n ∈ ns, NoticeRel i n
  | _, [] => by simp [noticeViolations]
  | k, n :: ns => by
    by_cases h : NoticeRel i n
    · simp [noticeViolations, h, notices_nil_iff i (k + 1) ns]
    · simp [noticeViolations, h]

theorem removed_nil_iff (i : IndexFile) :
    ∀ (k : Nat) (earlier rs : List Removed),
      removedViolations i k earlier rs = [] ↔
        (∀ r ∈ rs,
            (¬∃ o ∈ i.operations, o.id = r.id ∧ o.version = r.version) ∧
              ∃ n ∈ i.notices, n.id = r.id ∧ n.version = r.version) ∧
          (rs.map fun r => (r.id, r.version)).Nodup ∧
          ∀ r ∈ rs, ¬∃ e ∈ earlier, e.id = r.id ∧ e.version = r.version
  | _, _, [] => by simp [removedViolations]
  | k, earlier, r :: rs => by
    have ih := removed_nil_iff i (k + 1) (earlier ++ [r]) rs
    by_cases h : RemovedRel i earlier r
    · simp only [removedViolations, h, ite_true, List.nil_append, ih]
      obtain ⟨hop, hearly, hnamed⟩ := h
      constructor
      · rintro ⟨hall, hnd, hlater⟩
        refine ⟨?_, ?_, ?_⟩
        · intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact ⟨hop, hnamed⟩
          · exact hall r' hr'
        · refine List.nodup_cons.mpr ⟨?_, hnd⟩
          intro hm
          obtain ⟨r', hr', he⟩ := List.mem_map.mp hm
          exact hlater r' hr' ⟨r, by simp, (Prod.mk.inj he).1.symm, (Prod.mk.inj he).2.symm⟩
        · intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact hearly
          · rintro ⟨e, he, h1, h2⟩
            exact hlater r' hr' ⟨e, by simp [he], h1, h2⟩
      · rintro ⟨hall, hnd, hlater⟩
        refine ⟨fun r' hr' => hall r' (List.mem_cons_of_mem _ hr'), (List.nodup_cons.mp hnd).2, ?_⟩
        intro r' hr'
        rintro ⟨e, he, h1, h2⟩
        rcases List.mem_append.mp he with he | he
        · exact hlater r' (List.mem_cons_of_mem _ hr') ⟨e, he, h1, h2⟩
        · simp only [List.mem_singleton] at he
          subst he
          exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨r', hr', by simp [h1, h2]⟩)
    · simp only [removedViolations, h, ite_false]
      simp only [List.cons_append, reduceCtorEq, false_iff]
      rintro ⟨hall, hnd, hlater⟩
      apply h
      refine ⟨(hall r (by simp)).1, hlater r (by simp), (hall r (by simp)).2⟩

theorem relations_nil_iff (i : IndexFile) :
    relationViolations i = [] ↔
      (∀ n ∈ i.notices, NoticeRel i n) ∧
        (i.removed.map fun r => (r.id, r.version)).Nodup ∧
        ∀ r ∈ i.removed,
          (¬∃ o ∈ i.operations, o.id = r.id ∧ o.version = r.version) ∧
            ∃ n ∈ i.notices, n.id = r.id ∧ n.version = r.version := by
  simp only [relationViolations, List.append_eq_nil_iff, notices_nil_iff, removed_nil_iff]
  constructor
  · rintro ⟨hn, hall, hnd, -⟩
    exact ⟨hn, hnd, hall⟩
  · rintro ⟨hn, hnd, hall⟩
    exact ⟨hn, hall, hnd, by simp⟩

/-! ## The document claims -/

theorem index_encode (i : IndexFile) : i.toJson = indexLayout i := rfl

theorem first_none_iff (v : Value) :
    firstViolation indexTy v = none ↔ violations "" indexTy [] v = [] := by
  simp [firstViolation, List.head?_eq_none_iff]

/-- C8 `IndexSchemaExact`: on a J1-valid value the walk finds no violation exactly when the value is
the layout of an index whose every node is well formed. -/
theorem index_schema_exact (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) :
    firstViolation indexTy v = none ↔ ∃ i, IndexNodeWF i ∧ v = indexLayout i := by
  rw [first_none_iff]
  constructor
  · exact index_of_ok hv.2.2.2
  · rintro ⟨i, hi, rfl⟩
    exact index_layout_ok i hi

theorem index_wf_iff (i : IndexFile) : IndexWF i ↔ IndexNodeWF i ∧ relationViolations i = [] := by
  rw [relations_nil_iff]
  rfl

theorem index_ok (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) (i : IndexFile) :
    IndexFile.ofJson v = .ok i ↔ IndexWF i ∧ v = indexLayout i := by
  unfold IndexFile.ofJson
  rw [walk_eq]
  cases hvi : violations "" indexTy [] v with
  | cons e es =>
    simp only [List.head?_cons, reduceCtorEq, false_iff, not_and]
    rintro hwf rfl
    rw [index_layout_ok i hwf.1] at hvi
    exact absurd hvi (by simp)
  | nil =>
    obtain ⟨i0, hi0, rfl⟩ := index_of_ok hv.2.2.2 hvi
    simp only [List.head?_nil, index_extract, relational_eq]
    cases hr : (relationViolations i0).head? with
    | some e =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hwf he
      obtain rfl := layout_injective he
      rw [((index_wf_iff i0).mp hwf).2] at hr
      exact absurd hr (by simp)
    | none =>
      have hnil : relationViolations i0 = [] := List.head?_eq_none_iff.mp hr
      simp only [Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨(index_wf_iff i0).mpr ⟨hi0, hnil⟩, rfl⟩
      · rintro ⟨-, he⟩
        exact layout_injective he

/-- C8: `IndexFile.ofJson` refuses with the walk's first violation, else (the value then the
layout of a well-formed node tree) the first relational violation. -/
theorem index_error (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) (e : DocError) :
    IndexFile.ofJson v = .error e ↔
      firstViolation indexTy v = some e ∨
        ∃ i,
          IndexNodeWF i ∧
            firstViolation indexTy v = none ∧
            v = indexLayout i ∧ (relationViolations i).head? = some e := by
  unfold IndexFile.ofJson firstViolation
  rw [walk_eq]
  cases hvi : violations "" indexTy [] v with
  | cons e' es =>
    simp only [List.head?_cons, Except.error.injEq, Option.some.injEq, reduceCtorEq, false_and,
      and_false, exists_false, or_false]
  | nil =>
    obtain ⟨i0, hi0, rfl⟩ := index_of_ok hv.2.2.2 hvi
    simp only [List.head?_nil, index_extract, relational_eq, reduceCtorEq, false_or, true_and]
    constructor
    · intro h
      refine ⟨i0, hi0, rfl, ?_⟩
      cases hr : (relationViolations i0).head? with
      | none => simp [hr] at h
      | some e' =>
        simp only [hr, Except.error.injEq] at h
        rw [h]
    · rintro ⟨i, -, he, hr⟩
      obtain rfl := layout_injective he
      simp [hr]

/-- C8 `IndexWellFormed` as a check. -/
theorem index_check (i : IndexFile) : i.wellFormed = true ↔ IndexWF i := by
  unfold IndexFile.wellFormed
  rw [index_encode, walk_eq, relational_eq, index_wf_iff]
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.head?_eq_none_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨i', hi', he⟩ := index_of_ok (index_keys i) h1
    obtain rfl := layout_injective he
    exact ⟨hi', h2⟩
  · rintro ⟨hn, hrel⟩
    exact ⟨index_layout_ok i hn, hrel⟩

/-- C8 `IndexValid`: a well-formed index's JSON is a J1-valid value. -/
theorem index_valid (i : IndexFile) (h : IndexWF i) : FvdepAudit.Json.Spec.Valid i.toJson := by
  rw [index_encode]
  exact index_valid_layout i h.1

theorem index_kinds : kindTable "" [] indexTy = indexKinds := by rfl

/-! ## Bytes (C8 `IndexBytes`) -/

/-- The shipped one-copy `dropFinalLF` = its byte-list description. -/
theorem dropFinalLF_eq (b : ByteArray) : dropFinalLF b = withoutFinalLF b := by
  rcases b with ⟨d⟩
  unfold dropFinalLF withoutFinalLF
  by_cases h : 0 < d.size
  · have hl : d.toList.getLast? = some d[d.size - 1] := by
      rw [List.getLast?_eq_getElem?]
      simp
    simp only [ByteArray.size, h, ↓reduceDIte, hl, Option.some.injEq,
      ByteArray.getElem_eq_getElem_data]
    by_cases hx : d[d.size - 1] = 10
    · simp only [hx, ↓reduceIte]
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      show d.extract 0 (d.size - 1) = d.toList.dropLast.toArray
      rw [Array.extract_eq_pop rfl, ← Array.toList_pop, Array.toArray_toList]
    · simp only [hx, ↓reduceIte]
  · have : d = #[] := by simpa using h
    subst this
    simp [ByteArray.size]

theorem dropFinalLF_push (b : ByteArray) : dropFinalLF (b.push 0x0A) = b := by
  rw [dropFinalLF_eq]
  unfold withoutFinalLF
  simp [ByteArray.push, List.getLast?_append, List.dropLast_append_of_ne_nil]

/-- Encoding refuses an index outside schema 1, else gives its canonical text + LF. -/
theorem encode_index_iff (i : IndexFile) (b : ByteArray) :
    encodeIndex i = .ok b ↔ IndexWF i ∧ b = (print (indexLayout i)).push 0x0A := by
  have hc := index_check i
  unfold IndexFile.wellFormed at hc
  unfold encodeIndex
  cases hw : walk "" indexTy [] i.toJson with
  | some
    e =>
    simp only [hw, Option.isNone_some, Bool.false_and, Bool.false_eq_true, false_iff] at hc
    simp [hc]
  | none =>
    cases hr : relational i with
    | some
      e =>
      simp only [hw, hr, Option.isNone_none, Option.isNone_some, Bool.and_false, Bool.false_eq_true,
        false_iff] at hc
      simp [hc]
    | none =>
      simp only [hw, hr, Option.isNone_none, Bool.and_self, true_iff] at hc
      simp [hc, index_encode, eq_comm]

/-- Encoding refuses with the first violation of the index's layout: the walk's, else the first
relational one. -/
theorem encode_index_error (i : IndexFile) (e : DocError) :
    encodeIndex i = .error e ↔
      firstViolation indexTy (indexLayout i) = some e ∨
        firstViolation indexTy (indexLayout i) = none ∧ (relationViolations i).head? = some e := by
  unfold encodeIndex firstViolation
  rw [index_encode, walk_eq, relational_eq]
  cases (violations "" indexTy [] (indexLayout i)).head? with
  | some e' => simp
  | none => cases (relationViolations i).head? <;> simp

/-- decode ∘ encode = id on well-formed indexes. -/
theorem index_bytes_encode (i : IndexFile) (h : IndexWF i) :
    decodeIndex ((print (indexLayout i)).push 0x0A) = .ok i := by
  unfold decodeIndex
  rw [dropFinalLF_push, FvdepAudit.Json.Proof.print_decode _ (index_valid_layout i h.1)]
  simp only
  rw [(index_ok _ (index_valid_layout i h.1) i).mpr ⟨h, rfl⟩]

/-- `decodeIndex` accepts exactly the bytes whose text (one final LF removed) J decodes to the
layout of a well-formed index, and returns that index. -/
theorem index_bytes_ok (b : ByteArray) (i : IndexFile) :
    decodeIndex b = .ok i ↔ decode (withoutFinalLF b) = .ok (indexLayout i) ∧ IndexWF i := by
  unfold decodeIndex
  rw [dropFinalLF_eq]
  cases hd : decode (withoutFinalLF b) with
  | error j => simp
  | ok v =>
    have hok := index_ok v (FvdepAudit.Json.Proof.decode_valid _ v hd) i
    simp only [Except.ok.injEq]
    cases ho : IndexFile.ofJson v with
    | ok i' =>
      rw [ho, Except.ok.injEq] at hok
      simp only [Except.ok.injEq, hok, and_comm]
    | error d =>
      rw [ho] at hok
      simp only [reduceCtorEq, false_iff] at hok ⊢
      exact fun ⟨h1, h2⟩ => hok ⟨h2, h1⟩

/-- A document refusal of `decodeIndex` = the first violation of the value J decodes from the
bytes (one final LF removed): the walk's, else the first relational one. -/
theorem index_bytes_doc (b : ByteArray) (e : DocError) :
    decodeIndex b = .error (.doc e) ↔
      ∃ v,
        decode (withoutFinalLF b) = .ok v ∧
          (firstViolation indexTy v = some e ∨
            ∃ i,
              IndexNodeWF i ∧
                firstViolation indexTy v = none ∧
                v = indexLayout i ∧ (relationViolations i).head? = some e) := by
  unfold decodeIndex
  rw [dropFinalLF_eq]
  cases hd : decode (withoutFinalLF b) with
  | error j => simp
  | ok v =>
    simp only [Except.ok.injEq, exists_eq_left']
    exact
      Iff.trans (by cases IndexFile.ofJson v <;> simp)
        (index_error v (FvdepAudit.Json.Proof.decode_valid _ v hd) e)

/-- A text refusal of `decodeIndex` = J's refusal of the bytes (one final LF removed). -/
theorem index_bytes_text (b : ByteArray) (j : DecodeError) :
    decodeIndex b = .error (.text j) ↔ decode (withoutFinalLF b) = .error j := by
  unfold decodeIndex
  rw [dropFinalLF_eq]
  cases decode (withoutFinalLF b) with
  | error j' => simp
  | ok v =>
    simp only [reduceCtorEq, iff_false]
    split <;> simp

end FvdepAudit.Index.Proof
