import FvdepAudit.Library.Proof.Tree

/-! Proofs: the `cat-file --batch -Z` replies (contract `docs/contracts/U5b-oracle.md` L4):
`parseBatch` accepts exactly the replies to the planned blobs, each its exact header, `size`
content bytes + NUL, nothing after the last. -/

namespace FvdepAudit.Library.Proof

open FvdepCore.Library FvdepAudit.Library.Spec

theorem bytesAt_iff (b : ByteArray) :
    ∀ (xs : List UInt8) (i : Nat), bytesAt b i xs = true ↔ ∃ rest, b.data.toList.drop i = xs ++ rest
  | [], i => by simp [bytesAt]
  | x :: xs, i => by
    unfold bytesAt
    by_cases hi : i < b.size
    · simp only [hi, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, bytesAt_iff b xs (i + 1),
        drop_cons' b i hi, List.cons_append, List.cons.injEq, exists_and_left]
    · simp only [hi, ↓reduceDIte, Bool.false_eq_true, false_iff, not_exists]
      intro rest h
      have : b.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hi)
      rw [this] at h
      simp at h

theorem batchHeader_eq (x : Blob) :
    batchHeader x.oid x.size = x.oid ++ ascii " blob " ++ decimalBytes x.size ++ [0] := by
  rw [ascii_names.2.2.2.2, decimalBytes_eq]
  rfl

theorem batchLayout_cons (x : Blob) (xs : List Blob) (c : ByteArray) (cs : List ByteArray) :
    batchLayout (x :: xs) (c :: cs) = replyLayout x c ++ batchLayout xs cs := by
  simp only [batchLayout, List.zip_cons_cons, List.map_cons, List.flatten_cons]

theorem getElem!_drop (b : ByteArray) (i k : Nat) (h : i + k < b.size) :
    b[i + k]! =
      (b.data.toList.drop i)[k]'(by
          simp at h ⊢; omega) := by
  rw [getElem!_pos b (i + k) h]
  simp only [List.getElem_drop]
  rfl

/-- One reply's checks = its bytes split as header, `n` content bytes, NUL, the rest. -/
theorem reply_iff (b : ByteArray) (i : Nat) (hd : List UInt8) (n : Nat) (hi : i ≤ b.size) :
    (bytesAt b i hd && decide (i + hd.length + n < b.size) && b[i + hd.length + n]! == 0) = true ↔
      ∃ c rest, c.length = n ∧ b.data.toList.drop i = hd ++ c ++ 0 :: rest := by
  have hl : (b.data.toList.drop i).length = b.size - i := by simp
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hb, hlt⟩, hz⟩ := h
    obtain ⟨r, hr⟩ := (bytesAt_iff b hd i).1 hb
    have hrl : n < r.length := by
      have := congrArg List.length hr
      simp only [List.length_append] at this
      omega
    rw [show i + hd.length + n = i + (hd.length + n) by omega, getElem!_drop b i _ (by omega)] at hz
    have hz' : r[n] = 0 := by
      rw [← hz]
      simp only [hr]
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    refine
      ⟨r.take n, r.drop (n + 1), by
        simp; omega, ?_⟩
    rw [hr, List.append_assoc]
    congr 1
    conv =>
      lhs; rw [← List.take_append_drop n r]
    rw [List.drop_eq_getElem_cons hrl, hz']
  · rintro ⟨c, rest, hc, hdrop⟩
    have hlen := congrArg List.length hdrop
    simp only [List.length_append, List.length_cons, hc] at hlen
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine
      ⟨⟨(bytesAt_iff b hd i).2 ⟨c ++ 0 :: rest, by rw [hdrop, List.append_assoc]⟩, by omega⟩, ?_⟩
    rw [show i + hd.length + n = i + (hd.length + n) by omega, getElem!_drop b i _ (by omega)]
    simp only [hdrop, List.append_assoc]
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simp [hc]

/-- A reply split = its content at `i + |hd|` + the rest after its NUL. -/
theorem reply_parts (b : ByteArray) (i : Nat) (hd : List UInt8) (n : Nat) (c rest : List UInt8)
    (h : b.data.toList.drop i = hd ++ c ++ 0 :: rest) (hc : c.length = n) :
    (b.extract (i + hd.length) (i + hd.length + n)).data.toList = c ∧
      b.data.toList.drop (i + hd.length + n + 1) = rest := by
  have h2 : b.data.toList.drop (i + hd.length) = c ++ 0 :: rest := by
    rw [← List.drop_drop, h, List.append_assoc]
    exact List.drop_left' rfl
  constructor
  · rw [extract_eq', Nat.add_sub_cancel_left, h2, ← hc]
    exact List.take_left' rfl
  · rw [show i + hd.length + n + 1 = (i + hd.length) + (n + 1) by omega, ← List.drop_drop, h2, ← hc]
    simp

/-- `parseBatchFrom` from a reply's start = the replies' layout from there. -/
theorem parseBatchFrom_exact (b : ByteArray) :
    ∀ (plan : List Blob) (i : Nat) (acc cs : List ByteArray),
      i ≤ b.size →
        (parseBatchFrom b i plan acc = some cs ↔
          ∃ cs',
            cs = acc.reverse ++ cs' ∧
              cs'.length = plan.length ∧
              (∀ p ∈ plan.zip cs', p.2.size = p.1.size) ∧
              b.data.toList.drop i = batchLayout plan cs')
  | [], i, acc, cs, hi => by
    simp only [parseBatchFrom, beq_iff_eq]
    by_cases he : i = b.size
    · subst he
      simp only [↓reduceIte, Option.some.injEq]
      have hd : b.data.toList.drop b.size = [] :=
        List.drop_eq_nil_of_le (show b.data.toList.length ≤ b.size by simp)
      rw [hd]
      constructor
      · rintro rfl
        exact ⟨[], by simp, rfl, by simp, by simp [batchLayout]⟩
      · rintro ⟨cs', rfl, hl, -, -⟩
        have : cs' = [] := by simpa using hl
        subst this
        simp
    · simp only [he, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨cs', -, hl, -, hd⟩
      have : cs' = [] := by simpa using hl
      subst this
      have hne : b.data.toList.drop i ≠ [] := by
        simp [List.drop_eq_nil_iff]
        omega
      exact hne (by simpa [batchLayout] using hd)
  | x :: xs, i, acc, cs, hi => by
    simp only [parseBatchFrom]
    generalize hh : batchHeader x.oid x.size = hd
    have hrl :
      ∀ (c0 : ByteArray) (tail : List UInt8),
        replyLayout x c0 ++ tail = hd ++ c0.data.toList ++ 0 :: tail := by
      intro c0 tail
      rw [← hh, batchHeader_eq]
      simp only [replyLayout, List.append_assoc, List.singleton_append]
    have hr := reply_iff b i hd x.size hi
    by_cases hc :
      (bytesAt b i hd && decide (i + hd.length + x.size < b.size) &&
          b[i + hd.length + x.size]! == 0) =
        true
    · obtain ⟨c, rest, hcl, hdrop⟩ := hr.1 hc
      obtain ⟨hex, hnext⟩ := reply_parts b i hd x.size c rest hdrop hcl
      have hle : i + hd.length + x.size + 1 ≤ b.size := by
        have := congrArg List.length hdrop
        simp only [List.length_drop, Array.length_toList, List.length_append, List.length_cons,
          hcl] at this
        simp only [ByteArray.size]
        omega
      simp only [hc, ↓reduceIte]
      rw [parseBatchFrom_exact b xs (i + hd.length + x.size + 1) _ cs hle, hnext]
      have hsz : (b.extract (i + hd.length) (i + hd.length + x.size)).size = x.size := by
        show (b.extract (i + hd.length) (i + hd.length + x.size)).data.size = x.size
        rw [← Array.length_toList, hex, hcl]
      constructor
      · rintro ⟨cs', rfl, hl, hp, hd'⟩
        refine
          ⟨b.extract (i + hd.length) (i + hd.length + x.size) :: cs', by simp, by simp [hl], ?_, ?_⟩
        · intro p hp'
          simp only [List.zip_cons_cons, List.mem_cons] at hp'
          rcases hp' with rfl | hp'
          · exact hsz
          · exact hp p hp'
        · rw [batchLayout_cons, hrl, hex, hdrop, hd']
      · rintro ⟨cs', rfl, hl, hp, hd'⟩
        cases cs' with
        | nil => simp at hl
        | cons c0
          cs'' =>
          have hc0 : c0.data.toList.length = x.size := by
            have := hp (x, c0) (by simp)
            simpa using this
          rw [batchLayout_cons, hrl, hdrop, List.append_assoc, List.append_assoc] at hd'
          have hsplit := List.append_inj (List.append_cancel_left hd') (by rw [hcl, hc0])
          obtain ⟨h1, h2⟩ := hsplit
          simp only [List.cons.injEq, true_and] at h2
          have heq : b.extract (i + hd.length) (i + hd.length + x.size) = c0 := by
            apply ByteArray.ext
            apply Array.toList_inj.1
            rw [hex, h1]
          refine ⟨cs'', by simp [heq], by simpa using hl, fun p hp' => hp p (by simp [hp']), h2⟩
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨cs', -, hl, hp, hd'⟩
      cases cs' with
      | nil => simp at hl
      | cons c0
        cs'' =>
        have hc0 : c0.data.toList.length = x.size := by
          have := hp (x, c0) (by simp)
          simpa using this
        rw [batchLayout_cons, hrl] at hd'
        have := hr.2 ⟨c0.data.toList, batchLayout xs cs'', hc0, hd'⟩
        rw [hc] at this
        cases this

/-- L4: `parseBatch` accepts exactly the replies to the planned blobs + returns their contents in
plan order. -/
theorem parseBatch_exact (plan : List Blob) (b : ByteArray) (cs : List ByteArray) :
    parseBatch plan b = some cs ↔
      cs.length = plan.length ∧
        (∀ p ∈ plan.zip cs, p.2.size = p.1.size) ∧ b.data.toList = batchLayout plan cs := by
  rw [parseBatch, parseBatchFrom_exact b plan 0 [] cs (Nat.zero_le _)]
  simp

end FvdepAudit.Library.Proof
