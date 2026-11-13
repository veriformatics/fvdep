import FvdepAudit.Doc.Proof.Receipt
import FvdepAudit.Json.Proof.Corollaries

/-! The lock file (D4): encoding = the layout, the schema walk accepts exactly the layouts of
well-formed locks, decoding (values + bytes), normalization. -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
open FvdepAudit.Doc.Spec
open FvdepAudit.Json.Spec (keysAscend keysAscendMembers keysAscendList)

theorem lock_encode (l : Lock) : l.toJson = lockLayout l := by
  rcases l with ⟨lib, es⟩
  simp only [Lock.toJson, lockLayout]
  congr
  funext r
  exact receipt_encode r

theorem lock_extract (l : Lock) (h : ∀ r ∈ l.entries, kindAgrees r = true) :
    lockOfValue (lockLayout l) = l := by
  rcases l with ⟨lib, es⟩
  have hes : (es.map receiptLayout).map receiptOfValue = es := by
    rw [List.map_map]
    conv =>
      rhs; rw [← List.map_id es]
    apply List.map_congr_left
    intro r hr
    exact extract_layout r (h r hr)
  simp [lockOfValue, lockLayout, membersOf, member?, textOf, Commit.parse_toString, hes]

theorem atPath_id (r : Receipt) :
    atPath ["request", "module"] (receiptLayout r) = some (.str (idOf r)) := by
  rcases r with ⟨c, e1, e2⟩ | ⟨c⟩ <;>
    simp [atPath, receiptLayout, List.lookup, idOf, Receipt.common]

theorem descents_ok (p : List PathSeg) :
    ∀ (i : Nat) (es : List Receipt),
      (es.map idOf).Pairwise (· < ·) →
        descentsSpec p ["request", "module"] i (es.map receiptLayout) = []
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | i, a :: b :: rest, h => by
    have hab : idOf a < idOf b := (List.pairwise_cons.mp h).1 _ (by simp)
    have ih := descents_ok p (i + 1) (b :: rest) (List.pairwise_cons.mp h).2
    simp only [List.map_cons, descentsSpec, atPath_id, hab, ite_true, List.nil_append]
    simpa using ih

theorem elems_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (es : List Receipt),
      (∀ r ∈ es, ReceiptWF r) →
        elemViolations tag receiptTy receiptTy p i (es.map receiptLayout) = []
  | _, [], _ => rfl
  | i, r :: es, h => by
    simp only [List.map_cons, elemViolations, ite_self, List.append_eq_nil_iff]
    exact
      ⟨receipt_layout_ok r (h r (by simp)),
        elems_ok tag p (i + 1) es fun x hx => h x (by simp [hx])⟩

theorem lock_layout_ok (l : Lock) (h : LockWF l) : violations "" lockTy [] (lockLayout l) = [] := by
  rcases l with ⟨lib, es⟩
  obtain ⟨hwf, hasc⟩ := h
  simp [violations, lockTy, lockLayout, resolveSpec, discSpec, unknownSpec, missingSpec,
    memberViolations, List.lookup, leafSpec, kindOf, ← check_iff, Rule.check, Commit.parse_toString,
    orderSpec, elems_ok "" [PathSeg.key "modules"] 0 es hwf,
    descents_ok [PathSeg.key "modules"] 1 es hasc]

/-- Accepted receipts in an array, out of `elemViolations`. -/
theorem elems_of_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Value),
      keysAscendList xs = true →
        elemViolations tag receiptTy receiptTy p i xs = [] →
        ∃ es : List Receipt, xs = es.map receiptLayout ∧ ∀ r ∈ es, ReceiptWF r
  | _, [], _, _ => ⟨[], rfl, by simp⟩
  | i, x :: xs, hk, h => by
    simp only [keysAscendList, Bool.and_eq_true] at hk
    simp only [elemViolations, ite_self, List.append_eq_nil_iff] at h
    obtain ⟨r, hr, rfl⟩ := receipt_of_ok hk.1 h.1
    obtain ⟨es, rfl, hes⟩ := elems_of_ok tag p (i + 1) xs hk.2 h.2
    exact ⟨r :: es, rfl, by simpa [hr] using hes⟩

theorem descents_of_ok (p : List PathSeg) :
    ∀ (i : Nat) (es : List Receipt),
      descentsSpec p ["request", "module"] i (es.map receiptLayout) = [] →
        (es.map idOf).Pairwise (· < ·)
  | _, [], _ => by simp
  | _, [_], _ => by simp
  | i, a :: b :: rest, h => by
    simp only [List.map_cons, descentsSpec, atPath_id, List.append_eq_nil_iff] at h
    obtain ⟨hab, hrest⟩ := h
    have hlt : idOf a < idOf b := by
      by_cases hc : idOf a < idOf b
      · exact hc
      · simp [hc] at hab
    have ih := descents_of_ok p (i + 1) (b :: rest) (by simpa using hrest)
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hlt
    · exact String.lt_trans hlt ((List.pairwise_cons.mp ih).1 y hy)

/-- `LockSchemaExact`, the hard half. -/
theorem lock_of_ok {v : Value} (hk : keysAscend v = true) (h : violations "" lockTy [] v = []) :
    ∃ l, LockWF l ∧ v = lockLayout l := by
  obtain ⟨ms, rfl, s, extra, hd, hunk, hmiss, hmem⟩ := viol_obj (t := lockTy) rfl h
  obtain ⟨hsch, rfl, rfl⟩ := disc_ok_int hd
  obtain ⟨hasc, hkm⟩ := keysAscend_obj hk
  have hkeys : ms.map (·.1) = ["library", "modules", "schema"] := by
    refine obj_keys ?_ hunk hmiss _ (by decide) ?_ hasc
    · intro k hk'
      simp only [List.mem_singleton] at hk'
      subst hk'
      simp [hsch]
    · intro k
      simp only [List.map, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
      constructor <;> intro hk' <;> rcases hk' with h' | h' | h' <;> subst h' <;> simp
  clear hunk hmiss hd hasc
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons hkeys
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain rfl : r3 = [] := List.map_eq_nil_iff.mp h3
  simp [List.lookup] at hsch
  subst hsch
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2⟩ := hmem
  simp [keysAscendMembers] at hkm
  obtain ⟨-, k2⟩ := hkm
  have c1 := scalar_ok rfl g1
  simp only [ruleHolds] at c1
  obtain ⟨lib, rfl⟩ := c1
  obtain ⟨xs, rfl, hel, hord⟩ := viol_arr rfl g2
  have k2' : keysAscendList xs = true := by simpa [keysAscend] using k2
  obtain ⟨es, rfl, hes⟩ := elems_of_ok "" _ 0 xs k2' hel
  exact ⟨⟨lib, es⟩, ⟨hes, descents_of_ok _ 1 es hord⟩, rfl⟩

/-! ## Lock claims (D7, D8) -/

theorem receipts_keys (es : List Receipt) : keysAscendList (es.map receiptLayout) = true := by
  induction es with
  | nil => rfl
  | cons r es ih => simp [keysAscendList, receipt_keys, ih]

theorem lock_keys (l : Lock) : keysAscend (lockLayout l) = true := by
  have k : ["library", "modules", "schema"].Pairwise (· < ·) := by decide
  rcases l with ⟨lib, es⟩
  simp [lockLayout, keysAscend, keysAscendMembers, receipts_keys, k]

theorem wf_kinds {es : List Receipt} (h : ∀ r ∈ es, ReceiptWF r) : ∀ r ∈ es, kindAgrees r = true :=
  fun r hr => kindAgrees_of_wf (h r hr)

/-- D7 `LockSchemaExact`. -/
theorem lock_schema_exact (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) :
    firstViolation lockTy v = none ↔ ∃ l, LockWF l ∧ v = lockLayout l := by
  unfold firstViolation
  rw [List.head?_eq_none_iff]
  constructor
  · exact lock_of_ok hv.2.2.2
  · rintro ⟨l, hl, rfl⟩
    exact lock_layout_ok l hl

theorem lock_error (v : Value) (e : DocError) :
    Lock.ofJson v = .error e ↔ firstViolation lockTy v = some e := by
  unfold Lock.ofJson firstViolation
  rw [walk_eq]
  cases (violations "" lockTy [] v).head? <;> simp

theorem lock_ok (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) (l : Lock) :
    Lock.ofJson v = .ok l ↔ LockWF l ∧ v = lockLayout l := by
  constructor
  · intro h
    unfold Lock.ofJson at h
    rw [walk_eq] at h
    cases hvio : violations "" lockTy [] v with
    | nil =>
      rw [hvio] at h
      simp only [List.head?_nil, Except.ok.injEq] at h
      obtain ⟨l', hl', rfl⟩ := lock_of_ok hv.2.2.2 hvio
      rw [lock_extract l' (wf_kinds hl'.1)] at h
      subst h
      exact ⟨hl', rfl⟩
    | cons e es =>
      rw [hvio] at h
      simp at h
  · rintro ⟨hl, rfl⟩
    unfold Lock.ofJson
    rw [walk_eq, lock_layout_ok l hl]
    simp [lock_extract l (wf_kinds hl.1)]

/-- D8 `LockCheck`. -/
theorem lock_check (l : Lock) : l.wellFormed = true ↔ LockWF l := by
  constructor
  · intro h
    simp only [Lock.wellFormed, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true] at h
    obtain ⟨hk, hw⟩ := h
    rw [walk_eq, lock_encode, List.head?_eq_none_iff] at hw
    obtain ⟨l', hl', he⟩ := lock_of_ok (lock_keys l) hw
    have e := congrArg lockOfValue he
    rw [lock_extract l hk, lock_extract l' (wf_kinds hl'.1)] at e
    exact e ▸ hl'
  · intro h
    simp only [Lock.wellFormed, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true]
    refine ⟨wf_kinds h.1, ?_⟩
    rw [walk_eq, lock_encode, lock_layout_ok l h]
    rfl

theorem receipt_depth (r : Receipt) : FvdepAudit.Json.Spec.depth (receiptLayout r) ≤ 3 := by
  rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
      ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩ <;>
    rcases sh with _ | _ | _ <;>
    cases pol <;>
    rcases ad with _ | argv <;>
    simp [receiptLayout, FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
      depth_nullOr, strs_depth, Receipt.common]

theorem receipts_depth (es : List Receipt) :
    FvdepAudit.Json.Spec.depthList (es.map receiptLayout) ≤ 3 := by
  induction es with
  | nil => simp [FvdepAudit.Json.Spec.depthList]
  | cons r es ih =>
    simp only [List.map_cons, FvdepAudit.Json.Spec.depthList]
    have := receipt_depth r
    omega

theorem receipts_ints (es : List Receipt) (h : ∀ r ∈ es, ReceiptWF r) :
    FvdepAudit.Json.Spec.intsFitList (es.map receiptLayout) = true := by
  induction es with
  | nil => rfl
  | cons r es ih =>
    have hv := receipt_valid r (h r (by simp))
    rw [receipt_encode] at hv
    simp only [List.map_cons, FvdepAudit.Json.Spec.intsFitList, Bool.and_eq_true]
    exact ⟨hv.1, ih fun x hx => h x (by simp [hx])⟩

theorem receipts_fit (es : List Receipt) (h : ∀ r ∈ es, ReceiptWF r) :
    FvdepAudit.Json.Spec.stringsFitList (es.map receiptLayout) = true := by
  induction es with
  | nil => rfl
  | cons r es ih =>
    have hv := receipt_valid r (h r (by simp))
    rw [receipt_encode] at hv
    simp only [List.map_cons, FvdepAudit.Json.Spec.stringsFitList, Bool.and_eq_true]
    exact ⟨hv.2.1, ih fun x hx => h x (by simp [hx])⟩

/-- D7 `LockValid`. -/
theorem lock_valid (l : Lock) (h : LockWF l) : FvdepAudit.Json.Spec.Valid l.toJson := by
  rw [lock_encode]
  rcases l with ⟨lib, es⟩
  refine ⟨?_, ?_, ?_, lock_keys _⟩
  · simp [lockLayout, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
      receipts_ints es h.1, FvdepAudit.Json.Spec.maxInt]
  · simp [lockLayout, FvdepAudit.Json.Spec.stringsFit, FvdepAudit.Json.Spec.stringsFitMembers,
      receipts_fit es h.1, commit_size]
    decide
  · have := receipts_depth es
    simp [lockLayout, FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
      FvdepAudit.Json.Spec.maxDepth]
    omega

/-- D7 `LockBytes` (encode side): a well-formed lock's bytes decode to it. -/
theorem lock_bytes_encode (l : Lock) (h : LockWF l) : decodeLock (encodeLock l) = .ok l := by
  unfold decodeLock encodeLock
  rw [FvdepAudit.Json.Proof.print_decode _ (lock_valid l h)]
  simp only
  rw [(lock_ok _ (lock_valid l h) l).mpr ⟨h, lock_encode l⟩]

/-- D7 `LockBytes` (accept side). -/
theorem lock_bytes_ok (b : ByteArray) (l : Lock) (h : decodeLock b = .ok l) :
    LockWF l ∧ ∃ v, decode b = .ok v ∧ v = lockLayout l := by
  unfold decodeLock at h
  cases hd : decode b with
  | error j => simp [hd] at h
  | ok v =>
    simp only [hd] at h
    cases ho : Lock.ofJson v with
    | error d => simp [ho] at h
    | ok l' =>
      simp only [ho, Except.ok.injEq] at h
      subst h
      have hv := FvdepAudit.Json.Proof.decode_valid b v hd
      obtain ⟨hwf, hl⟩ := (lock_ok v hv l').mp ho
      exact ⟨hwf, v, rfl, hl⟩

/-- D7 `LockBytes` (refusal side): step 0's text error, else the walk's first violation. -/
theorem lock_bytes_error (b : ByteArray) (e : LockError) :
    decodeLock b = .error e ↔
      (∃ j, decode b = .error j ∧ e = .text j) ∨
        ∃ v d, decode b = .ok v ∧ firstViolation lockTy v = some d ∧ e = .doc d := by
  unfold decodeLock
  cases hd : decode b with
  | error j =>
    simp only [Except.error.injEq, reduceCtorEq, false_and, exists_false, or_false]
    constructor
    · intro h
      exact ⟨j, rfl, h.symm⟩
    · rintro ⟨j', hj, rfl⟩
      rw [hj]
  | ok v =>
    simp only [reduceCtorEq, false_and, exists_false, false_or, Except.ok.injEq]
    cases ho : Lock.ofJson v with
    | error d =>
      have hf := (lock_error v d).mp ho
      constructor
      · intro h
        simp only [Except.error.injEq] at h
        exact ⟨v, d, rfl, hf, h.symm⟩
      · rintro ⟨v', d', rfl, hf', rfl⟩
        rw [hf] at hf'
        simp only [Option.some.injEq] at hf'
        rw [hf']
    | ok l =>
      constructor
      · intro h
        simp at h
      · rintro ⟨v', d', rfl, hf', rfl⟩
        have := (lock_error v d').mpr hf'
        rw [ho] at this
        simp at this

/-! ## Normalization (D4) -/

theorem key_trans :
    ∀ a b c : Receipt,
      decide (moduleKey a ≤ moduleKey b) = true →
        decide (moduleKey b ≤ moduleKey c) = true → decide (moduleKey a ≤ moduleKey c) = true := by
  intro a b c h1 h2
  simp only [decide_eq_true_eq] at *
  exact Std.le_trans h1 h2

theorem key_total :
    ∀ a b : Receipt,
      (decide (moduleKey a ≤ moduleKey b) || decide (moduleKey b ≤ moduleKey a)) = true := by
  intro a b
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Std.le_total

theorem string_lt_of_le_ne {a b : String} (h1 : a ≤ b) (h2 : a ≠ b) : a < b :=
  Classical.byContradiction fun h3 => h2 (Std.le_antisymm h1 (String.not_lt.mp h3))

/-- D7 `NormalizePreserves`. -/
theorem normalize_preserves (l : Lock) :
    l.normalize.library = l.library ∧
      l.normalize.entries.Perm l.entries ∧
      (l.normalize.entries.map idOf).Pairwise (· ≤ ·) ∧
      ∀ k,
        l.normalize.entries.filter (fun r => idOf r == k) =
          l.entries.filter (fun r => idOf r == k) := by
  refine ⟨rfl, List.mergeSort_perm _ _, ?_, ?_⟩
  · have h := List.pairwise_mergeSort key_trans key_total l.entries
    rw [List.pairwise_map]
    exact h.imp fun hab => of_decide_eq_true hab
  · intro k
    have hpw :
      (l.entries.filter fun r => idOf r == k).Pairwise fun a b =>
        decide (moduleKey a ≤ moduleKey b) := by
      rw [List.pairwise_iff_forall_sublist]
      intro a b hab
      have ha : a ∈ l.entries.filter fun r => idOf r == k := hab.subset (by simp)
      have hb : b ∈ l.entries.filter fun r => idOf r == k := hab.subset (by simp)
      replace ha := (List.mem_filter.mp ha).2
      replace hb := (List.mem_filter.mp hb).2
      have : moduleKey a = moduleKey b := by
        simp only [beq_iff_eq] at ha hb
        exact ha.trans hb.symm
      simp [this, Std.le_refl]
    have hsub :=
      List.sublist_mergeSort key_trans key_total hpw (List.filter_sublist (l := l.entries))
    have h1 :
      (l.entries.filter fun r => idOf r == k).Sublist
        (l.normalize.entries.filter fun r => idOf r == k) := by
      simpa [List.filter_filter, Lock.normalize] using hsub.filter (fun r => idOf r == k)
    have hlen :=
      ((List.mergeSort_perm l.entries fun a b => decide (moduleKey a ≤ moduleKey b)).filter
          (fun r => idOf r == k)).length_eq
    exact (h1.eq_of_length hlen.symm).symm

/-- D7 `NormalizeSorted`. -/
theorem normalize_sorted (l : Lock) (hd : (l.entries.map idOf).Nodup)
    (hw : ∀ r ∈ l.entries, ReceiptWF r) : LockWF l.normalize := by
  obtain ⟨-, hp, hle, -⟩ := normalize_preserves l
  refine ⟨fun r hr => hw r (hp.mem_iff.mp hr), ?_⟩
  have hne : (l.normalize.entries.map idOf).Nodup := ((hp.map idOf).nodup_iff).mpr hd
  exact (hle.and hne).imp fun h => string_lt_of_le_ne h.1 h.2

/-- D8 (reviewer-3 D10): the lock schema's general types = interface §6 + D4's, written apart. -/
theorem lock_kinds : kindTable "" [] lockTy = lockKinds := by rfl

end FvdepAudit.Doc.Proof
