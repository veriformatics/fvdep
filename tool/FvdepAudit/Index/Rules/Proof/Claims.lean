import FvdepAudit.Index.Rules.Proof.Rows

/-! Every shipped row against its spec row, in C9's order; the claims (contract U4 C8
`ValidateExact`, `ClosureExact`), headers = the ledger statements. -/

namespace FvdepAudit.Index.Rules.Proof

open Lean FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepAudit.Index.Rules.Spec

theorem mem_carriers (F : Facts) (e : Entry) (fl : Flag) (c : Name) :
    c ∈ (reach F (e.spec :: e.abi.toList)).filter (carries F fl) ↔
      Checked F e c ∧ ∃ d, libDecl? F c = some d ∧ HasFlag F d fl := by
  simp only [List.mem_filter, reach_exact, Checked, carries]
  constructor
  · rintro ⟨⟨hr, hl⟩, hc⟩
    split at hc
    · rename_i d hd
      exact ⟨⟨hr, hl⟩, d, hd, (hasFlag_iff F d fl).mp hc⟩
    · simp at hc
  · rintro ⟨⟨hr, hl⟩, d, hd, hf⟩
    refine ⟨⟨hr, hl⟩, ?_⟩
    rw [hd]
    exact (hasFlag_iff F d fl).mpr hf

theorem specIn_iff (F : Facts) (e : Entry) :
    ((canonical? e).isSome && specIn F e.spec (specModule e)) = true ↔
      canonical? e ≠ none ∧
        (∃ fn, e.spec = .str (specModule e) fn) ∧
        ∃ d, libDecl? F e.spec = some d ∧ d.kind = .defn ∧ d.module = specModule e := by
  simp only [Bool.and_eq_true, Option.isSome_iff_ne_none, specIn]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · split at h₁
      · rename_i p fn hfn
        simp only [beq_iff_eq] at h₁
        exact ⟨fn, by rw [hfn, h₁]⟩
      · simp at h₁
    · split at h₂
      · rename_i d hd
        simp only [Bool.and_eq_true, beq_iff_eq] at h₂
        exact ⟨d, hd, h₂⟩
      · simp at h₂
  · rintro ⟨⟨fn, hfn⟩, d, hd, hk, hm⟩
    rw [hd, hfn]
    simp [hk, hm]

theorem encodable_iff (F : Facts) (c : Name) :
    encodable F c = true ↔
      ∃ d sig, libDecl? F c = some d ∧ FvdepCore.Protocol.sigOf d.type = some sig := by
  unfold encodable
  split
  · rename_i d hd
    simp [hd, Option.isSome_iff_exists]
  · rename_i hd
    simp [hd]

theorem propIn_iff (F : Facts) (e : Entry) (o : Name) :
    ((canonical? e).isSome && propIn F o (specModule e)) = true ↔ PropObligation F e o := by
  simp only [Bool.and_eq_true, Option.isSome_iff_ne_none, PropObligation, propIn]
  apply and_congr_right
  intro _
  apply and_congr
  · cases o <;> simp
  · split
    · rename_i d hd
      simp only [Bool.and_eq_true, beq_iff_eq, alphaEq_iff]
      constructor
      · rintro ⟨⟨hk, hm⟩, ht⟩
        exact ⟨d, hd, hk, hm, by simpa [erase] using ht⟩
      · rintro ⟨d', hd', hk, hm, ht⟩
        rw [hd] at hd'
        cases hd'
        exact ⟨⟨hk, hm⟩, by simpa [erase] using ht⟩
    · rename_i hd
      simp [hd]

theorem abiShape_iff (F : Facts) (a : Name) : abiShape F a = true ↔ AbiShape F a := by
  unfold abiShape AbiShape
  split
  · rename_i d hd
    simp only [Bool.and_eq_true, beq_iff_eq, hd, Option.some.injEq, exists_and_left,
      exists_eq_left']
    constructor
    · rintro ⟨hk, hm⟩
      refine ⟨hk, ?_⟩
      split at hm
      · rename_i s h
        exact ⟨s, h, hm⟩
      · simp at hm
    · rintro ⟨hk, s, hm, hv⟩
      refine ⟨hk, ?_⟩
      rw [hm]
      exact hv
  · rename_i hd
    simp [hd]

theorem holdsOk_iff (M m : Name) : holdsOk M m = true ↔ HoldsOk M m := by
  simp [holdsOk, HoldsOk, or_assoc]

theorem importOk_iff (i : Name) : importOk i = true ↔ ImportOk i := by
  simp [importOk, ImportOk, or_assoc]

theorem known_iff (l : Lists) (id version : String) :
    known l id version = true ↔ Known l id version := by simp [known, Known]

theorem isText_iff (s : String) : FvdepCore.Doc.isText 65536 s = true ↔ ReasonText s := by
  simp [FvdepCore.Doc.isText, FvdepCore.Doc.isControl, ReasonText, and_assoc]

theorem isDigest_iff (s : String) : FvdepCore.Doc.isDigest s = true ↔ LowerHex s 64 := by
  simp [FvdepCore.Doc.isDigest, FvdepCore.Doc.isLowerHex, LowerHex]

theorem compatEarlier_iff (l : Lists) (e : Entry) (c : String) :
    compatEarlier l e c = true ↔ CompatEarlier l e c := by
  unfold compatEarlier CompatEarlier
  split
  · rename_i cv m v hc he
    simp [hc, he, Option.isSome_iff_ne_none, and_assoc]
  · rename_i h
    constructor
    · intro hf
      simp at hf
    · rintro ⟨cv, m, v, hc, he, _, _⟩
      exact (h cv m v hc he).elim

/-! ## Rows of an entry, a notice, a removed record -/

theorem not_true_iff {b : Bool} {P : Prop} (h : b = true ↔ P) : (!b) = true ↔ ¬P := by
  cases b <;> simp_all

theorem entry_corr (F : Facts) (l : Lists) (i : Nat) (e : Entry) :
    Corr ((entryChecks F l i e).map (·.map (subject e.id e.version, ·))) (entryRows F l i e) := by
  simp only [entryChecks, entryRows, List.map_append, List.map_cons, List.map_nil, List.map_map]
  refine Corr.append (Corr.append ?_ ?_) ?_
  · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))
    · exact rowOk_fail _ _ (by simp [Option.isSome_iff_ne_none])
    · exact rowOk_fail _ _ (by simp [Option.isSome_iff_ne_none])
    · cases hc : canonical? e with
      | none => simp [RowOk]
      | some p =>
        obtain ⟨m, v⟩ := p
        by_cases he : e.module = entryModule m v
        · simp [RowOk, fail, he]
        · simp [RowOk, fail, he, and_assoc]
    · exact rowOk_fail _ _ (by simp)
    · exact rowOk_fail _ _ (specIn_iff F e)
    · exact rowOk_fail _ _ (encodable_iff F e.spec)
  · apply corr_map
    intro fl _
    simp only [Function.comp_apply, Option.map_map]
    exact rowOk_least (fun c => (subject e.id e.version, .flagged c fl)) (mem_carriers F e fl)
  · refine
      .cons ?_
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))))
    · rw [Option.map_map]
      exact rowOk_find (fun o => not_true_iff (propIn_iff F e o)) _
    · rw [Option.map_map]
      exact rowOk_repeat _ _
    · cases ha : e.abi with
      | none => simp [RowOk]
      | some
        a =>
        have := rowOk_fail (subject e.id e.version) (.abiNotDefinition a) (abiShape_iff F a)
        simp only [RowOk, row, Option.some.injEq, forall_eq', exists_eq_left'] at this ⊢
        exact this
    · cases ha : e.abi with
      | none => simp [RowOk]
      | some a =>
        simp only [RowOk, Option.some.injEq, forall_eq', exists_eq_left']
        unfold abiTypeCheck
        cases ht : abiTypeOf? F a e.spec with
        | none => simp
        | some o =>
          cases o with
          | none => simp
          | some t =>
            by_cases hb : erase t = erase bytesFn ∨ erase t = erase bytesOptFn
            · have hb' : (alphaEq t bytesFn || alphaEq t bytesOptFn) = true := by
                simpa [alphaEq_iff] using hb
              simp [fail, hb', hb]
            · have hb' : (alphaEq t bytesFn || alphaEq t bytesOptFn) = false := by
                rw [Bool.eq_false_iff]
                intro h
                exact hb (by simpa [alphaEq_iff] using h)
              simp only [not_or] at hb
              simp [fail, hb', hb.1, hb.2]
    · cases hc : e.compat with
      | none => simp [RowOk]
      | some
        c =>
        have := rowOk_fail (subject e.id e.version) (.compatNotEarlier c) (compatEarlier_iff l e c)
        simp only [RowOk, row, Option.some.injEq, forall_eq', exists_eq_left'] at this ⊢
        exact this
    · cases hc : e.compat with
      | none => simp [RowOk]
      | some c =>
        simp only [RowOk, Option.some.injEq, forall_eq', exists_eq_left']
        unfold compatTypeCheck
        cases ho : listedAt? l e.id c with
        | none => simp
        | some old =>
          simp only [Option.some.injEq, forall_eq', exists_eq_left']
          cases hd : defeqOf? F e.spec old.spec with
          | none => simp
          | some b => cases b <;> simp [fail]
    · rw [Option.map_map]
      exact
        rowOk_least (fun m => (subject e.id e.version, .closureHolds m)) fun m =>
          List.mem_filter.trans
            (and_congr (closure_exact F e.module m).1 (not_true_iff (holdsOk_iff e.module m)))
    · rw [Option.map_map]
      refine rowOk_least (fun i => (subject e.id e.version, .closureImports i)) fun i => ?_
      simp only [List.mem_flatMap, (closure_exact F e.module _).1, badImports]
      constructor
      · rintro ⟨m, hm, hi⟩
        split at hi
        · rename_i x hx
          simp only [List.mem_filter] at hi
          exact ⟨m, x, hm, hx, hi.1, (not_true_iff (importOk_iff i)).mp hi.2⟩
        · simp at hi
      · rintro ⟨m, x, hm, hx, hi, hn⟩
        refine ⟨m, hm, ?_⟩
        rw [hx]
        simp only [List.mem_filter]
        exact ⟨hi, (not_true_iff (importOk_iff i)).mpr hn⟩
    · rw [Option.map_map]
      refine
        rowOk_least (fun m => (subject e.id e.version, .notRegularFile m (modulePath m))) fun m =>
          ?_
      simp only [List.mem_filter, (closure_exact F e.module m).1, regularFile]
      constructor
      · rintro ⟨hm, hr⟩
        refine ⟨hm, fun x hx => ?_⟩
        rw [hx] at hr
        simpa using hr
      · rintro ⟨hm, hr⟩
        refine ⟨hm, ?_⟩
        cases hx : modFacts? F m with
        | none => simp
        | some x => simp [hr x hx]

theorem notice_corr (l : Lists) (n : Notice) :
    Corr ((noticeChecks l n).map (·.map (subject n.id n.version, ·))) (noticeRows l n) := by
  simp only [noticeChecks, noticeRows, List.map_cons, List.map_nil]
  refine
    .cons (rowOk_fail _ _ (known_iff l _ _)) (.cons ?_ (.cons (rowOk_fail _ _ (isText_iff _)) .nil))
  cases hr : n.replacement with
  | none => simp [RowOk]
  | some
    r =>
    have :=
      rowOk_fail (subject n.id n.version) (.noticeReplacement r n.id) (b :=
        r != n.version && known l n.id r) (P := r ≠ n.version ∧ Known l n.id r)
        (by simp [known_iff])
    simp only [RowOk, row, Option.some.injEq, forall_eq', exists_eq_left'] at this ⊢
    exact this

theorem removed_corr (l : Lists) (k : Nat) (r : Removed) :
    Corr ((removedChecks l k r).map (·.map (subject r.id r.version, ·))) (removedRows l k r) := by
  simp only [removedChecks, removedRows, List.map_cons, List.map_nil]
  refine
    .cons (rowOk_fail _ _ (by simp))
      (.cons (rowOk_fail _ _ (by simp))
        (.cons (rowOk_fail _ _ (by simp))
          (.cons (rowOk_fail _ _ (isDigest_iff _))
            (.cons (rowOk_fail _ _ (by simp [Option.isSome_iff_ne_none]))
              (.cons (rowOk_fail _ _ (by simp))
                (.cons (rowOk_fail _ _ (by simp [List.any_eq_true])) .nil))))))

theorem checks_corr (F : Facts) (l : Lists) : Corr (checks F l) (specChecks F l) := by
  unfold checks specChecks
  refine Corr.append (Corr.append (Corr.append (Corr.append (Corr.append ?_ ?_) ?_) ?_) ?_) ?_
  · apply corr_map
    intro e _
    unfold observedFile observedRow
    cases hc : canonical? e with
    | none => simp [RowOk, row]
    | some p =>
      obtain ⟨m, v⟩ := p
      exact
        rowOk_fail _ _
          (by
            simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
            constructor
            · rintro h m' v' hmv hm
              simp only [Option.some.injEq, Prod.mk.injEq] at hmv
              obtain ⟨rfl, rfl⟩ := hmv
              exact h.resolve_left fun hn => hn hm
            · intro h
              by_cases hm : e.module = entryModule m v
              · exact .inr (h m v rfl hm)
              · exact .inl hm)
  · exact corr_flatMap _ _ _ fun p _ => entry_corr F l p.2 p.1
  · apply corr_map
    intro p _
    by_cases h : ∃ e ∈ l.entries, modulePath e.module = p
    · have : l.entries.any (modulePath ·.module == p) = true := by simpa [List.any_eq_true] using h
      simp [RowOk, row, this, h]
    · have : l.entries.any (modulePath ·.module == p) = false := by simpa [List.any_eq_true] using h
      simp [RowOk, row, this, h]
  · exact corr_flatMap _ _ _ fun n _ => notice_corr l n
  · exact corr_flatMap _ _ _ fun p _ => removed_corr l p.2 p.1
  · exact .cons (rowOk_fail _ _ (by simp)) .nil

/-! ## Claims -/

theorem validate_accepts (F : Facts) (l : Lists) : validate F l = none ↔ RegistryValid F l :=
  head_none (checks_corr F l)

theorem validate_first (F : Facts) (l : Lists) (f : Found) (h : validate F l = some f) :
    FirstFail (specChecks F l) f := head_some (checks_corr F l) h

end FvdepAudit.Index.Rules.Proof
