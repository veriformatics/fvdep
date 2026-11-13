import FvdepAudit.Doc.Proof.Invert
import FvdepAudit.Doc.Proof.Valid

/-! Receipts (D3): encoding = the layout, extraction inverts it, the schema walk accepts exactly the
layouts of well-formed receipts, decoding. -/

namespace FvdepAudit.Doc.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
open FvdepAudit.Doc.Spec

theorem optStr_eq (o : Option String) : optStr o = nullOr o := by cases o <;> rfl

theorem receipt_encode (r : Receipt) : r.toJson = receiptLayout r := by
  rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
      ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩ <;>
    rcases sh with _ | _ | _ <;>
    cases pol <;>
    rcases ad with _ | argv <;>
    simp [Receipt.toJson, receiptLayout, optStr_eq, shapeText, policyText, Receipt.common, nullOr]

theorem textOpt_nullOr (o : Option String) : textOpt (some (nullOr o)) = o := by cases o <;> rfl

theorem extract_layout (r : Receipt) (h : kindAgrees r = true) :
    receiptOfValue (receiptLayout r) = r := by
  rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
      ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩ <;>
    simp only [kindAgrees, beq_iff_eq] at h <;>
    subst h <;>
    rcases sh with _ | _ | _ <;>
    cases pol <;>
    rcases ad with _ | argv <;>
    simp [receiptOfValue, receiptLayout, member?, textOf, textOpt_nullOr, membersOf,
      ModuleId.parse_toString, EntryVersion.parse_toString, Commit.parse_toString,
      Function.comp_def, Receipt.common]

theorem holds_commit (c : Commit) : ruleHolds .commit (.str (toString c)) := ⟨c, rfl⟩

theorem holds_module (m : ModuleId) (h : SpellingFits (toString m)) :
    ruleHolds .moduleId (.str (toString m)) := ⟨m, rfl, h⟩

theorem holds_version (x : EntryVersion) (h : SpellingFits (toString x)) :
    ruleHolds .version (.str (toString x)) := ⟨x, rfl, h⟩

/-- The argv elements after the first meet their rule. -/
theorem args_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (rest : List String),
      i ≠ 0 →
        (∀ x ∈ rest, ArgText false x) →
        elemViolations tag (.scalar [.str] (.arg true)) (.scalar [.str] (.arg false)) p i
            (rest.map .str) =
          []
  | _, [], _, _ => rfl
  | i, x :: rest, hi, h => by
    have hx := h x (by simp)
    have ih := args_ok tag p (i + 1) rest (by omega) fun y hy => h y (by simp [hy])
    simp only [List.map_cons, elemViolations, hi, ite_false, ih, List.append_nil]
    simp [violations, resolveSpec, leafSpec, kindOf, ruleHolds, hx]

theorem receipt_layout_ok {tag : String} {p : List PathSeg} (r : Receipt) (h : ReceiptWF r) :
    violations tag receiptTy p (receiptLayout r) = [] := by
  rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
    ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩
  · simp only [ReceiptWF, Receipt.common] at h
    obtain
      ⟨hc, hp, hm, hv, hs, hk, hsh, ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl, ⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩,
        rfl, he1, he2⟩ :=
      h
    subst hk
    simp only [SpellingFits] at hm hv
    rcases sh with _ | sh
    · exact absurd rfl hsh
    cases sh <;> cases pol <;>
      simp [violations, memberViolations, resolveSpec, discSpec, unknownSpec, missingSpec,
        List.lookup, leafSpec, kindOf, ← check_iff, Rule.check, receiptTy, digestsTy, requestTy,
        argvTy, receiptLayout, proofOnly, differentialOnly, Receipt.common, nullOr,
        Commit.parse_toString, ModuleId.parse_toString, EntryVersion.parse_toString, hm, hv,
        (isUtc_iff _).mpr hc, (isProfileId_iff _).mpr hp, (isDigest_iff _).mpr hs,
        (isConstant_iff _).mpr hi, (isConstant_iff _).mpr hx, (isDigest_iff _).mpr hy,
        (isDigest_iff _).mpr hz, (isDigest_iff _).mpr he1, (isDigest_iff _).mpr he2]
  · simp only [ReceiptWF, Receipt.common] at h
    obtain
      ⟨hc, hp, hm, hv, hs, hk, rfl, rfl, rfl, ⟨argv, rfl, a, rest, rfl, ha, hrest⟩, rfl, rfl,
        ⟨x, rfl, hx⟩⟩ :=
      h
    subst hk
    simp only [SpellingFits] at hm hv
    cases pol <;>
      simp [violations, memberViolations, elemViolations, orderSpec, resolveSpec, discSpec,
        List.lookup, unknownSpec, missingSpec, leafSpec, kindOf, ← check_iff, Rule.check, receiptTy,
        digestsTy, requestTy, argvTy, receiptLayout, proofOnly, differentialOnly, Receipt.common,
        nullOr, Commit.parse_toString, ModuleId.parse_toString, EntryVersion.parse_toString, hm, hv,
        (isUtc_iff _).mpr hc, (isProfileId_iff _).mpr hp, (isDigest_iff _).mpr hs,
        (isDigest_iff _).mpr hx, (isArg_iff _ _).mpr ha,
        args_ok "differential" _ 1 rest (by omega) hrest]

/-! ## The walk accepts only layouts of well-formed receipts -/

open FvdepAudit.Json.Spec (keysAscend keysAscendMembers)

theorem keysAscend_obj {ms : List (String × Value)} (h : keysAscend (.obj ms) = true) :
    (ms.map (·.1)).Pairwise (· < ·) ∧ keysAscendMembers ms = true := by
  simp only [keysAscend, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem scalar_ok {tag : String} {t : Ty} {ks : List JKind} {r : Rule} {p : List PathSeg}
    {v : Value} (ht : resolveSpec tag t = .scalar ks r) (h : violations tag t p v = []) :
    ruleHolds r v := by
  rw [viol_scalar ht] at h
  exact (leaf_nil h).2

/-- A plain object type with no violations: exactly its fields' keys, in order. -/
theorem obj_plain {tag : String} {fs : List (String × Ty)} {p : List PathSeg} {v : Value}
    (hk : keysAscend v = true) (hs : (fs.map (·.1)).Pairwise (· < ·))
    (h : violations tag (.obj none fs) p v = []) :
    ∃ ms,
      v = .obj ms ∧
        ms.map (·.1) = fs.map (·.1) ∧
        memberViolations tag fs p ms = [] ∧ keysAscendMembers ms = true := by
  obtain ⟨ms, rfl, tag', extra, hd, hu, hm, hmem⟩ := viol_obj (t := .obj none fs) rfl h
  obtain ⟨rfl, rfl⟩ := disc_ok_none hd
  obtain ⟨hasc, hkm⟩ := keysAscend_obj hk
  exact ⟨ms, rfl, obj_keys (by simp) hu hm _ hs (by simp) hasc, hmem, hkm⟩

/-- The argv elements after the first, accepted, are arguments. -/
theorem args_of_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Value),
      i ≠ 0 →
        elemViolations tag (.scalar [.str] (.arg true)) (.scalar [.str] (.arg false)) p i xs = [] →
        ∃ rest : List String, xs = rest.map .str ∧ ∀ x ∈ rest, ArgText false x
  | _, [], _, _ => ⟨[], rfl, by simp⟩
  | i, x :: xs, hi, h => by
    simp only [elemViolations, hi, ite_false, List.append_eq_nil_iff] at h
    obtain ⟨hx, hxs⟩ := h
    have hr := scalar_ok (t := .scalar [.str] (.arg false)) rfl hx
    simp only [ruleHolds] at hr
    obtain ⟨a, rfl, ha⟩ := hr
    obtain ⟨rest, rfl, hrest⟩ := args_of_ok tag p (i + 1) xs (by omega) hxs
    exact ⟨a :: rest, rfl, by simpa [ha] using hrest⟩

theorem resolve_po_p (r : Rule) : resolveSpec "proof" (proofOnly r) = .scalar [.null, .str] r := by
  simp [resolveSpec, proofOnly, List.lookup]

theorem resolve_po_d (r : Rule) :
    resolveSpec "differential" (proofOnly r) = .scalar [.null, .str] .null := by
  simp [resolveSpec, proofOnly, List.lookup]

theorem resolve_do_p (r : Rule) :
    resolveSpec "proof" (differentialOnly r) = .scalar [.null, .str] .null := by
  simp [resolveSpec, differentialOnly, List.lookup]

theorem resolve_do_d (r : Rule) :
    resolveSpec "differential" (differentialOnly r) = .scalar [.null, .str] r := by
  simp [resolveSpec, differentialOnly, List.lookup]

theorem resolve_adapter_p :
    resolveSpec "proof"
        (.byTag [("differential", argvTy), ("proof", .scalar [.arr, .null] .null)]) =
      .scalar [.arr, .null] .null := by
  simp [resolveSpec, List.lookup]

theorem resolve_adapter_d :
    resolveSpec "differential"
        (.byTag [("differential", argvTy), ("proof", .scalar [.arr, .null] .null)]) =
      argvTy := by
  simp [resolveSpec, List.lookup]

/-- Six members, in the order of `ks`, out of a key list equation. -/
theorem six_members {β : Type} {ms : List (String × β)} {k1 k2 k3 k4 k5 k6 : String}
    (h : ms.map (·.1) = [k1, k2, k3, k4, k5, k6]) :
    ∃ a1 a2 a3 a4 a5 a6, ms = [(k1, a1), (k2, a2), (k3, a3), (k4, a4), (k5, a5), (k6, a6)] := by
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons h
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain ⟨a4, r4, rfl, h4⟩ := map_fst_cons h3
  obtain ⟨a5, r5, rfl, h5⟩ := map_fst_cons h4
  obtain ⟨a6, r6, rfl, h6⟩ := map_fst_cons h5
  obtain rfl : r6 = [] := List.map_eq_nil_iff.mp h6
  exact ⟨a1, a2, a3, a4, a5, a6, rfl⟩

theorem digests_proof {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations "proof" digestsTy p v = []) :
    ∃ y e1 z e2 sc,
      v =
          .obj
            [("adapter", .null), ("impl_sources", .str y), ("phase1_export", .str e1),
              ("proof_sources", .str z), ("solution_export", .str e2), ("spec_closure", .str sc)] ∧
        DigestText y ∧ DigestText e1 ∧ DigestText z ∧ DigestText e2 ∧ DigestText sc := by
  obtain ⟨ms, rfl, hkeys, hmem, -⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, a2, a3, a4, a5, a6, rfl⟩ := six_members hkeys
  simp only [memberViolations, List.lookup, List.append_nil, List.append_eq_nil_iff] at hmem
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hmem
  have c1 := scalar_ok (resolve_do_p _) g1
  have c2 := scalar_ok (resolve_po_p _) g2
  have c3 := scalar_ok (resolve_po_p _) g3
  have c4 := scalar_ok (resolve_po_p _) g4
  have c5 := scalar_ok (resolve_po_p _) g5
  have c6 := scalar_ok rfl g6
  simp only [ruleHolds] at c1 c2 c3 c4 c5 c6
  obtain ⟨y, rfl, hy⟩ := c2
  obtain ⟨e1, rfl, he1⟩ := c3
  obtain ⟨z, rfl, hz⟩ := c4
  obtain ⟨e2, rfl, he2⟩ := c5
  obtain ⟨sc, rfl, hsc⟩ := c6
  subst c1
  exact ⟨y, e1, z, e2, sc, rfl, hy, he1, hz, he2, hsc⟩

theorem digests_diff {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations "differential" digestsTy p v = []) :
    ∃ x sc,
      v =
          .obj
            [("adapter", .str x), ("impl_sources", .null), ("phase1_export", .null),
              ("proof_sources", .null), ("solution_export", .null), ("spec_closure", .str sc)] ∧
        DigestText x ∧ DigestText sc := by
  obtain ⟨ms, rfl, hkeys, hmem, -⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, a2, a3, a4, a5, a6, rfl⟩ := six_members hkeys
  simp only [memberViolations, List.lookup, List.append_nil, List.append_eq_nil_iff] at hmem
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hmem
  have c1 := scalar_ok (resolve_do_d _) g1
  have c2 := scalar_ok (resolve_po_d _) g2
  have c3 := scalar_ok (resolve_po_d _) g3
  have c4 := scalar_ok (resolve_po_d _) g4
  have c5 := scalar_ok (resolve_po_d _) g5
  have c6 := scalar_ok rfl g6
  simp only [ruleHolds] at c1 c2 c3 c4 c5 c6
  obtain ⟨x, rfl, hx⟩ := c1
  obtain ⟨sc, rfl, hsc⟩ := c6
  subst c2 c3 c4 c5
  exact ⟨x, sc, rfl, hx, hsc⟩

theorem request_proof {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations "proof" requestTy p v = []) :
    ∃ (i : String) (m : ModuleId) (x s : String) (ver : EntryVersion),
      v =
          .obj
            [("adapter", .null), ("impl", .str i), ("module", .str (toString m)), ("proof", .str x),
              ("shape", .str s), ("version", .str (toString ver))] ∧
        ConstantText i ∧
        SpellingFits (toString m) ∧
        ConstantText x ∧ (s = "abi" ∨ s = "fn") ∧ SpellingFits (toString ver) := by
  obtain ⟨ms, rfl, hkeys, hmem, -⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, a2, a3, a4, a5, a6, rfl⟩ := six_members hkeys
  simp only [memberViolations, List.lookup, List.append_nil, List.append_eq_nil_iff] at hmem
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hmem
  have c1 := scalar_ok resolve_adapter_p g1
  have c2 := scalar_ok (resolve_po_p _) g2
  have c3 := scalar_ok rfl g3
  have c4 := scalar_ok (resolve_po_p _) g4
  have c5 := scalar_ok (resolve_po_p _) g5
  have c6 := scalar_ok rfl g6
  simp only [ruleHolds] at c1 c2 c3 c4 c5 c6
  obtain ⟨i, rfl, hi⟩ := c2
  obtain ⟨m, rfl, hm⟩ := c3
  obtain ⟨x, rfl, hx⟩ := c4
  obtain ⟨s, rfl, hs⟩ := c5
  obtain ⟨ver, rfl, hv⟩ := c6
  subst c1
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  exact ⟨i, m, x, s, ver, rfl, hi, hm, hx, hs, hv⟩

theorem request_diff {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations "differential" requestTy p v = []) :
    ∃ (argv : List String) (m : ModuleId) (ver : EntryVersion),
      v =
          .obj
            [("adapter", .arr (argv.map .str)), ("impl", .null), ("module", .str (toString m)),
              ("proof", .null), ("shape", .null), ("version", .str (toString ver))] ∧
        Argv argv ∧ SpellingFits (toString m) ∧ SpellingFits (toString ver) := by
  obtain ⟨ms, rfl, hkeys, hmem, -⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, a2, a3, a4, a5, a6, rfl⟩ := six_members hkeys
  simp only [memberViolations, List.lookup, List.append_nil, List.append_eq_nil_iff] at hmem
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hmem
  obtain ⟨xs, rfl, hel, hord⟩ := viol_arr resolve_adapter_d g1
  have c2 := scalar_ok (resolve_po_d _) g2
  have c3 := scalar_ok rfl g3
  have c4 := scalar_ok (resolve_po_d _) g4
  have c5 := scalar_ok (resolve_po_d _) g5
  have c6 := scalar_ok rfl g6
  simp only [ruleHolds] at c2 c3 c4 c5 c6
  obtain ⟨m, rfl, hm⟩ := c3
  obtain ⟨ver, rfl, hv⟩ := c6
  subst c2 c4 c5
  cases xs with
  | nil => simp [orderSpec] at hord
  | cons x0 rest =>
    simp only [elemViolations, ite_true, List.append_eq_nil_iff] at hel
    obtain ⟨h0, hrest⟩ := hel
    have c0 := scalar_ok (t := .scalar [.str] (.arg true)) rfl h0
    simp only [ruleHolds] at c0
    obtain ⟨a, rfl, ha⟩ := c0
    obtain ⟨l, rfl, hl⟩ := args_of_ok "differential" _ 1 rest (by omega) hrest
    exact ⟨a :: l, m, ver, rfl, ⟨a, l, rfl, ha, hl⟩, hm, hv⟩

theorem seven_members {β : Type} {ms : List (String × β)} {k1 k2 k3 k4 k5 k6 k7 : String}
    (h : ms.map (·.1) = [k1, k2, k3, k4, k5, k6, k7]) :
    ∃ a1 a2 a3 a4 a5 a6 a7,
      ms = [(k1, a1), (k2, a2), (k3, a3), (k4, a4), (k5, a5), (k6, a6), (k7, a7)] := by
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons h
  obtain ⟨a2, a3, a4, a5, a6, a7, rfl⟩ := six_members h1
  exact ⟨a1, a2, a3, a4, a5, a6, a7, rfl⟩

/-- `ReceiptSchemaExact`, the hard half: a key-sorted value the walk accepts is the layout of a
well-formed receipt. -/
theorem receipt_of_ok {tag : String} {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations tag receiptTy p v = []) : ∃ r, ReceiptWF r ∧ v = receiptLayout r := by
  obtain ⟨ms, rfl, s, extra, hd, hunk, hmiss, hmem⟩ := viol_obj (t := receiptTy) rfl h
  obtain ⟨hev, hs, rfl⟩ := disc_ok_str hd
  obtain ⟨hasc, hkm⟩ := keysAscend_obj hk
  have hkeys :
    ms.map (·.1) =
      ["checked", "digests", "evidence", "library", "policy", "request",
        "verification_profile"] := by
    refine obj_keys ?_ hunk hmiss _ (by decide) ?_ hasc
    · intro k hk'
      simp only [List.mem_singleton] at hk'
      subst hk'
      simp [hev]
    · intro k
      simp only [List.map, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
      constructor <;> intro hk' <;> rcases hk' with h' | h' | h' | h' | h' | h' | h' <;>
        subst h' <;>
        simp
  clear hunk hmiss hd hasc
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, rfl⟩ := seven_members hkeys
  simp [List.lookup] at hev
  subst hev
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2, g4, g5, g6, g7⟩ := hmem
  simp [keysAscendMembers] at hkm
  obtain ⟨-, k2, -, -, -, k6, -⟩ := hkm
  have c1 := scalar_ok rfl g1
  have c4 := scalar_ok rfl g4
  have c5 := scalar_ok rfl g5
  have c7 := scalar_ok rfl g7
  simp only [ruleHolds] at c1 c4 c5 c7
  obtain ⟨chk, rfl, hc⟩ := c1
  obtain ⟨lib, rfl⟩ := c4
  obtain ⟨pol, rfl, hpol⟩ := c5
  obtain ⟨prof, rfl, hp⟩ := c7
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs hpol
  rcases hs with rfl | rfl
  · obtain ⟨x, sc, rfl, hx, hsc⟩ := digests_diff k2 g2
    obtain ⟨argv, m, ver, rfl, hargv, hm, hv⟩ := request_diff k6 g6
    rcases hpol with rfl | rfl
    · exact
        ⟨.differential
            ⟨⟨⟨m, ver, none, .differential, none, none, some argv⟩, sc, none, none, some x⟩, lib,
              prof, .development, chk⟩,
          ⟨hc, hp, hm, hv, hsc, rfl, rfl, rfl, rfl, ⟨argv, rfl, hargv⟩, rfl, rfl, ⟨x, rfl, hx⟩⟩,
          rfl⟩
    · exact
        ⟨.differential
            ⟨⟨⟨m, ver, none, .differential, none, none, some argv⟩, sc, none, none, some x⟩, lib,
              prof, .required, chk⟩,
          ⟨hc, hp, hm, hv, hsc, rfl, rfl, rfl, rfl, ⟨argv, rfl, hargv⟩, rfl, rfl, ⟨x, rfl, hx⟩⟩,
          rfl⟩
  · obtain ⟨y, e1, z, e2, sc, rfl, hy, he1, hz, he2, hsc⟩ := digests_proof k2 g2
    obtain ⟨i, m, x, s', ver, rfl, hi, hm, hx, hsh, hv⟩ := request_proof k6 g6
    rcases hpol with rfl | rfl <;> rcases hsh with rfl | rfl
    · exact
        ⟨.proof
            ⟨⟨⟨m, ver, some .abi, .proof, some i, some x, none⟩, sc, some y, some z, none⟩, lib,
              prof, .development, chk⟩
            e1 e2,
          ⟨hc, hp, hm, hv, hsc, rfl, by simp [Receipt.common], ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl,
            ⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩, rfl, he1, he2⟩,
          rfl⟩
    · exact
        ⟨.proof
            ⟨⟨⟨m, ver, some .fn, .proof, some i, some x, none⟩, sc, some y, some z, none⟩, lib,
              prof, .development, chk⟩
            e1 e2,
          ⟨hc, hp, hm, hv, hsc, rfl, by simp [Receipt.common], ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl,
            ⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩, rfl, he1, he2⟩,
          rfl⟩
    · exact
        ⟨.proof
            ⟨⟨⟨m, ver, some .abi, .proof, some i, some x, none⟩, sc, some y, some z, none⟩, lib,
              prof, .required, chk⟩
            e1 e2,
          ⟨hc, hp, hm, hv, hsc, rfl, by simp [Receipt.common], ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl,
            ⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩, rfl, he1, he2⟩,
          rfl⟩
    · exact
        ⟨.proof
            ⟨⟨⟨m, ver, some .fn, .proof, some i, some x, none⟩, sc, some y, some z, none⟩, lib,
              prof, .required, chk⟩
            e1 e2,
          ⟨hc, hp, hm, hv, hsc, rfl, by simp [Receipt.common], ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl,
            ⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩, rfl, he1, he2⟩,
          rfl⟩

/-! ## Receipt claims (D7, D8) -/

theorem kindAgrees_of_wf {r : Receipt} (h : ReceiptWF r) : kindAgrees r = true := by
  rcases r with ⟨c, e1, e2⟩ | ⟨c⟩ <;> simp only [ReceiptWF, Receipt.common] at h <;>
    simp [kindAgrees, h.2.2.2.2.2.1]

theorem keys_nullOr (o : Option String) : keysAscend (nullOr o) = true := by cases o <;> rfl

theorem receipt_keys (r : Receipt) : keysAscend (receiptLayout r) = true := by
  have k1 :
    ["checked", "digests", "evidence", "library", "policy", "request",
          "verification_profile"].Pairwise
      (· < ·) := by
    decide
  have k2 :
    ["adapter", "impl_sources", "phase1_export", "proof_sources", "solution_export",
          "spec_closure"].Pairwise
      (· < ·) := by
    decide
  have k3 : ["adapter", "impl", "module", "proof", "shape", "version"].Pairwise (· < ·) := by decide
  rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
      ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩ <;>
    rcases sh with _ | _ | _ <;>
    cases pol <;>
    rcases ad with _ | argv <;>
    simp [receiptLayout, keysAscend, keysAscendMembers, keys_nullOr, strs_keys, Receipt.common, k1,
      k2, k3]

/-- D7 `ReceiptSchemaExact`. -/
theorem receipt_schema_exact (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) :
    firstViolation receiptTy v = none ↔ ∃ r, ReceiptWF r ∧ v = receiptLayout r := by
  unfold firstViolation
  rw [List.head?_eq_none_iff]
  constructor
  · exact receipt_of_ok hv.2.2.2
  · rintro ⟨r, hr, rfl⟩
    exact receipt_layout_ok r hr

theorem receipt_error (v : Value) (e : DocError) :
    Receipt.ofJson v = .error e ↔ firstViolation receiptTy v = some e := by
  unfold Receipt.ofJson firstViolation
  rw [walk_eq]
  cases (violations "" receiptTy [] v).head? <;> simp

theorem receipt_ok (v : Value) (hv : FvdepAudit.Json.Spec.Valid v) (r : Receipt) :
    Receipt.ofJson v = .ok r ↔ ReceiptWF r ∧ v = receiptLayout r := by
  constructor
  · intro h
    unfold Receipt.ofJson at h
    rw [walk_eq] at h
    cases hvio : violations "" receiptTy [] v with
    | nil =>
      rw [hvio] at h
      simp only [List.head?_nil, Except.ok.injEq] at h
      obtain ⟨r', hr', rfl⟩ := receipt_of_ok hv.2.2.2 hvio
      rw [extract_layout r' (kindAgrees_of_wf hr')] at h
      subst h
      exact ⟨hr', rfl⟩
    | cons e es =>
      rw [hvio] at h
      simp at h
  · rintro ⟨hr, rfl⟩
    unfold Receipt.ofJson
    rw [walk_eq, receipt_layout_ok r hr]
    simp [extract_layout r (kindAgrees_of_wf hr)]

/-- D8 `ReceiptCheck`. -/
theorem receipt_check (r : Receipt) : r.wellFormed = true ↔ ReceiptWF r := by
  constructor
  · intro h
    simp only [Receipt.wellFormed, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hk, hw⟩ := h
    rw [walk_eq, receipt_encode, List.head?_eq_none_iff] at hw
    obtain ⟨r', hr', hl⟩ := receipt_of_ok (receipt_keys r) hw
    have e := congrArg receiptOfValue hl
    rw [extract_layout r hk, extract_layout r' (kindAgrees_of_wf hr')] at e
    exact e ▸ hr'
  · intro h
    simp only [Receipt.wellFormed, Bool.and_eq_true, Option.isNone_iff_eq_none]
    refine ⟨kindAgrees_of_wf h, ?_⟩
    rw [walk_eq, receipt_encode, receipt_layout_ok r h]
    rfl

theorem ints_nullOr (o : Option String) : FvdepAudit.Json.Spec.intsFit (nullOr o) = true := by
  cases o <;> rfl

theorem depth_nullOr (o : Option String) : FvdepAudit.Json.Spec.depth (nullOr o) = 0 := by
  cases o <;> rfl

theorem fit_nullOr {o : Option String}
    (h : ∀ s, o = some s → s.utf8ByteSize ≤ FvdepAudit.Json.Spec.maxStringBytes) :
    FvdepAudit.Json.Spec.stringsFit (nullOr o) = true := by
  cases o with
  | none => rfl
  | some s => simpa [nullOr, FvdepAudit.Json.Spec.stringsFit] using h s rfl

/-- D7 `ReceiptValid`. -/
theorem receipt_valid (r : Receipt) (h : ReceiptWF r) : FvdepAudit.Json.Spec.Valid r.toJson := by
  rw [receipt_encode]
  refine ⟨?_, ?_, ?_, receipt_keys r⟩
  · rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
        ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩ <;>
      rcases sh with _ | _ | _ <;>
      cases pol <;>
      rcases ad with _ | argv <;>
      simp [receiptLayout, FvdepAudit.Json.Spec.intsFit, FvdepAudit.Json.Spec.intsFitMembers,
        ints_nullOr, strs_ints, Receipt.common]
  · rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
      ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩
    · simp only [ReceiptWF, Receipt.common] at h
      obtain
        ⟨hc, hp, hm, hv, hs, -, hsh, ⟨i, rfl, hi⟩, ⟨x, rfl, hx⟩, rfl, ⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩,
          rfl, he1, he2⟩ :=
        h
      rcases sh with _ | sh
      · exact absurd rfl hsh
      cases sh <;> cases pol <;>
        simp [receiptLayout, FvdepAudit.Json.Spec.stringsFit,
          FvdepAudit.Json.Spec.stringsFitMembers, Receipt.common, nullOr, utc_size hc,
          profile_size hp, spelling_size hm, spelling_size hv, digest_size hs, constant_size hi,
          constant_size hx, digest_size hy, digest_size hz, digest_size he1, digest_size he2,
          commit_size] <;>
        decide
    · simp only [ReceiptWF, Receipt.common] at h
      obtain
        ⟨hc, hp, hm, hv, hs, -, rfl, rfl, rfl, ⟨argv, rfl, a, rest, rfl, ha, hrest⟩, rfl, rfl,
          ⟨x, rfl, hx⟩⟩ :=
        h
      have hargs : ∀ s ∈ a :: rest, s.utf8ByteSize ≤ FvdepAudit.Json.Spec.maxStringBytes := by
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact arg_size ha
        · exact arg_size (hrest s hs')
      have hfa :
        FvdepAudit.Json.Spec.stringsFitList (Value.str a :: List.map Value.str rest) = true :=
        strs_fit (a :: rest) hargs
      cases pol <;>
        simp [receiptLayout, FvdepAudit.Json.Spec.stringsFit,
          FvdepAudit.Json.Spec.stringsFitMembers, Receipt.common, nullOr, utc_size hc,
          profile_size hp, spelling_size hm, spelling_size hv, digest_size hs, digest_size hx,
          commit_size, hfa] <;>
        decide
  · rcases r with ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩, e1, e2⟩ |
        ⟨⟨⟨⟨m, ver, sh, k, im, pf, ad⟩, sc, is, ps, da⟩, lib, prof, pol, chk⟩⟩ <;>
      rcases sh with _ | _ | _ <;>
      cases pol <;>
      rcases ad with _ | argv <;>
      simp [receiptLayout, FvdepAudit.Json.Spec.depth, FvdepAudit.Json.Spec.depthMembers,
        depth_nullOr, strs_depth, Receipt.common, FvdepAudit.Json.Spec.maxDepth]

end FvdepAudit.Doc.Proof
