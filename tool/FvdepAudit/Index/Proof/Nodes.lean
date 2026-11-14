import FvdepAudit.Doc.Proof.Receipt
import FvdepAudit.Index.Spec

/-! The index's nodes against their schema data (contract U4 C6): each layout of a well-formed node
has no violation, and a value with none is such a layout (names, statuses, obligations). -/

namespace FvdepAudit.Index.Proof

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepCore.Index
open FvdepAudit.Doc.Spec FvdepAudit.Doc.Proof FvdepAudit.Index.Spec
open FvdepAudit.Json.Spec (keysAscend keysAscendMembers keysAscendList)

/-! ## Names (axioms) -/

theorem names_elems_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List String),
      (∀ a ∈ xs, TextFits 1024 a) → elemViolations tag labelTy labelTy p i (xs.map .str) = []
  | _, [], _ => rfl
  | i, a :: xs, h => by
    simp only [List.map_cons, elemViolations, ite_self, List.append_eq_nil_iff]
    refine ⟨?_, names_elems_ok tag p (i + 1) xs fun x hx => h x (by simp [hx])⟩
    simp [violations, labelTy, resolveSpec, leafSpec, kindOf, ruleHolds, h a (by simp)]

theorem names_elems_of_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Value),
      elemViolations tag labelTy labelTy p i xs = [] →
        ∃ ns : List String, xs = ns.map .str ∧ ∀ a ∈ ns, TextFits 1024 a
  | _, [], _ => ⟨[], rfl, by simp⟩
  | i, x :: xs, h => by
    simp only [elemViolations, ite_self, List.append_eq_nil_iff] at h
    have hr := scalar_ok (t := labelTy) rfl h.1
    simp only [ruleHolds] at hr
    obtain ⟨a, rfl, ha⟩ := hr
    obtain ⟨ns, rfl, hns⟩ := names_elems_of_ok tag p (i + 1) xs h.2
    exact ⟨a :: ns, rfl, by simpa [ha] using hns⟩

theorem names_descents_iff (p : List PathSeg) :
    ∀ (i : Nat) (ns : List String), descentsSpec p [] i (ns.map .str) = [] ↔ Ascends ns
  | _, [] => by simp [descentsSpec, Ascends]
  | _, [_] => by simp [descentsSpec, Ascends]
  | i, a :: b :: rest => by
    have ih := names_descents_iff p (i + 1) (b :: rest)
    simp only [List.map_cons] at ih
    by_cases h : a < b
    · simp [descentsSpec, atPath, Ascends, h, ih]
    · simp [descentsSpec, atPath, Ascends, h]

theorem strsSpec_map : ∀ ns : List String, strsSpec (ns.map .str) = some ns
  | [] => rfl
  | n :: ns => by simp [strsSpec, strsSpec_map ns]

/-- The array type of each status (`axiomsTy`'s cases). -/
theorem resolve_axioms (s : Status) :
    resolveSpec (statusText s) axiomsTy =
      .arr [.arr] labelTy labelTy
        (match s with
        | .proven => .empty
        | .«open» => .ascendingHas "sorryAx"
        | .trusts => .ascendingWithout "sorryAx") := by
  cases s <;> rfl

theorem status_order_iff (p : List PathSeg) (s : Status) (ns : List String) :
    orderSpec p (ns.map .str)
          (match s with
          | .proven => .empty
          | .«open» => .ascendingHas "sorryAx"
          | .trusts => .ascendingWithout "sorryAx") =
        [] ↔
      Ascends ns ∧ StatusAxioms (statusText s) ns := by
  cases s with
  | proven =>
    cases ns with
    | nil => simp [orderSpec, Ascends, StatusAxioms, statusText]
    | cons n ns => simp [orderSpec, StatusAxioms, statusText]
  | «open» =>
    cases ns with
    | nil => simp [orderSpec, descentsSpec, Ascends, StatusAxioms, statusText]
    | cons n ns =>
      have hd := names_descents_iff p 1 (n :: ns)
      have hm : strsSpec (Value.str n :: List.map Value.str ns) = some (n :: ns) :=
        strsSpec_map (n :: ns)
      simp only [List.map_cons] at hd ⊢
      by_cases hs : "sorryAx" ∈ n :: ns
      · simp [orderSpec, hm, hs, StatusAxioms, statusText, hd]
      · simp [orderSpec, hm, hs, StatusAxioms, statusText]
  | trusts =>
    cases ns with
    | nil => simp [orderSpec, descentsSpec, StatusAxioms, statusText]
    | cons n ns =>
      have hd := names_descents_iff p 1 (n :: ns)
      have hm : strsSpec (Value.str n :: List.map Value.str ns) = some (n :: ns) :=
        strsSpec_map (n :: ns)
      simp only [List.map_cons] at hd ⊢
      by_cases hs : "sorryAx" ∈ n :: ns
      · simp [orderSpec, hm, hs, StatusAxioms, statusText]
      · simp [orderSpec, hm, hs, StatusAxioms, statusText, hd]

/-! ## Obligations -/

theorem status_mem (s : Status) : statusText s ∈ ["open", "proven", "trusts"] := by
  cases s <;> decide

theorem obligation_layout_ok {tag : String} {p : List PathSeg} (o : Obligation)
    (h : ObligationWF o) : violations tag obligationTy p (obligationLayout o) = [] := by
  rcases o with ⟨name, s, axs⟩
  obtain ⟨hn, hax, hasc, hst⟩ := h
  have hord := (status_order_iff (p ++ [.key "axioms"]) s axs).mpr ⟨hasc, hst⟩
  have hel := names_elems_ok (statusText s) (p ++ [.key "axioms"]) 0 axs hax
  have hres := resolve_axioms s
  have hsm := status_mem s
  have e1 : violations (statusText s) axiomsTy (p ++ [.key "axioms"]) (namesLayout axs) = [] := by
    simp only [namesLayout, violations, hres, hel, hord, List.append_nil]
  have e2 : violations (statusText s) labelTy (p ++ [.key "name"]) (.str name) = [] := by
    simp [violations, labelTy, resolveSpec, leafSpec, kindOf, ruleHolds, hn]
  have hm :
    memberViolations (statusText s) [("axioms", axiomsTy), ("name", labelTy)] p
        [("axioms", namesLayout axs), ("name", .str name), ("status", .str (statusText s))] =
      [] := by
    simp [memberViolations, List.lookup, e1, e2]
  simp [violations, obligationTy, resolveSpec, obligationLayout, discSpec, List.lookup, hsm,
    unknownSpec, missingSpec, hm]

theorem obligation_of_ok {tag : String} {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations tag obligationTy p v = []) : ∃ o, ObligationWF o ∧ v = obligationLayout o := by
  obtain ⟨ms, rfl, st, extra, hd, hunk, hmiss, hmem⟩ := viol_obj (t := obligationTy) rfl h
  obtain ⟨hst, hstm, rfl⟩ := disc_ok_str hd
  obtain ⟨hasc, -⟩ := keysAscend_obj hk
  have hkeys : ms.map (·.1) = ["axioms", "name", "status"] := by
    refine obj_keys ?_ hunk hmiss _ (by decide) ?_ hasc
    · intro k hk'
      simp only [List.mem_singleton] at hk'
      subst hk'
      simp [hst]
    · intro k
      simp only [List.map, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
      constructor <;> intro hk' <;> rcases hk' with h' | h' | h' <;> subst h' <;> simp
  clear hunk hmiss hd hasc
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons hkeys
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain rfl : r3 = [] := List.map_eq_nil_iff.mp h3
  simp [List.lookup] at hst
  subst hst
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2⟩ := hmem
  have hs : ∃ s : Status, statusText s = st := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hstm
    rcases hstm with rfl | rfl | rfl
    · exact ⟨.«open», rfl⟩
    · exact ⟨.proven, rfl⟩
    · exact ⟨.trusts, rfl⟩
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨xs, rfl, hel, hord⟩ := viol_arr (resolve_axioms s) g1
  obtain ⟨ns, rfl, hns⟩ := names_elems_of_ok _ _ 0 xs hel
  obtain ⟨hA, hS⟩ := (status_order_iff _ s ns).mp hord
  have c2 := scalar_ok (t := labelTy) rfl g2
  simp only [ruleHolds] at c2
  obtain ⟨n, rfl, hn⟩ := c2
  exact ⟨⟨n, s, ns⟩, ⟨hn, hns, hA, hS⟩, rfl⟩

theorem obligations_elems_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (obs : List Obligation),
      (∀ o ∈ obs, ObligationWF o) →
        elemViolations tag obligationTy obligationTy p i (obs.map obligationLayout) = []
  | _, [], _ => rfl
  | i, o :: obs, h => by
    simp only [List.map_cons, elemViolations, ite_self, List.append_eq_nil_iff]
    exact
      ⟨obligation_layout_ok o (h o (by simp)),
        obligations_elems_ok tag p (i + 1) obs fun x hx => h x (by simp [hx])⟩

theorem obligations_elems_of_ok (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List Value),
      keysAscendList xs = true →
        elemViolations tag obligationTy obligationTy p i xs = [] →
        ∃ obs : List Obligation, xs = obs.map obligationLayout ∧ ∀ o ∈ obs, ObligationWF o
  | _, [], _, _ => ⟨[], rfl, by simp⟩
  | i, x :: xs, hk, h => by
    simp only [keysAscendList, Bool.and_eq_true] at hk
    simp only [elemViolations, ite_self, List.append_eq_nil_iff] at h
    obtain ⟨o, ho, rfl⟩ := obligation_of_ok hk.1 h.1
    obtain ⟨obs, rfl, hobs⟩ := obligations_elems_of_ok tag p (i + 1) xs hk.2 h.2
    exact ⟨o :: obs, rfl, by simpa [ho] using hobs⟩

theorem atPath_name (o : Obligation) :
    atPath ["name"] (obligationLayout o) = some (.str o.name) := by
  simp [atPath, obligationLayout, List.lookup]

theorem repeats_iff (p : List PathSeg) :
    ∀ (i : Nat) (seen : List String) (obs : List Obligation),
      nameRepeatsSpec p ["name"] i seen (obs.map obligationLayout) = [] ↔
        (obs.map (·.name)).Nodup ∧ ∀ n ∈ obs.map (·.name), n ∉ seen
  | _, _, [] => by simp [nameRepeatsSpec]
  | i, seen, o :: obs => by
    have ih := repeats_iff p (i + 1) (o.name :: seen) obs
    simp only [List.map_cons, nameRepeatsSpec, atPath_name]
    by_cases h : o.name ∈ seen
    · simp [h]
    · simp only [h, ite_false, List.nil_append, ih, List.nodup_cons]
      constructor
      · rintro ⟨hnd, hall⟩
        refine ⟨⟨fun hm => hall _ hm List.mem_cons_self, hnd⟩, ?_⟩
        intro n hn hs
        rcases List.mem_cons.mp hn with rfl | hn
        · exact h hs
        · exact hall n hn (List.mem_cons_of_mem _ hs)
      · rintro ⟨⟨hno, hnd⟩, hall⟩
        refine ⟨hnd, fun n hn hm => ?_⟩
        rcases List.mem_cons.mp hm with rfl | hs
        · exact hno hn
        · exact hall n (List.mem_cons_of_mem _ hn) hs

/-! ## Compat (one leaf) -/

theorem status_of_axioms {st : String} {ns : List String} (h : StatusAxioms st ns) :
    ∃ s : Status, statusText s = st := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨.proven, rfl⟩
  · exact ⟨.«open», rfl⟩
  · exact ⟨.trusts, rfl⟩

theorem compat_layout_ok {tag : String} {p : List PathSeg} (c : Option Compat)
    (h : ∀ x, c = some x → CompatWF x) :
    violations tag (.scalar [.null, .obj] .compat) p (compatLayout c) = [] := by
  cases c with
  | none => simp [violations, resolveSpec, compatLayout, leafSpec, kindOf, ruleHolds]
  | some x =>
    obtain ⟨⟨hax, hasc, hst⟩, hv⟩ := h x rfl
    have hr :
      ruleHolds .compat
        (.obj
          [("axioms", namesLayout x.axioms), ("status", .str (statusText x.status)),
            ("version", .str (toString x.version))]) :=
      .inr ⟨statusText x.status, x.axioms, x.version, rfl, hax, hasc, hst, hv⟩
    simp [violations, resolveSpec, compatLayout, leafSpec, kindOf, hr]

theorem compat_of_ok {tag : String} {p : List PathSeg} {v : Value}
    (h : violations tag (.scalar [.null, .obj] .compat) p v = []) :
    ∃ c, (∀ x, c = some x → CompatWF x) ∧ v = compatLayout c := by
  have hr := scalar_ok (t := .scalar [.null, .obj] .compat) rfl h
  rcases hr with rfl | ⟨st, ns, x, rfl, hax, hasc, hst, hv⟩
  · exact ⟨none, by simp, rfl⟩
  · obtain ⟨s, rfl⟩ := status_of_axioms hst
    exact ⟨some ⟨x, s, ns⟩, by simpa [CompatWF, AxiomsWF] using ⟨⟨hax, hasc, hst⟩, hv⟩, rfl⟩

/-! ## Operations, notices, removed records -/

theorem keys_of_mem :
    ∀ {ms : List (String × Value)} {k : String} {v : Value},
      keysAscendMembers ms = true → (k, v) ∈ ms → keysAscend v = true
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | (k', v') :: ms, k, v, h, hm => by
    simp only [keysAscendMembers, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with he | hm
    · obtain ⟨-, rfl⟩ := Prod.mk.inj he
      exact h.1
    · exact keys_of_mem h.2 hm

theorem digest_ok {tag : String} {p : List PathSeg} {d : String} (h : DigestText d) :
    violations tag (.scalar [.str] .digest) p (.str d) = [] := by
  simp [violations, resolveSpec, leafSpec, kindOf, ruleHolds, h]

theorem module_ok {tag : String} {p : List PathSeg} {m : ModuleId} (h : SpellingFits (toString m)) :
    violations tag (.scalar [.str] .moduleId) p (.str (toString m)) = [] := by
  have hr : ruleHolds .moduleId (.str (toString m)) := ⟨m, rfl, h⟩
  simp [violations, resolveSpec, leafSpec, kindOf, hr]

theorem version_ok {tag : String} {p : List PathSeg} {x : EntryVersion}
    (h : SpellingFits (toString x)) :
    violations tag (.scalar [.str] .version) p (.str (toString x)) = [] := by
  have hr : ruleHolds .version (.str (toString x)) := ⟨x, rfl, h⟩
  simp [violations, resolveSpec, leafSpec, kindOf, hr]

theorem operation_layout_ok {tag : String} {p : List PathSeg} (o : Operation) (h : OperationWF o) :
    violations tag operationTy p (operationLayout o) = [] := by
  rcases o with ⟨m, x, d, obs, c⟩
  obtain ⟨hm, hx, hd, hobs, hnd, hc⟩ := h
  have e1 := compat_layout_ok (tag := tag) (p := p ++ [.key "compat"]) c hc
  have e4 :
    violations tag (.arr [.arr] obligationTy obligationTy (.unique ["name"]))
        (p ++ [.key "obligations"]) (.arr (obs.map obligationLayout)) =
      [] := by
    have e2 := obligations_elems_ok tag (p ++ [.key "obligations"]) 0 obs hobs
    have e3 := (repeats_iff (p ++ [.key "obligations"]) 0 [] obs).mpr ⟨hnd, by simp⟩
    simp [violations, resolveSpec, orderSpec, e2, e3]
  have hmv :
    memberViolations tag
        [("compat", .scalar [.null, .obj] .compat), ("digest", .scalar [.str] .digest),
          ("id", .scalar [.str] .moduleId),
          ("obligations", .arr [.arr] obligationTy obligationTy (.unique ["name"])),
          ("version", .scalar [.str] .version)]
        p
        [("compat", compatLayout c), ("digest", .str d), ("id", .str (toString m)),
          ("obligations", .arr (obs.map obligationLayout)), ("version", .str (toString x))] =
      [] := by
    simp [memberViolations, List.lookup, e1, digest_ok hd, module_ok hm, e4, version_ok hx]
  simp [violations, operationTy, resolveSpec, operationLayout, discSpec, unknownSpec, missingSpec,
    hmv]

theorem operation_of_ok {tag : String} {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations tag operationTy p v = []) : ∃ o, OperationWF o ∧ v = operationLayout o := by
  obtain ⟨ms, rfl, hkeys, hmem, hkm⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons hkeys
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain ⟨a4, r4, rfl, h4⟩ := map_fst_cons h3
  obtain ⟨a5, r5, rfl, h5⟩ := map_fst_cons h4
  obtain rfl : r5 = [] := List.map_eq_nil_iff.mp h5
  have k4 := keys_of_mem hkm (k := "obligations") (v := a4) (by simp)
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2, g3, g4, g5⟩ := hmem
  obtain ⟨c, hc, rfl⟩ := compat_of_ok g1
  have c2 := scalar_ok (t := .scalar [.str] .digest) rfl g2
  simp only [ruleHolds] at c2
  obtain ⟨d, rfl, hd⟩ := c2
  have c3 := scalar_ok (t := .scalar [.str] .moduleId) rfl g3
  simp only [ruleHolds] at c3
  obtain ⟨m, rfl, hm⟩ := c3
  obtain ⟨xs, rfl, hel, hord⟩ :=
    viol_arr (t := .arr [.arr] obligationTy obligationTy (.unique ["name"])) rfl g4
  obtain ⟨obs, rfl, hobs⟩ := obligations_elems_of_ok _ _ 0 xs (by simpa [keysAscend] using k4) hel
  obtain ⟨hnd, -⟩ := (repeats_iff _ 0 [] obs).mp (by simpa [orderSpec] using hord)
  have c5 := scalar_ok (t := .scalar [.str] .version) rfl g5
  simp only [ruleHolds] at c5
  obtain ⟨x, rfl, hx⟩ := c5
  exact ⟨⟨m, x, d, obs, c⟩, ⟨hm, hx, hd, hobs, hnd, hc⟩, rfl⟩

theorem label_ok {tag : String} {p : List PathSeg} {t : String} (h : TextFits 1024 t) :
    violations tag labelTy p (.str t) = [] := by
  simp [violations, labelTy, resolveSpec, leafSpec, kindOf, ruleHolds, h]

theorem notice_layout_ok {tag : String} {p : List PathSeg} (n : Notice) (h : NoticeNodeWF n) :
    violations tag noticeTy p (noticeLayout n) = [] := by
  rcases n with ⟨m, x, r, rep⟩
  obtain ⟨hm, hx, hr, hrep⟩ := h
  have e2 : violations tag (.scalar [.str] .reason) (p ++ [.key "reason"]) (.str r) = [] := by
    simp [violations, resolveSpec, leafSpec, kindOf, ruleHolds, hr]
  have e3 :
    violations tag (.scalar [.null, .str] .versionOrNull) (p ++ [.key "replacement"])
        (replacementLayout rep) =
      [] := by
    cases rep with
    | none => simp [violations, resolveSpec, leafSpec, kindOf, ruleHolds, replacementLayout]
    | some
      y =>
      have hy : ruleHolds .versionOrNull (.str (toString y)) := .inr ⟨y, rfl, hrep y rfl⟩
      simp [violations, resolveSpec, leafSpec, kindOf, replacementLayout, hy]
  have hmv :
    memberViolations tag
        [("id", .scalar [.str] .moduleId), ("reason", .scalar [.str] .reason),
          ("replacement", .scalar [.null, .str] .versionOrNull),
          ("version", .scalar [.str] .version)]
        p
        [("id", .str (toString m)), ("reason", .str r), ("replacement", replacementLayout rep),
          ("version", .str (toString x))] =
      [] := by
    simp [memberViolations, List.lookup, module_ok hm, e2, e3, version_ok hx]
  simp [violations, noticeTy, resolveSpec, noticeLayout, discSpec, unknownSpec, missingSpec, hmv]

theorem notice_of_ok {tag : String} {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations tag noticeTy p v = []) : ∃ n, NoticeNodeWF n ∧ v = noticeLayout n := by
  obtain ⟨ms, rfl, hkeys, hmem, -⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons hkeys
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain ⟨a4, r4, rfl, h4⟩ := map_fst_cons h3
  obtain rfl : r4 = [] := List.map_eq_nil_iff.mp h4
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2, g3, g4⟩ := hmem
  have c1 := scalar_ok (t := .scalar [.str] .moduleId) rfl g1
  simp only [ruleHolds] at c1
  obtain ⟨m, rfl, hm⟩ := c1
  have c2 := scalar_ok (t := .scalar [.str] .reason) rfl g2
  simp only [ruleHolds] at c2
  obtain ⟨r, rfl, hr⟩ := c2
  have c3 := scalar_ok (t := .scalar [.null, .str] .versionOrNull) rfl g3
  simp only [ruleHolds] at c3
  have c4 := scalar_ok (t := .scalar [.str] .version) rfl g4
  simp only [ruleHolds] at c4
  obtain ⟨x, rfl, hx⟩ := c4
  rcases c3 with rfl | ⟨y, rfl, hy⟩
  · exact ⟨⟨m, x, r, none⟩, ⟨hm, hx, hr, by simp⟩, rfl⟩
  · exact ⟨⟨m, x, r, some y⟩, ⟨hm, hx, hr, by simpa using hy⟩, rfl⟩

theorem removed_layout_ok {tag : String} {p : List PathSeg} (r : Removed) (h : RemovedNodeWF r) :
    violations tag removedTy p (removedLayout r) = [] := by
  rcases r with ⟨m, x, d, c, t⟩
  obtain ⟨hm, hx, hd, ht⟩ := h
  have e3 :
    violations tag (.scalar [.str] (.oneOf ["operation"])) (p ++ [.key "kind"]) (.str "operation") =
      [] := by
    simp [violations, resolveSpec, leafSpec, kindOf, ruleHolds]
  have e4 :
    violations tag (.scalar [.str] .commit) (p ++ [.key "last_commit"]) (.str (toString c)) =
      [] := by
    have hc : ruleHolds .commit (.str (toString c)) := ⟨c, rfl⟩
    simp [violations, resolveSpec, leafSpec, kindOf, hc]
  have hmv :
    memberViolations tag
        [("digest", .scalar [.str] .digest), ("id", .scalar [.str] .moduleId),
          ("kind", .scalar [.str] (.oneOf ["operation"])), ("last_commit", .scalar [.str] .commit),
          ("toolchain", labelTy), ("version", .scalar [.str] .version)]
        p
        [("digest", .str d), ("id", .str (toString m)), ("kind", .str "operation"),
          ("last_commit", .str (toString c)), ("toolchain", .str t),
          ("version", .str (toString x))] =
      [] := by
    simp [memberViolations, List.lookup, digest_ok hd, module_ok hm, e3, e4, label_ok ht,
      version_ok hx]
  simp [violations, removedTy, resolveSpec, removedLayout, discSpec, unknownSpec, missingSpec, hmv]

theorem removed_of_ok {tag : String} {p : List PathSeg} {v : Value} (hk : keysAscend v = true)
    (h : violations tag removedTy p v = []) : ∃ r, RemovedNodeWF r ∧ v = removedLayout r := by
  obtain ⟨ms, rfl, hkeys, hmem, -⟩ := obj_plain hk (by decide) h
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons hkeys
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain ⟨a4, r4, rfl, h4⟩ := map_fst_cons h3
  obtain ⟨a5, r5, rfl, h5⟩ := map_fst_cons h4
  obtain ⟨a6, r6, rfl, h6⟩ := map_fst_cons h5
  obtain rfl : r6 = [] := List.map_eq_nil_iff.mp h6
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hmem
  have c1 := scalar_ok (t := .scalar [.str] .digest) rfl g1
  simp only [ruleHolds] at c1
  obtain ⟨d, rfl, hd⟩ := c1
  have c2 := scalar_ok (t := .scalar [.str] .moduleId) rfl g2
  simp only [ruleHolds] at c2
  obtain ⟨m, rfl, hm⟩ := c2
  have c3 := scalar_ok (t := .scalar [.str] (.oneOf ["operation"])) rfl g3
  simp only [ruleHolds, List.mem_singleton] at c3
  obtain ⟨_, rfl, rfl⟩ := c3
  have c4 := scalar_ok (t := .scalar [.str] .commit) rfl g4
  simp only [ruleHolds] at c4
  obtain ⟨c, rfl⟩ := c4
  have c5 := scalar_ok (t := labelTy) rfl g5
  simp only [ruleHolds] at c5
  obtain ⟨t, rfl, ht⟩ := c5
  have c6 := scalar_ok (t := .scalar [.str] .version) rfl g6
  simp only [ruleHolds] at c6
  obtain ⟨x, rfl, hx⟩ := c6
  exact ⟨⟨m, x, d, c, t⟩, ⟨hm, hx, hd, ht⟩, rfl⟩

/-! ## Arrays of operations, notices, removed records -/

theorem keys_op (a b : Operation) :
    keysSpec (operationLayout a) (operationLayout b) =
      some (toString a.id, toString a.version, toString b.id, toString b.version) := by
  simp [keysSpec, strAtSpec, atPath, operationLayout, List.lookup]

theorem misorders_iff (p : List PathSeg) :
    ∀ (i : Nat) (ops : List Operation),
      misordersSpec p i (ops.map operationLayout) = [] ↔ OpsAscend ops
  | _, [] => by simp [misordersSpec, OpsAscend]
  | _, [_] => by simp [misordersSpec, OpsAscend]
  | i, a :: b :: rest => by
    have ih := misorders_iff p (i + 1) (b :: rest)
    simp only [List.map_cons] at ih
    by_cases h :
      IdVersionBefore (toString a.id) (toString a.version) (toString b.id) (toString b.version)
    · simp [misordersSpec, keys_op, OpsAscend, h, ih]
    · simp [misordersSpec, keys_op, OpsAscend, h]

theorem elems_ok_of {α : Type} (t : Ty) (lay : α → Value) (W : α → Prop)
    (hok : ∀ (tag : String) (p : List PathSeg) (x : α), W x → violations tag t p (lay x) = [])
    (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (xs : List α), (∀ x ∈ xs, W x) → elemViolations tag t t p i (xs.map lay) = []
  | _, [], _ => rfl
  | i, x :: xs, h => by
    simp only [List.map_cons, elemViolations, ite_self, List.append_eq_nil_iff]
    exact
      ⟨hok tag _ x (h x (by simp)),
        elems_ok_of t lay W hok tag p (i + 1) xs fun y hy => h y (by simp [hy])⟩

theorem elems_inv_of {α : Type} (t : Ty) (lay : α → Value) (W : α → Prop)
    (hof :
      ∀ (tag : String) (p : List PathSeg) (v : Value),
        keysAscend v = true → violations tag t p v = [] → ∃ x, W x ∧ v = lay x)
    (tag : String) (p : List PathSeg) :
    ∀ (i : Nat) (vs : List Value),
      keysAscendList vs = true →
        elemViolations tag t t p i vs = [] → ∃ xs : List α, vs = xs.map lay ∧ ∀ x ∈ xs, W x
  | _, [], _, _ => ⟨[], rfl, by simp⟩
  | i, v :: vs, hk, h => by
    simp only [keysAscendList, Bool.and_eq_true] at hk
    simp only [elemViolations, ite_self, List.append_eq_nil_iff] at h
    obtain ⟨x, hx, rfl⟩ := hof tag _ v hk.1 h.1
    obtain ⟨xs, rfl, hxs⟩ := elems_inv_of t lay W hof tag p (i + 1) vs hk.2 h.2
    exact ⟨x :: xs, rfl, by simpa [hx] using hxs⟩

/-! ## The index root -/

/-- `IndexSchemaExact`'s layout half: a well-formed node tree has no violation. -/
theorem index_layout_ok (i : IndexFile) (h : IndexNodeWF i) :
    violations "" indexTy [] (indexLayout i) = [] := by
  rcases i with ⟨tc, ops, ns, rs⟩
  obtain ⟨ht, hops, hasc, hns, hrs⟩ := h
  have e1 :
    violations "" (.arr [.arr] noticeTy noticeTy .any) [.key "notices"]
        (.arr (ns.map noticeLayout)) =
      [] := by
    simp [violations, resolveSpec, orderSpec,
      elems_ok_of noticeTy noticeLayout NoticeNodeWF (fun _ _ n hn => notice_layout_ok n hn) "" _ 0
          ns hns]
  have e2 :
    violations "" (.arr [.arr] operationTy operationTy .idVersion) [.key "operations"]
        (.arr (ops.map operationLayout)) =
      [] := by
    simp [violations, resolveSpec, orderSpec, (misorders_iff _ 1 ops).mpr hasc,
      elems_ok_of operationTy operationLayout OperationWF (fun _ _ o ho => operation_layout_ok o ho)
          "" _ 0 ops hops]
  have e3 :
    violations "" (.arr [.arr] removedTy removedTy .any) [.key "removed"]
        (.arr (rs.map removedLayout)) =
      [] := by
    simp [violations, resolveSpec, orderSpec,
      elems_ok_of removedTy removedLayout RemovedNodeWF (fun _ _ r hr => removed_layout_ok r hr) ""
          _ 0 rs hrs]
  have hmv :
    memberViolations ""
        [("notices", .arr [.arr] noticeTy noticeTy .any),
          ("operations", .arr [.arr] operationTy operationTy .idVersion),
          ("removed", .arr [.arr] removedTy removedTy .any), ("toolchain", labelTy)]
        []
        [("notices", .arr (ns.map noticeLayout)), ("operations", .arr (ops.map operationLayout)),
          ("removed", .arr (rs.map removedLayout)), ("schema", .int 1), ("toolchain", .str tc)] =
      [] := by
    simp [memberViolations, List.lookup, e1, e2, e3, label_ok ht]
  simp only [violations, indexTy, resolveSpec, indexLayout, discSpec, List.lookup]
  simp [kindOf, unknownSpec, missingSpec, hmv]

/-- `IndexSchemaExact`'s hard half: a value with no violation is a well-formed node tree's layout.
-/
theorem index_of_ok {v : Value} (hk : keysAscend v = true) (h : violations "" indexTy [] v = []) :
    ∃ i, IndexNodeWF i ∧ v = indexLayout i := by
  obtain ⟨ms, rfl, s, extra, hd, hunk, hmiss, hmem⟩ := viol_obj (t := indexTy) rfl h
  obtain ⟨hsch, rfl, rfl⟩ := disc_ok_int hd
  obtain ⟨hasc, hkm⟩ := keysAscend_obj hk
  have hkeys : ms.map (·.1) = ["notices", "operations", "removed", "schema", "toolchain"] := by
    refine obj_keys ?_ hunk hmiss _ (by decide) ?_ hasc
    · intro k hk'
      simp only [List.mem_singleton] at hk'
      subst hk'
      simp [hsch]
    · intro k
      simp only [List.map, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
      constructor <;> intro hk' <;> rcases hk' with h' | h' | h' | h' | h' <;> subst h' <;> simp
  clear hunk hmiss hd hasc
  obtain ⟨a1, r1, rfl, h1⟩ := map_fst_cons hkeys
  obtain ⟨a2, r2, rfl, h2⟩ := map_fst_cons h1
  obtain ⟨a3, r3, rfl, h3⟩ := map_fst_cons h2
  obtain ⟨a4, r4, rfl, h4⟩ := map_fst_cons h3
  obtain ⟨a5, r5, rfl, h5⟩ := map_fst_cons h4
  obtain rfl : r5 = [] := List.map_eq_nil_iff.mp h5
  simp [List.lookup] at hsch
  subst hsch
  have k1 := keys_of_mem hkm (k := "notices") (v := a1) (by simp)
  have k2 := keys_of_mem hkm (k := "operations") (v := a2) (by simp)
  have k3 := keys_of_mem hkm (k := "removed") (v := a3) (by simp)
  simp [memberViolations, List.lookup] at hmem
  obtain ⟨g1, g2, g3, g5⟩ := hmem
  obtain ⟨xs1, rfl, hel1, -⟩ := viol_arr (t := .arr [.arr] noticeTy noticeTy .any) rfl g1
  obtain ⟨ns, rfl, hns⟩ :=
    elems_inv_of noticeTy noticeLayout NoticeNodeWF (fun _ _ v hk h => notice_of_ok hk h) _ _ 0 xs1
      (by simpa [keysAscend] using k1) hel1
  obtain ⟨xs2, rfl, hel2, hord2⟩ :=
    viol_arr (t := .arr [.arr] operationTy operationTy .idVersion) rfl g2
  obtain ⟨ops, rfl, hops⟩ :=
    elems_inv_of operationTy operationLayout OperationWF (fun _ _ v hk h => operation_of_ok hk h) _
      _ 0 xs2 (by simpa [keysAscend] using k2) hel2
  have hasc := (misorders_iff _ 1 ops).mp (by simpa [orderSpec] using hord2)
  obtain ⟨xs3, rfl, hel3, -⟩ := viol_arr (t := .arr [.arr] removedTy removedTy .any) rfl g3
  obtain ⟨rs, rfl, hrs⟩ :=
    elems_inv_of removedTy removedLayout RemovedNodeWF (fun _ _ v hk h => removed_of_ok hk h) _ _ 0
      xs3 (by simpa [keysAscend] using k3) hel3
  have c5 := scalar_ok (t := labelTy) rfl g5
  simp only [ruleHolds] at c5
  obtain ⟨tc, rfl, ht⟩ := c5
  exact ⟨⟨tc, ops, ns, rs⟩, ⟨ht, hops, hasc, hns, hrs⟩, rfl⟩

end FvdepAudit.Index.Proof
