import FvdepAudit.Judge.Graph.Spec
import FvdepAudit.Judge.Statement.Proof

/-! Proofs: G2's scan (contract `docs/contracts/U7-judge.md` G2) — on an export the reader accepts,
`usesOf` finds a constant's uses (`Uses`), each expression scanned once per export: an expression a
scan skips had its constants found by the scan that took it. -/

namespace FvdepAudit.Judge.Proof

open FvdepCore.Export FvdepCore.Judge FvdepAudit.Export.Spec FvdepAudit.Judge.Spec
  FvdepAudit.Judge.Statement.Spec FvdepAudit.Judge.Graph.Spec

theorem constOf_iff {t : Tables} {k : Nat} {y : Lean.Expr} (hy : t.exprs[k]? = some y)
    (c : Lean.Name) : ConstOf t k c ↔ c ∈ exprConsts y := by
  constructor
  · rintro ⟨x, hx, hc⟩
    rw [hy, Option.some.injEq] at hx
    subst hx
    exact hc
  · exact fun hc => ⟨y, hy, hc⟩

theorem leaf_consts (t : Tables) (c : Lean.Name) :
    c ∈ ([] : List Lean.Name) ↔
      (∃ n ∈ ([] : List Nat), t.names[n]? = some c) ∨ ∃ k ∈ ([] : List Nat), ConstOf t k c :=
  ⟨fun hc => (nomatch hc), fun h =>
    h.elim (fun ⟨_, hn, _⟩ => (nomatch hn)) fun ⟨_, hk, _⟩ => (nomatch hk)⟩

theorem one_name {t : Tables} {n : Nat} {y : Lean.Name} (hy : t.names[n]? = some y)
    (c : Lean.Name) :
    c ∈ [y] ↔ (∃ m ∈ [n], t.names[m]? = some c) ∨ ∃ k ∈ ([] : List Nat), ConstOf t k c := by
  constructor
  · intro hc
    rw [List.mem_singleton.1 hc]
    exact Or.inl ⟨n, List.mem_cons_self, hy⟩
  · rintro (⟨m, hm, hmc⟩ | ⟨_, hk, _⟩)
    · rw [List.mem_singleton.1 hm, hy, Option.some.injEq] at hmc
      rw [← hmc]
      exact List.mem_cons_self
    · exact nomatch hk

theorem name_kid {t : Tables} {s e : Nat} {y : Lean.Name} {z : Lean.Expr}
    (hy : t.names[s]? = some y) (hz : t.exprs[e]? = some z) (c : Lean.Name) :
    c ∈ y :: exprConsts z ↔ (∃ m ∈ [s], t.names[m]? = some c) ∨ ∃ k ∈ [e], ConstOf t k c := by
  constructor
  · intro hc
    rcases List.mem_cons.1 hc with hc | hc
    · rw [hc]
      exact Or.inl ⟨s, List.mem_cons_self, hy⟩
    · exact Or.inr ⟨e, List.mem_cons_self, (constOf_iff hz c).2 hc⟩
  · rintro (⟨m, hm, hmc⟩ | ⟨k, hk, hc⟩)
    · rw [List.mem_singleton.1 hm, hy, Option.some.injEq] at hmc
      rw [← hmc]
      exact List.mem_cons_self
    · rw [List.mem_singleton.1 hk] at hc
      exact List.mem_cons_of_mem _ ((constOf_iff hz c).1 hc)

theorem two_kids {t : Tables} {a b : Nat} {y z : Lean.Expr} (hy : t.exprs[a]? = some y)
    (hz : t.exprs[b]? = some z) (c : Lean.Name) :
    c ∈ exprConsts y ++ exprConsts z ↔
      (∃ n ∈ ([] : List Nat), t.names[n]? = some c) ∨ ∃ k ∈ [a, b], ConstOf t k c := by
  constructor
  · intro hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inr ⟨a, List.mem_cons_self, (constOf_iff hy c).2 hc⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, (constOf_iff hz c).2 hc⟩
  · rintro (⟨_, hn, _⟩ | ⟨k, hk, hc⟩)
    · exact nomatch hn
    · rcases List.mem_cons.1 hk with hk | hk
      · rw [hk] at hc
        exact List.mem_append.2 (Or.inl ((constOf_iff hy c).1 hc))
      · rw [List.mem_singleton.1 hk] at hc
        exact List.mem_append.2 (Or.inr ((constOf_iff hz c).1 hc))

theorem three_kids {t : Tables} {a b d : Nat} {u w z : Lean.Expr} (hu : t.exprs[a]? = some u)
    (hw : t.exprs[b]? = some w) (hz : t.exprs[d]? = some z) (c : Lean.Name) :
    c ∈ exprConsts u ++ exprConsts w ++ exprConsts z ↔
      (∃ n ∈ ([] : List Nat), t.names[n]? = some c) ∨ ∃ k ∈ [a, b, d], ConstOf t k c := by
  constructor
  · intro hc
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · exact Or.inr ⟨a, List.mem_cons_self, (constOf_iff hu c).2 hc⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, (constOf_iff hw c).2 hc⟩
    · exact
        Or.inr
          ⟨d, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
            (constOf_iff hz c).2 hc⟩
  · rintro (⟨_, hn, _⟩ | ⟨k, hk, hc⟩)
    · exact nomatch hn
    · rcases List.mem_cons.1 hk with hk | hk
      · rw [hk] at hc
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ((constOf_iff hu c).1 hc))))
      · rcases List.mem_cons.1 hk with hk | hk
        · rw [hk] at hc
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ((constOf_iff hw c).1 hc))))
        · rw [List.mem_singleton.1 hk] at hc
          exact List.mem_append.2 (Or.inr ((constOf_iff hz c).1 hc))

/-- G2's step at a record = its denoted expression's constants: the record's own names, then its
children's. -/
theorem consts_step {t : Tables} (h : RawOk t) {i : Nat} {x : Lean.Expr} (hx : t.exprs[i]? = some x)
    (c : Lean.Name) :
    c ∈ exprConsts x ↔
      (∃ n ∈ (exprStep t i).1, t.names[n]? = some c) ∨ ∃ k ∈ (exprStep t i).2, ConstOf t k c := by
  obtain ⟨f, hf, hd⟩ := raw_of_expr h hx
  cases f with
  | bvar k =>
    cases hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [] := by simp [exprStep, hf]
    rw [h1, h2]
    exact leaf_consts t c
  | sort l =>
    obtain ⟨_, _, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [] := by simp [exprStep, hf]
    rw [h1, h2]
    exact leaf_consts t c
  | const n us =>
    obtain ⟨y, _, hy, _, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [n] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [] := by simp [exprStep, hf]
    rw [h1, h2]
    exact one_name hy c
  | app a b =>
    obtain ⟨y, z, hy, hz, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [a, b] := by simp [exprStep, hf]
    rw [h1, h2]
    exact two_kids (extract_some hy).2 (extract_some hz).2 c
  | lam n ty b bi =>
    obtain ⟨_, u, w, _, hu, hw, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [ty, b] := by simp [exprStep, hf]
    rw [h1, h2]
    exact two_kids (extract_some hu).2 (extract_some hw).2 c
  | forallE n ty b bi =>
    obtain ⟨_, u, w, _, hu, hw, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [ty, b] := by simp [exprStep, hf]
    rw [h1, h2]
    exact two_kids (extract_some hu).2 (extract_some hw).2 c
  | letE n ty v b nd =>
    obtain ⟨_, u, w, z, _, hu, hw, hz, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [ty, v, b] := by simp [exprStep, hf]
    rw [h1, h2]
    exact three_kids (extract_some hu).2 (extract_some hw).2 (extract_some hz).2 c
  | proj s idx e =>
    obtain ⟨y, z, hy, hz, rfl⟩ := hd
    have h1 : (exprStep t i).1 = [s] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [e] := by simp [exprStep, hf]
    rw [h1, h2]
    exact name_kid hy (extract_some hz).2 c
  | natVal v =>
    cases hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [] := by simp [exprStep, hf]
    rw [h1, h2]
    exact leaf_consts t c
  | strVal s =>
    cases hd
    have h1 : (exprStep t i).1 = [] := by simp [exprStep, hf]
    have h2 : (exprStep t i).2 = [] := by simp [exprStep, hf]
    rw [h1, h2]
    exact leaf_consts t c

/-- A record's children are earlier records (the reader's denotation reads a prefix). -/
theorem kids_lt {t : Tables} (h : RawOk t) {i k : Nat} (hk : k ∈ (exprStep t i).2) : k < i := by
  cases hf : t.rawExprs[i]? with
  | none => simp [exprStep, hf] at hk
  | some f =>
    obtain ⟨_, _, hd⟩ := h.expr i f hf
    cases f with
    | bvar _ => simp [exprStep, hf] at hk
    | sort _ => simp [exprStep, hf] at hk
    | const _ _ => simp [exprStep, hf] at hk
    | app a b =>
      obtain ⟨_, _, ha, hb, _⟩ := hd
      have h2 : (exprStep t i).2 = [a, b] := by simp [exprStep, hf]
      rw [h2] at hk
      rcases List.mem_cons.1 hk with hk | hk
      · rw [hk]
        exact (extract_some ha).1
      · rw [List.mem_singleton.1 hk]
        exact (extract_some hb).1
    | lam _ ty b _ =>
      obtain ⟨_, _, _, _, ha, hb, _⟩ := hd
      have h2 : (exprStep t i).2 = [ty, b] := by simp [exprStep, hf]
      rw [h2] at hk
      rcases List.mem_cons.1 hk with hk | hk
      · rw [hk]
        exact (extract_some ha).1
      · rw [List.mem_singleton.1 hk]
        exact (extract_some hb).1
    | forallE _ ty b _ =>
      obtain ⟨_, _, _, _, ha, hb, _⟩ := hd
      have h2 : (exprStep t i).2 = [ty, b] := by simp [exprStep, hf]
      rw [h2] at hk
      rcases List.mem_cons.1 hk with hk | hk
      · rw [hk]
        exact (extract_some ha).1
      · rw [List.mem_singleton.1 hk]
        exact (extract_some hb).1
    | letE _ ty v b _ =>
      obtain ⟨_, _, _, _, _, ha, hv, hb, _⟩ := hd
      have h2 : (exprStep t i).2 = [ty, v, b] := by simp [exprStep, hf]
      rw [h2] at hk
      rcases List.mem_cons.1 hk with hk | hk
      · rw [hk]
        exact (extract_some ha).1
      · rcases List.mem_cons.1 hk with hk | hk
        · rw [hk]
          exact (extract_some hv).1
        · rw [List.mem_singleton.1 hk]
          exact (extract_some hb).1
    | proj _ _ e =>
      obtain ⟨_, _, _, he, _⟩ := hd
      have h2 : (exprStep t i).2 = [e] := by simp [exprStep, hf]
      rw [h2, List.mem_singleton] at hk
      rw [hk]
      exact (extract_some he).1
    | natVal _ => simp [exprStep, hf] at hk
    | strVal _ => simp [exprStep, hf] at hk

/-- A record set closed under children, each record's own names inside `M`: every constant of each
record's expression lies inside `M`. -/
theorem closed_consts {t : Tables} (h : RawOk t) {seen : Std.HashSet Nat} {M : Lean.Name → Prop}
    (hs :
      ∀ i ∈ seen,
        (∀ n ∈ (exprStep t i).1, ∀ c, t.names[n]? = some c → M c) ∧
          ∀ k ∈ (exprStep t i).2, k ∈ seen) :
    ∀ i, i ∈ seen → ∀ c, ConstOf t i c → M c := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rintro hi c ⟨x, hx, hc⟩
    rcases (consts_step h hx c).1 hc with ⟨n, hn, hnc⟩ | ⟨k, hk, hkc⟩
    · exact (hs i hi).1 n hn c hnc
    · exact ih k (kids_lt h hk) ((hs i hi).2 k hk) c hkc

/-- A record's own name is bound + a constant of its expression. -/
theorem direct_const {t : Tables} (h : RawOk t) {i n : Nat} (hn : n ∈ (exprStep t i).1) :
    ∃ c, t.names[n]? = some c ∧ ConstOf t i c := by
  cases hf : t.rawExprs[i]? with
  | none => simp [exprStep, hf] at hn
  | some f =>
    obtain ⟨x, hx, hd⟩ := h.expr i f hf
    have hb : ∃ c, t.names[n]? = some c := by
      cases f with
      | const m _ =>
        obtain ⟨y, _, hy, _, _⟩ := hd
        have h1 : (exprStep t i).1 = [m] := by simp [exprStep, hf]
        rw [h1, List.mem_singleton] at hn
        rw [hn]
        exact ⟨y, hy⟩
      | proj s _ _ =>
        obtain ⟨y, _, hy, _, _⟩ := hd
        have h1 : (exprStep t i).1 = [s] := by simp [exprStep, hf]
        rw [h1, List.mem_singleton] at hn
        rw [hn]
        exact ⟨y, hy⟩
      | _ => simp [exprStep, hf] at hn
    obtain ⟨c, hc⟩ := hb
    exact ⟨c, hc, x, hx, (consts_step h hx c).2 (Or.inl ⟨n, hn, hc⟩)⟩

/-- A child's constant is a constant of its parent. -/
theorem kid_const {t : Tables} (h : RawOk t) {i k : Nat} {c : Lean.Name} (hk : k ∈ (exprStep t i).2)
    (hc : ConstOf t k c) : ConstOf t i c := by
  cases hf : t.rawExprs[i]? with
  | none => simp [exprStep, hf] at hk
  | some f =>
    obtain ⟨x, hx, _⟩ := h.expr i f hf
    exact ⟨x, hx, (consts_step h hx c).2 (Or.inr ⟨k, hk, hc⟩)⟩

theorem collect_nil (t : Tables) (fuel : Nat) (seen : Std.HashSet Nat) (acc : List Nat) :
    collect t fuel [] seen acc = some (acc, fuel, seen) := by cases fuel <;> rfl

/-- `collect`, sound: each name it adds is a constant of an expression it was handed. -/
theorem collect_sound {t : Tables} (h : RawOk t) :
    ∀ (fuel : Nat) (todo : List Nat) (seen : Std.HashSet Nat) (acc acc' : List Nat) (f : Nat)
      (seen' : Std.HashSet Nat),
      collect t fuel todo seen acc = some (acc', f, seen') →
        ∀ n ∈ acc', n ∈ acc ∨ ∃ c, t.names[n]? = some c ∧ ∃ j ∈ todo, ConstOf t j c := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo seen acc acc' f seen' hc n hn
    cases todo with
    | nil =>
      simp only [collect_nil, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, _, _⟩ := hc
      exact Or.inl hn
    | cons _ _ => simp [collect] at hc
  | succ fuel ih =>
    intro todo seen acc acc' f seen' hc n hn
    cases todo with
    | nil =>
      simp only [collect_nil, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, _, _⟩ := hc
      exact Or.inl hn
    | cons i rest =>
      simp only [collect] at hc
      by_cases hi : seen.contains i = true
      · simp only [hi, ↓reduceIte] at hc
        rcases ih rest seen acc acc' f seen' hc n hn with hn | ⟨c, hc', j, hj, hjc⟩
        · exact Or.inl hn
        · exact Or.inr ⟨c, hc', j, List.mem_cons_of_mem i hj, hjc⟩
      · simp only [hi] at hc
        rcases hst : exprStep t i with ⟨ns, kids⟩
        simp only [hst] at hc
        rcases ih (kids ++ rest) (seen.insert i) (ns ++ acc) acc' f seen' hc n hn with hn |
          ⟨c, hc', j, hj, hjc⟩
        · rcases List.mem_append.1 hn with hn | hn
          · have hn' : n ∈ (exprStep t i).1 := by
              rw [hst]
              exact hn
            obtain ⟨c, hc', hic⟩ := direct_const h hn'
            exact Or.inr ⟨c, hc', i, List.mem_cons_self, hic⟩
          · exact Or.inl hn
        · rcases List.mem_append.1 hj with hj | hj
          · have hj' : j ∈ (exprStep t i).2 := by
              rw [hst]
              exact hj
            exact Or.inr ⟨c, hc', i, List.mem_cons_self, kid_const h hj' hjc⟩
          · exact Or.inr ⟨c, hc', j, List.mem_cons_of_mem i hj, hjc⟩

/-- `collect`, closed: each expression seen has its own names added (or inside `P`) + its children
seen or still to scan ⇒ at the end every expression seen has its children seen; everything handed
ends seen. -/
theorem collect_closed {t : Tables} (P : Nat → Prop) :
    ∀ (fuel : Nat) (todo : List Nat) (seen : Std.HashSet Nat) (acc acc' : List Nat) (f : Nat)
      (seen' : Std.HashSet Nat),
      collect t fuel todo seen acc = some (acc', f, seen') →
        (∀ i ∈ seen,
          (∀ n ∈ (exprStep t i).1, n ∈ acc ∨ P n) ∧ ∀ k ∈ (exprStep t i).2, k ∈ seen ∨ k ∈ todo) →
        (∀ i ∈ seen',
            (∀ n ∈ (exprStep t i).1, n ∈ acc' ∨ P n) ∧ ∀ k ∈ (exprStep t i).2, k ∈ seen') ∧
          (∀ j ∈ todo, j ∈ seen') ∧ (∀ i ∈ seen, i ∈ seen') ∧ ∀ n ∈ acc, n ∈ acc' := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo seen acc acc' f seen' hc hs
    cases todo with
    | nil =>
      simp only [collect_nil, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, _, rfl⟩ := hc
      refine
        ⟨fun i hi => ⟨(hs i hi).1, fun k hk => ?_⟩, fun j hj => (nomatch hj), fun i hi => hi,
          fun n hn => hn⟩
      rcases (hs i hi).2 k hk with hk | hk
      · exact hk
      · exact nomatch hk
    | cons _ _ => simp [collect] at hc
  | succ fuel ih =>
    intro todo seen acc acc' f seen' hc hs
    cases todo with
    | nil =>
      simp only [collect_nil, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, _, rfl⟩ := hc
      refine
        ⟨fun i hi => ⟨(hs i hi).1, fun k hk => ?_⟩, fun j hj => (nomatch hj), fun i hi => hi,
          fun n hn => hn⟩
      rcases (hs i hi).2 k hk with hk | hk
      · exact hk
      · exact nomatch hk
    | cons i rest =>
      simp only [collect] at hc
      by_cases hi : seen.contains i = true
      · simp only [hi, ↓reduceIte] at hc
        have hi' : i ∈ seen := Std.HashSet.mem_iff_contains.2 hi
        have hs' :
          ∀ i' ∈ seen,
            (∀ n ∈ (exprStep t i').1, n ∈ acc ∨ P n) ∧
              ∀ k ∈ (exprStep t i').2, k ∈ seen ∨ k ∈ rest := by
          intro i' hi''
          refine ⟨(hs i' hi'').1, fun k hk => ?_⟩
          rcases (hs i' hi'').2 k hk with hk | hk
          · exact Or.inl hk
          · rcases List.mem_cons.1 hk with hk | hk
            · rw [hk]
              exact Or.inl hi'
            · exact Or.inr hk
        obtain ⟨h1, h2, h3, h4⟩ := ih rest seen acc acc' f seen' hc hs'
        refine ⟨h1, fun j hj => ?_, h3, h4⟩
        rcases List.mem_cons.1 hj with hj | hj
        · rw [hj]
          exact h3 i hi'
        · exact h2 j hj
      · simp only [hi] at hc
        rcases hst : exprStep t i with ⟨ns, kids⟩
        simp only [hst] at hc
        have hii : i ∈ seen.insert i := Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true i))
        have hs' :
          ∀ i' ∈ seen.insert i,
            (∀ n ∈ (exprStep t i').1, n ∈ ns ++ acc ∨ P n) ∧
              ∀ k ∈ (exprStep t i').2, k ∈ seen.insert i ∨ k ∈ kids ++ rest := by
          intro i' hi'
          rcases Std.HashSet.mem_insert.1 hi' with he | hi'
          · rw [← beq_iff_eq.1 he, hst]
            exact
              ⟨fun n hn => Or.inl (List.mem_append_left _ hn), fun k hk =>
                Or.inr (List.mem_append_left _ hk)⟩
          · refine ⟨fun n hn => ?_, fun k hk => ?_⟩
            · rcases (hs i' hi').1 n hn with hn | hn
              · exact Or.inl (List.mem_append_right _ hn)
              · exact Or.inr hn
            · rcases (hs i' hi').2 k hk with hk | hk
              · exact Or.inl (Std.HashSet.mem_insert.2 (Or.inr hk))
              · rcases List.mem_cons.1 hk with hk | hk
                · rw [hk]
                  exact Or.inl hii
                · exact Or.inr (List.mem_append_right _ hk)
        obtain ⟨h1, h2, h3, h4⟩ := ih (kids ++ rest) (seen.insert i) (ns ++ acc) acc' f seen' hc hs'
        refine
          ⟨h1, fun j hj => ?_, fun i' hi' => h3 i' (Std.HashSet.mem_insert.2 (Or.inr hi')),
            fun n hn => h4 n (List.mem_append_right _ hn)⟩
        rcases List.mem_cons.1 hj with hj | hj
        · rw [hj]
          exact h3 i hii
        · exact h2 j (List.mem_append_right _ hj)

theorem uses_one {t : Tables} {ty : Nat} {c : Lean.Name} :
    ConstOf t ty c ↔ (∃ n ∈ ([] : List Nat), t.names[n]? = some c) ∨ ∃ j ∈ [ty], ConstOf t j c := by
  constructor
  · exact fun h => Or.inr ⟨ty, List.mem_cons_self, h⟩
  · rintro (⟨_, hn, _⟩ | ⟨j, hj, h⟩)
    · exact nomatch hn
    · rw [List.mem_singleton.1 hj] at h
      exact h

theorem uses_two {t : Tables} {ty v : Nat} {c : Lean.Name} :
    ConstOf t ty c ∨ ConstOf t v c ↔
      (∃ n ∈ ([] : List Nat), t.names[n]? = some c) ∨ ∃ j ∈ [ty, v], ConstOf t j c := by
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨ty, List.mem_cons_self, h⟩
    · exact Or.inr ⟨v, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
  · rintro (⟨_, hn, _⟩ | ⟨j, hj, h⟩)
    · exact nomatch hn
    · rcases List.mem_cons.1 hj with hj | hj
      · rw [hj] at h
        exact Or.inl h
      · rw [List.mem_singleton.1 hj] at h
        exact Or.inr h

/-- G2: `entryUses` lists exactly a constant's uses — its direct names + the expressions whose
constants count. -/
theorem entryUses_spec (t : Tables) (e : Entry) (c : Lean.Name) :
    Uses t e c ↔
      (∃ n ∈ (entryUses e).1, t.names[n]? = some c) ∨ ∃ j ∈ (entryUses e).2, ConstOf t j c := by
  cases e with
  | «axiom»_ _ _ ty => exact uses_one
  | defn _ _ _ _ _ ty v => exact uses_two
  | thm _ _ _ ty v => exact uses_two
  | «opaque»_ _ _ _ ty v => exact uses_two
  | quot _ _ _ ty => exact uses_one
  | induct
    x =>
    show
      ConstOf t x.type c ∨ (∃ i ∈ x.ctors ++ x.all, t.names[i]? = some c) ↔
        (∃ n ∈ x.ctors ++ x.all, t.names[n]? = some c) ∨ ∃ j ∈ [x.type], ConstOf t j c
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨x.type, List.mem_cons_self, h⟩
      · exact Or.inl h
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inr h
      · rw [List.mem_singleton.1 hj] at h
        exact Or.inl h
  | ctor
    k =>
    show
      ConstOf t k.type c ∨ t.names[k.induct]? = some c ↔
        (∃ n ∈ [k.induct], t.names[n]? = some c) ∨ ∃ j ∈ [k.type], ConstOf t j c
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨k.type, List.mem_cons_self, h⟩
      · exact Or.inl ⟨k.induct, List.mem_cons_self, h⟩
    · rintro (⟨n, hn, h⟩ | ⟨j, hj, h⟩)
      · rw [List.mem_singleton.1 hn] at h
        exact Or.inr h
      · rw [List.mem_singleton.1 hj] at h
        exact Or.inl h
  | recursor
    r =>
    show
      ConstOf t r.type c ∨ (∃ q ∈ r.rules, t.names[q.ctor]? = some c ∨ ConstOf t q.rhs c) ↔
        (∃ n ∈ r.rules.map (·.ctor), t.names[n]? = some c) ∨
          ∃ j ∈ r.type :: r.rules.map (·.rhs), ConstOf t j c
    constructor
    · rintro (h | ⟨q, hq, h | h⟩)
      · exact Or.inr ⟨r.type, List.mem_cons_self, h⟩
      · exact Or.inl ⟨q.ctor, List.mem_map.2 ⟨q, hq, rfl⟩, h⟩
      · exact Or.inr ⟨q.rhs, List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, hq, rfl⟩), h⟩
    · rintro (⟨n, hn, h⟩ | ⟨j, hj, h⟩)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hn
        exact Or.inr ⟨q, hq, Or.inl h⟩
      · rcases List.mem_cons.1 hj with hj | hj
        · rw [hj] at h
          exact Or.inl h
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
          exact Or.inr ⟨q, hq, Or.inr h⟩

/-- G2: one constant's scan — the names `usesOf` returns are uses; every use is returned or was
already inside `N` (found by an earlier scan of the same export: the `seen` invariant), and the
invariant holds for the expressions seen after it. -/
theorem usesOf_closed {t : Tables} (h : RawOk t) {e : Entry} {fuel : Nat} {seen : Std.HashSet Nat}
    {L : List Lean.Name} {f : Nat} {s : Std.HashSet Nat} (N : Lean.Name → Prop)
    (hu : usesOf t e fuel seen = some (L, f, s))
    (hs :
      ∀ i ∈ seen,
        (∀ n ∈ (exprStep t i).1, ∀ c, t.names[n]? = some c → N c) ∧
          ∀ k ∈ (exprStep t i).2, k ∈ seen) :
    (∀ c ∈ L, Uses t e c) ∧
      (∀ c, Uses t e c → c ∈ L ∨ N c) ∧
      ∀ i ∈ s,
        (∀ n ∈ (exprStep t i).1, ∀ c, t.names[n]? = some c → c ∈ L ∨ N c) ∧
          ∀ k ∈ (exprStep t i).2, k ∈ s := by
  unfold usesOf at hu
  rcases hst : entryUses e with ⟨ns, roots⟩
  simp only [hst] at hu
  rcases hc : collect t fuel roots seen [] with _ | ⟨found, f', s'⟩
  · simp [hc] at hu
  · simp only [hc, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, _, rfl⟩ := hu
    have hsound := collect_sound h fuel roots seen [] found f' s' hc
    obtain ⟨hcl, hroots, _, _⟩ :=
      collect_closed (fun n => ∀ c, t.names[n]? = some c → N c) fuel roots seen [] found f' s' hc
        fun i hi => ⟨fun n hn => Or.inr ((hs i hi).1 n hn), fun k hk => Or.inl ((hs i hi).2 k hk)⟩
    have hspec := entryUses_spec t e
    rw [hst] at hspec
    have h3 :
      ∀ i ∈ s',
        (∀ n ∈ (exprStep t i).1,
            ∀ c, t.names[n]? = some c → c ∈ (ns ++ found).filterMap (t.names[·]?) ∨ N c) ∧
          ∀ k ∈ (exprStep t i).2, k ∈ s' := by
      intro i hi
      refine ⟨fun n hn c hnc => ?_, (hcl i hi).2⟩
      rcases (hcl i hi).1 n hn with hn' | hn'
      · exact Or.inl (List.mem_filterMap.2 ⟨n, List.mem_append_right _ hn', hnc⟩)
      · exact Or.inr (hn' c hnc)
    refine ⟨fun c hcL => ?_, fun c hcu => ?_, h3⟩
    · obtain ⟨n, hn, hnc⟩ := List.mem_filterMap.1 hcL
      rcases List.mem_append.1 hn with hn | hn
      · exact (hspec c).2 (Or.inl ⟨n, hn, hnc⟩)
      · rcases hsound n hn with hn | ⟨c', hc', j, hj, hjc⟩
        · exact nomatch hn
        · rw [hnc, Option.some.injEq] at hc'
          rw [hc']
          exact (hspec c').2 (Or.inr ⟨j, hj, hjc⟩)
    · rcases (hspec c).1 hcu with ⟨n, hn, hnc⟩ | ⟨j, hj, hjc⟩
      · exact Or.inl (List.mem_filterMap.2 ⟨n, List.mem_append_left _ hn, hnc⟩)
      · exact closed_consts h h3 j (hroots j hj) c hjc

end FvdepAudit.Judge.Proof
