import FvdepAudit.Export.Proof.Tables
import FvdepAudit.Protocol.Proof.Val

/-! Proofs: the export reader's stage 1 + header (contract `docs/contracts/U5b-oracle.md` X1–X3):
each parser accepts exactly its layout (`parseLine v = .ok r ↔ v = rawLayout r`), `mdata` alone
is outside the profile, the header's class. -/

namespace FvdepAudit.Export.Proof

open FvdepCore.Json FvdepCore.Export FvdepAudit.Export.Spec

/-! ## Scalars + lists -/

theorem natR_nat (w : String) (n : Nat) : natR w (nat n) = .ok n := by simp [natR, nat]

theorem nat_of_natR {w : String} {v : Value} {n : Nat} (h : natR w v = .ok n) : nat n = v := by
  unfold natR at h
  split at h
  · rename_i m
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      simp only [nat]
      congr 1
      omega
    · simp [bad] at h
  · simp [bad] at h

theorem strR_str (w s : String) : strR w (.str s) = .ok s := rfl

theorem str_of_strR {w : String} {v : Value} {s : String} (h : strR w v = .ok s) : .str s = v := by
  unfold strR at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp [bad] at h

theorem boolR_bool (w : String) (b : Bool) : boolR w (.bool b) = .ok b := rfl

theorem bool_of_boolR {w : String} {v : Value} {b : Bool} (h : boolR w v = .ok b) :
    .bool b = v := by
  unfold boolR at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp [bad] at h

theorem mapM_layout {α : Type} {f : Value → R α} {g : α → Value} (hf : ∀ x, f (g x) = .ok x) :
    ∀ xs : List α, (xs.map g).mapM f = .ok xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.mapM_cons, hf x, mapM_layout hf xs]
    rfl

theorem mapM_inverse {α : Type} {f : Value → R α} {g : α → Value}
    (hf : ∀ {v x}, f v = .ok x → g x = v) :
    ∀ {vs : List Value} {xs : List α}, vs.mapM f = .ok xs → xs.map g = vs
  | [], xs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | v :: vs, xs, h => by
    rw [List.mapM_cons, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨xs', hxs, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [hf hx, mapM_inverse hf hxs]

theorem natsR_nats (w : String) (ns : List Nat) : natsR w (nats ns) = .ok ns :=
  mapM_layout (natR_nat w) ns

theorem nats_of_natsR {w : String} {v : Value} {ns : List Nat} (h : natsR w v = .ok ns) :
    nats ns = v := by
  unfold natsR at h
  split at h
  · simp only [nats, mapM_inverse nat_of_natR h]
  · simp [bad] at h

/-! ## Names, levels, expressions -/

theorem nameF_layout (f : NameF) : nameF (nameForm f).1 (nameForm f).2 = .ok f := by
  cases f <;> simp [nameF, nameForm, natR_nat, strR_str, bind, Except.bind, pure, Except.pure]

theorem nameForm_of_nameF {k : String} {p : Value} {f : NameF} (h : nameF k p = .ok f) :
    nameForm f = (k, p) := by
  unfold nameF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [nameForm, nat_of_natR ha, str_of_strR hb]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [nameForm, nat_of_natR ha, nat_of_natR hb]
  · simp [bad] at h

theorem levelF_layout (f : LevelF) : levelF (levelForm f).1 (levelForm f).2 = .ok f := by
  cases f <;> simp [levelF, levelForm, natR_nat, bind, Except.bind, pure, Except.pure]

theorem levelForm_of_levelF {k : String} {p : Value} {f : LevelF} (h : levelF k p = .ok f) :
    levelForm f = (k, p) := by
  unfold levelF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [levelForm, nat_of_natR ha]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [levelForm, nat_of_natR ha, nat_of_natR hb]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [levelForm, nat_of_natR ha, nat_of_natR hb]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [levelForm, nat_of_natR ha]
  · simp [bad] at h

theorem binderInfoR_layout (bi : Lean.BinderInfo) : binderInfoR (binderInfoLayout bi) = .ok bi := by
  cases bi <;> rfl

theorem binderInfo_of_binderInfoR {v : Value} {bi : Lean.BinderInfo} (h : binderInfoR v = .ok bi) :
    binderInfoLayout bi = v := by
  unfold binderInfoR at h
  split at h <;> simp only [Except.ok.injEq, bad, reduceCtorEq] at h <;> subst h <;> rfl

theorem exprLo_layout (f : ExprF) (h : (exprForm f).1 < "ie") :
    exprLo (exprForm f).1 (exprForm f).2 = .ok f := by
  cases f <;>
    simp_all [exprLo, exprForm, binderLayout, natR_nat, natsR_nats, binderInfoR_layout, bind,
      Except.bind, pure, Except.pure]

theorem exprHi_layout (f : ExprF) (h : ¬(exprForm f).1 < "ie") :
    exprHi (exprForm f).1 (exprForm f).2 = .ok f := by
  cases f <;>
    simp_all [exprHi, exprForm, binderLayout, natR_nat, boolR_bool, binderInfoR_layout, need,
      String.toList_ofList, FvdepCore.Ids.parseNat_decimal, bind, Except.bind, pure, Except.pure]

theorem exprForm_of_exprLo {k : String} {p : Value} {f : ExprF} (h : exprLo k p = .ok f) :
    exprForm f = (k, p) ∧ k < "ie" := by
  unfold exprLo at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [exprForm, nat_of_natR ha, nat_of_natR hb]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [exprForm, nat_of_natR ha]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [exprForm, nat_of_natR ha, nats_of_natsR hb]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    simp [exprForm, binderLayout, nat_of_natR ha, nat_of_natR hb, nat_of_natR hc,
      binderInfo_of_binderInfoR hd]
  · simp [bad] at h

theorem exprForm_of_exprHi {k : String} {p : Value} {f : ExprF} (h : exprHi k p = .ok f) :
    exprForm f = (k, p) ∧ ¬k < "ie" := by
  unfold exprHi at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    simp [exprForm, binderLayout, nat_of_natR ha, nat_of_natR hb, nat_of_natR hc,
      binderInfo_of_binderInfoR hd]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, rfl⟩ := h
    simp [exprForm, nat_of_natR ha, nat_of_natR hb, nat_of_natR hc, nat_of_natR hd,
      bool_of_boolR he]
  · simp [outside] at h
  · simp only [bind_ok, need_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [exprForm, FvdepAudit.Protocol.Proof.decimal_of_parseNat ha, String.ofList_toList]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
    simp [exprForm, nat_of_natR ha, nat_of_natR hb, nat_of_natR hc]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [exprForm, nat_of_natR ha]
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [exprForm]
  · simp [bad] at h

/-! ## Declarations -/

theorem hintsR_layout (x : Hints) : hintsR (hintsLayout x) = .ok x := by
  cases x
  · rfl
  · rfl
  · rename_i k
    have hk : k.toNat ≤ 4294967295 := by
      have := k.toNat_lt
      omega
    simp [hintsR, hintsLayout, natR_nat, hk, bind, Except.bind, pure, Except.pure]

theorem hints_of_hintsR {v : Value} {x : Hints} (h : hintsR v = .ok x) : hintsLayout x = v := by
  unfold hintsR at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp only [bind_ok] at h
    obtain ⟨a, ha, h⟩ := h
    split at h
    · rename_i hle
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have e : a.toUInt32.toNat = a := by
        simp
        omega
      simp [hintsLayout, ← nat_of_natR ha, e]
    · simp [bad] at h
  · simp [bad] at h

theorem safetyR_layout (x : Safety) : safetyR (safetyLayout x) = .ok x := by cases x <;> rfl

theorem safety_of_safetyR {v : Value} {x : Safety} (h : safetyR v = .ok x) :
    safetyLayout x = v := by
  unfold safetyR at h
  split at h <;> simp only [Except.ok.injEq, bad, reduceCtorEq] at h <;> subst h <;> rfl

theorem quotKindR_layout (x : QuotKind) : quotKindR (quotKindLayout x) = .ok x := by cases x <;> rfl

theorem quotKind_of_quotKindR {v : Value} {x : QuotKind} (h : quotKindR v = .ok x) :
    quotKindLayout x = v := by
  unfold quotKindR at h
  split at h <;> simp only [Except.ok.injEq, bad, reduceCtorEq] at h <;> subst h <;> rfl

theorem typeF_layout (x : TypeF) : typeF (typeLayout x) = .ok x := by
  cases x
  simp [typeF, typeLayout, natR_nat, natsR_nats, boolR_bool, bind, Except.bind, pure, Except.pure]

theorem type_of_typeF {v : Value} {x : TypeF} (h : typeF v = .ok x) : typeLayout x = v := by
  unfold typeF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain
      ⟨a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, a6, h6, a7, h7, a8, h8, a9, h9, a10, h10, a11, h11,
        rfl⟩ :=
      h
    simp [typeLayout, nats_of_natsR h1, nats_of_natsR h2, bool_of_boolR h3, bool_of_boolR h4,
      bool_of_boolR h5, nats_of_natsR h6, nat_of_natR h7, nat_of_natR h8, nat_of_natR h9,
      nat_of_natR h10, nat_of_natR h11]
  · simp [bad] at h

theorem ctorF_layout (x : CtorF) : ctorF (ctorLayout x) = .ok x := by
  cases x
  simp [ctorF, ctorLayout, natR_nat, natsR_nats, boolR_bool, bind, Except.bind, pure, Except.pure]

theorem ctor_of_ctorF {v : Value} {x : CtorF} (h : ctorF v = .ok x) : ctorLayout x = v := by
  unfold ctorF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, a6, h6, a7, h7, a8, h8, rfl⟩ := h
    simp [ctorLayout, nat_of_natR h1, nat_of_natR h2, bool_of_boolR h3, nats_of_natsR h4,
      nat_of_natR h5, nat_of_natR h6, nat_of_natR h7, nat_of_natR h8]
  · simp [bad] at h

theorem ruleF_layout (x : RuleF) : ruleF (ruleLayout x) = .ok x := by
  cases x
  simp [ruleF, ruleLayout, natR_nat, bind, Except.bind, pure, Except.pure]

theorem rule_of_ruleF {v : Value} {x : RuleF} (h : ruleF v = .ok x) : ruleLayout x = v := by
  unfold ruleF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a1, h1, a2, h2, a3, h3, rfl⟩ := h
    simp [ruleLayout, nat_of_natR h1, nat_of_natR h2, nat_of_natR h3]
  · simp [bad] at h

theorem rulesR_layout (rs : List RuleF) : rulesR (.arr (rs.map ruleLayout)) = .ok rs :=
  mapM_layout ruleF_layout rs

theorem rules_of_rulesR {v : Value} {rs : List RuleF} (h : rulesR v = .ok rs) :
    .arr (rs.map ruleLayout) = v := by
  unfold rulesR at h
  split at h
  · simp only [mapM_inverse rule_of_ruleF h]
  · simp [bad] at h

theorem recF_layout (x : RecF) : recF (recLayout x) = .ok x := by
  cases x
  simp [recF, recLayout, natR_nat, natsR_nats, boolR_bool, rulesR_layout, bind, Except.bind, pure,
    Except.pure]

theorem rec_of_recF {v : Value} {x : RecF} (h : recF v = .ok x) : recLayout x = v := by
  unfold recF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain
      ⟨a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, a6, h6, a7, h7, a8, h8, a9, h9, a10, h10, a11, h11,
        rfl⟩ :=
      h
    simp [recLayout, nats_of_natsR h1, bool_of_boolR h2, bool_of_boolR h3, nats_of_natsR h4,
      nat_of_natR h5, nat_of_natR h6, nat_of_natR h7, nat_of_natR h8, nat_of_natR h9,
      rules_of_rulesR h10, nat_of_natR h11]
  · simp [bad] at h

theorem declF_layout (d : DeclF) : declF (declForm d).1 (declForm d).2 = .ok d := by
  cases d <;>
    simp [declF, declForm, natR_nat, natsR_nats, boolR_bool, hintsR_layout, safetyR_layout,
      quotKindR_layout, mapM_layout ctorF_layout, mapM_layout recF_layout, mapM_layout typeF_layout,
      bind, Except.bind, pure, Except.pure]

theorem declForm_of_declF {k : String} {p : Value} {d : DeclF} (h : declF k p = .ok d) :
    declForm d = (k, p) := by
  unfold declF at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := h
    simp [declForm, bool_of_boolR ha, nats_of_natsR hb, nat_of_natR hc, nat_of_natR he]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, e, he, f, hf, g, hg, i, hi, rfl⟩ := h
    simp [declForm, nats_of_natsR ha, hints_of_hintsR hb, nats_of_natsR hc, nat_of_natR he,
      safety_of_safetyR hf, nat_of_natR hg, nat_of_natR hi]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, e, he, f, hf, rfl⟩ := h
    simp [declForm, nats_of_natsR ha, nats_of_natsR hb, nat_of_natR hc, nat_of_natR he,
      nat_of_natR hf]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, e, he, f, hf, g, hg, rfl⟩ := h
    simp [declForm, nats_of_natsR ha, bool_of_boolR hb, nats_of_natsR hc, nat_of_natR he,
      nat_of_natR hf, nat_of_natR hg]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := h
    simp [declForm, quotKind_of_quotKindR ha, nats_of_natsR hb, nat_of_natR hc, nat_of_natR he]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
    simp [declForm, mapM_inverse ctor_of_ctorF ha, mapM_inverse rec_of_recF hb,
      mapM_inverse type_of_typeF hc]
  · simp [bad] at h

/-! ## Records -/

theorem nameForm_key (f : NameF) : ¬(nameForm f).1 < "in" := by
  cases f <;> simp only [nameForm] <;> decide

theorem levelForm_key (f : LevelF) : ¬(levelForm f).1 < "il" := by
  cases f <;> simp only [levelForm] <;> decide

theorem exprForm_mdata (f : ExprF) : (exprForm f).1 ≠ "mdata" := by
  cases f <;> simp only [exprForm] <;> decide

theorem parseLine_layout (r : Raw) : parseLine (rawLayout r) = .ok r := by
  cases r with
  | name i f =>
    have hk := nameForm_key f
    have hf := nameF_layout f
    simp only [rawLayout, ascending, hk, ite_false]
    rcases hn : nameForm f with ⟨k, p⟩
    rw [hn] at hk hf
    cases f <;> simp only [nameForm, Prod.mk.injEq] at hn <;> obtain ⟨rfl, rfl⟩ := hn <;>
      simp [parseLine, natR_nat, hf, bind, Except.bind, pure, Except.pure]
  | level i f =>
    have hk := levelForm_key f
    have hf := levelF_layout f
    simp only [rawLayout, ascending, hk, ite_false]
    rcases hn : levelForm f with ⟨k, p⟩
    rw [hn] at hk hf
    cases f <;> simp only [levelForm, Prod.mk.injEq] at hn <;> obtain ⟨rfl, rfl⟩ := hn <;>
      simp [parseLine, natR_nat, hf, bind, Except.bind, pure, Except.pure]
  | expr i f =>
    simp only [rawLayout, ascending]
    by_cases hk : (exprForm f).1 < "ie"
    · have hf := exprLo_layout f hk
      simp only [hk, ite_true]
      rcases hn : exprForm f with ⟨k, p⟩
      rw [hn] at hk hf
      cases f <;> simp only [exprForm, Prod.mk.injEq] at hn <;> obtain ⟨rfl, rfl⟩ := hn <;>
        simp_all [parseLine, natR_nat, bind, Except.bind, pure, Except.pure]
    · have hf := exprHi_layout f hk
      simp only [hk, ite_false]
      rcases hn : exprForm f with ⟨k, p⟩
      rw [hn] at hk hf
      cases f <;> simp only [exprForm, Prod.mk.injEq] at hn <;> obtain ⟨rfl, rfl⟩ := hn <;>
        simp_all [parseLine, natR_nat, bind, Except.bind, pure, Except.pure]
  | decl d =>
    have hf := declF_layout d
    simp only [rawLayout]
    rcases hn : declForm d with ⟨k, p⟩
    rw [hn] at hf
    cases d <;> simp only [declForm, Prod.mk.injEq] at hn <;> obtain ⟨rfl, rfl⟩ := hn <;>
      simp [parseLine, hf, bind, Except.bind, pure, Except.pure]

theorem rawLayout_of_parseLine {v : Value} {r : Raw} (h : parseLine v = .ok r) :
    rawLayout r = v := by
  unfold parseLine at h
  split at h
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, f, hf, rfl⟩ := h
    have hn := nameForm_of_nameF hf
    have hk := nameForm_key f
    rw [hn] at hk
    simp only [rawLayout, ascending, hn, hk, ↓reduceIte, nat_of_natR ha]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, f, hf, rfl⟩ := h
    have hn := levelForm_of_levelF hf
    have hk := levelForm_key f
    rw [hn] at hk
    simp only [rawLayout, ascending, hn, hk, ↓reduceIte, nat_of_natR ha]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, f, hf, rfl⟩ := h
    obtain ⟨hn, hk⟩ := exprForm_of_exprLo hf
    simp only [rawLayout, ascending, hn, hk, ↓reduceIte, nat_of_natR ha]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨a, ha, f, hf, rfl⟩ := h
    obtain ⟨hn, hk⟩ := exprForm_of_exprHi hf
    simp only [rawLayout, ascending, hn, hk, ↓reduceIte, nat_of_natR ha]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨d, hd, rfl⟩ := h
    simp only [rawLayout, declForm_of_declF hd]
  · simp [bad] at h

/-- Stage 1 accepts exactly the layouts. -/
theorem parseLine_ok (v : Value) (r : Raw) : parseLine v = .ok r ↔ v = rawLayout r :=
  ⟨fun h => (rawLayout_of_parseLine h).symm, fun h => h ▸ parseLine_layout r⟩

theorem rawLayout_inj {r r' : Raw} (h : rawLayout r = rawLayout r') : r = r' := by
  have := parseLine_layout r
  rw [h, parseLine_layout r'] at this
  exact (Except.ok.inj this).symm

/-- A layout is never an `mdata` record. -/
theorem rawLayout_not_mdata (r : Raw) : ¬IsMData (rawLayout r) := by
  rintro ⟨i, p, h⟩
  cases r with
  | name j
    f =>
    simp only [rawLayout, ascending, nameForm_key f, ite_false, Value.obj.injEq, List.cons.injEq,
      Prod.mk.injEq] at h
    simp at h
  | level j
    f =>
    simp only [rawLayout, ascending, levelForm_key f, ite_false, Value.obj.injEq, List.cons.injEq,
      Prod.mk.injEq] at h
    simp at h
  | expr j f =>
    have hm := exprForm_mdata f
    simp only [rawLayout, ascending] at h
    split at h <;> simp_all
  | decl d => simp [rawLayout] at h

/-! ## Failure classes: `mdata` alone is outside the profile -/

theorem onlyBad_bad {α : Type} (w : String) : OnlyBad (bad w : R α) := by
  intro c w' h
  simp only [bad, Except.error.injEq, Prod.mk.injEq] at h
  exact h.1.symm

theorem onlyBad_ok {α : Type} (x : α) : OnlyBad (.ok x : R α) := fun _ _ h => by cases h

theorem onlyBad_natR (w : String) (v : Value) : OnlyBad (natR w v) := by
  unfold natR
  split
  · split
    · exact onlyBad_ok _
    · exact onlyBad_bad _
  · exact onlyBad_bad _

theorem onlyBad_strR (w : String) (v : Value) : OnlyBad (strR w v) := by
  unfold strR
  split
  · exact onlyBad_ok _
  · exact onlyBad_bad _

theorem onlyBad_boolR (w : String) (v : Value) : OnlyBad (boolR w v) := by
  unfold boolR
  split
  · exact onlyBad_ok _
  · exact onlyBad_bad _

theorem onlyBad_natsR (w : String) (v : Value) : OnlyBad (natsR w v) := by
  unfold natsR
  split
  · exact onlyBad_mapM _ (onlyBad_natR w) _
  · exact onlyBad_bad _

theorem onlyBad_binderInfoR (v : Value) : OnlyBad (binderInfoR v) := by
  unfold binderInfoR
  split <;>
    first
    | exact onlyBad_ok _
    | exact onlyBad_bad _

theorem onlyBad_hintsR (v : Value) : OnlyBad (hintsR v) := by
  unfold hintsR
  split
  · exact onlyBad_ok _
  · exact onlyBad_ok _
  · refine onlyBad_bind (onlyBad_natR _ _) fun k => ?_
    split
    · exact onlyBad_pure _
    · exact onlyBad_bad _
  · exact onlyBad_bad _

theorem onlyBad_safetyR (v : Value) : OnlyBad (safetyR v) := by
  unfold safetyR
  split <;>
    first
    | exact onlyBad_ok _
    | exact onlyBad_bad _

theorem onlyBad_quotKindR (v : Value) : OnlyBad (quotKindR v) := by
  unfold quotKindR
  split <;>
    first
    | exact onlyBad_ok _
    | exact onlyBad_bad _

theorem onlyBad_nameF (k : String) (p : Value) : OnlyBad (nameF k p) := by
  unfold nameF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_strR _ _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_levelF (k : String) (p : Value) : OnlyBad (levelF k p) := by
  unfold levelF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_exprLo (k : String) (p : Value) : OnlyBad (exprLo k p) := by
  unfold exprLo
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_natsR _ _
        | exact onlyBad_binderInfoR _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_exprHi (k : String) (p : Value) (hk : k ≠ "mdata") : OnlyBad (exprHi k p) := by
  unfold exprHi
  split <;>
    (first
      | exact absurd rfl hk
      | skip) <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_boolR _ _
        | exact onlyBad_need _ _
        | exact onlyBad_binderInfoR _
        | apply onlyBad_bind
        | intro)

theorem exprHi_profile (k : String) (p : Value) (w : String)
    (h : exprHi k p = .error (.profile, w)) : k = "mdata" :=
  Classical.byContradiction fun hk => absurd (onlyBad_exprHi k p hk _ _ h) (by decide)

theorem onlyBad_typeF (v : Value) : OnlyBad (typeF v) := by
  unfold typeF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_natsR _ _
        | exact onlyBad_boolR _ _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_ctorF (v : Value) : OnlyBad (ctorF v) := by
  unfold ctorF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_natsR _ _
        | exact onlyBad_boolR _ _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_ruleF (v : Value) : OnlyBad (ruleF v) := by
  unfold ruleF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_rulesR (v : Value) : OnlyBad (rulesR v) := by
  unfold rulesR
  split
  · exact onlyBad_mapM _ onlyBad_ruleF _
  · exact onlyBad_bad _

theorem onlyBad_recF (v : Value) : OnlyBad (recF v) := by
  unfold recF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_natsR _ _
        | exact onlyBad_boolR _ _
        | exact onlyBad_rulesR _
        | apply onlyBad_bind
        | intro)

theorem onlyBad_declF (k : String) (p : Value) : OnlyBad (declF k p) := by
  unfold declF
  split <;>
    repeat'
      (first
        | exact onlyBad_pure _
        | exact onlyBad_bad _
        | exact onlyBad_natR _ _
        | exact onlyBad_natsR _ _
        | exact onlyBad_boolR _ _
        | exact onlyBad_hintsR _
        | exact onlyBad_safetyR _
        | exact onlyBad_quotKindR _
        | exact onlyBad_mapM _ onlyBad_ctorF _
        | exact onlyBad_mapM _ onlyBad_recF _
        | exact onlyBad_mapM _ onlyBad_typeF _
        | apply onlyBad_bind
        | intro)

/-- Stage 1's failure class: outside the profile exactly for an `mdata` record. -/
theorem parseLine_class (v : Value) (c : Class) (w : String) (h : parseLine v = .error (c, w)) :
    c = .profile ↔ IsMData v := by
  constructor
  · intro hc
    subst hc
    unfold parseLine at h
    split at h
    · exact
        absurd
          (onlyBad_bind (onlyBad_natR _ _)
            (fun _ => onlyBad_bind (onlyBad_nameF _ _) fun _ => onlyBad_pure _) _ _ h)
          (by decide)
    · exact
        absurd
          (onlyBad_bind (onlyBad_natR _ _)
            (fun _ => onlyBad_bind (onlyBad_levelF _ _) fun _ => onlyBad_pure _) _ _ h)
          (by decide)
    · exact
        absurd
          (onlyBad_bind (onlyBad_natR _ _)
            (fun _ => onlyBad_bind (onlyBad_exprLo _ _) fun _ => onlyBad_pure _) _ _ h)
          (by decide)
    · rcases (bind_error _ _ _).1 h with h | ⟨a, ha, h⟩
      · exact absurd (onlyBad_natR _ _ _ _ h) (by decide)
      · rcases (bind_error _ _ _).1 h with h | ⟨f, _, h⟩
        · have hk := exprHi_profile _ _ w h
          subst hk
          exact ⟨a, _, by rw [nat_of_natR ha]⟩
        · simp [pure, Except.pure] at h
    · exact absurd (onlyBad_bind (onlyBad_declF _ _) (fun _ => onlyBad_pure _) _ _ h) (by decide)
    · exact absurd (onlyBad_bad _ _ _ h) (by decide)
  · rintro ⟨i, p, rfl⟩
    have e :
      parseLine (.obj [("ie", nat i), ("mdata", p)]) =
        outside "metadata (the export step passes no --export-mdata)" :=
      rfl
    rw [e] at h
    simp only [outside, Except.error.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-! ## The header -/

theorem header_layout (githash version : String) :
    header githash version (headerLayout githash version) = .ok () := by
  simp [header, headerLayout, pure, Except.pure]

theorem header_ok (githash version : String) (v : Value) :
    header githash version v = .ok () ↔ v = headerLayout githash version := by
  constructor
  · intro h
    unfold header at h
    split at h
    · split at h
      · split at h
        · rename_i hgv
          simp only [Bool.and_eq_true, beq_iff_eq] at hgv
          obtain ⟨rfl, rfl⟩ := hgv
          rfl
        · simp [outside] at h
      · simp [outside] at h
    · simp [bad] at h
  · rintro rfl
    exact header_layout githash version

theorem header_class (githash version : String) (v : Value) (c : Class) (w : String)
    (h : header githash version v = .error (c, w)) : c = .profile ↔ HeaderShape v := by
  constructor
  · intro hc
    subst hc
    unfold header at h
    split at h
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact absurd (onlyBad_bad _ _ _ h) (by decide)
  · rintro ⟨a, b, d, e, f, rfl⟩
    simp only [header] at h
    split at h
    · split at h
      · simp [pure, Except.pure] at h
      · simp only [outside, Except.error.injEq, Prod.mk.injEq] at h
        exact h.1.symm
    · simp only [outside, Except.error.injEq, Prod.mk.injEq] at h
      exact h.1.symm

end FvdepAudit.Export.Proof
