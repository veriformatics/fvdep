import Fvdep.Semver.Compare.V1_0_0

/-! Obligations of `Fvdep.Semver.Compare.V1_0_0`: each comparison layer (numbers, characters,
identifiers, identifier lists, pre-release parts, whole versions) is `Lawful` — antisymmetric,
equal exactly on equal arguments, transitive in "not above" — and lexicographic steps keep it. -/

namespace FvdepProofs.Semver.Compare.V1_0_0

open Fvdep.Semver.Version.V1_0_0 Fvdep.Semver.Compare.V1_0_0

structure Lawful {α : Type} (f : α → α → Ordering) : Prop where
  swap : ∀ a b, f a b = (f b a).swap
  eqIff : ∀ a b, f a b = .eq ↔ a = b
  leTrans : ∀ a b c, f a b ≠ .gt → f b c ≠ .gt → f a c ≠ .gt

theorem Lawful.ltTrans {α : Type} {f : α → α → Ordering} (h : Lawful f) {a b c : α}
    (hab : f a b = .lt) (hbc : f b c = .lt) : f a c = .lt := by
  have hle := h.leTrans a b c (by simp [hab]) (by simp [hbc])
  cases hac : f a c with
  | lt => rfl
  | gt => exact absurd hac hle
  | eq =>
    have e := (h.eqIff a c).mp hac
    subst e
    have hs := h.swap a b
    rw [hbc, hab] at hs
    cases hs

/-- A lexicographic step `(f a b).then r` keeps "not above" transitive when `f` is lawful and the
rest is (`x`, `y`, `z` = the rest's results for (a, b), (b, c), (a, c)). -/
theorem then_leTrans {α : Type} {f : α → α → Ordering} (hf : Lawful f) {a b c : α}
    {x y z : Ordering} (hr : a = b → b = c → x ≠ .gt → y ≠ .gt → z ≠ .gt)
    (hab : (f a b).then x ≠ .gt) (hbc : (f b c).then y ≠ .gt) : (f a c).then z ≠ .gt := by
  cases h1 : f a b with
  | gt => simp [h1, Ordering.then] at hab
  | lt =>
    cases h2 : f b c with
    | gt => simp [h2, Ordering.then] at hbc
    | lt => simp [hf.ltTrans h1 h2, Ordering.then]
    | eq =>
      have e := (hf.eqIff b c).mp h2
      subst e
      simp [h1, Ordering.then]
  | eq =>
    have e := (hf.eqIff a b).mp h1
    subst e
    cases h2 : f a c with
    | gt => simp [h2, Ordering.then] at hbc
    | lt => simp [Ordering.then]
    | eq =>
      have e := (hf.eqIff a c).mp h2
      subst e
      simp only [h1, Ordering.then] at hab hbc ⊢
      exact hr rfl rfl hab hbc

theorem lawful_pair {α β : Type} {f : α → α → Ordering} {g : β → β → Ordering} (hf : Lawful f)
    (hg : Lawful g) : Lawful fun (p q : α × β) => (f p.1 q.1).then (g p.2 q.2)
    where
  swap p q := by
    rw [hf.swap p.1 q.1, hg.swap p.2 q.2]
    cases f q.1 p.1 <;> cases g q.2 p.2 <;> rfl
  eqIff p q := by
    rw [Ordering.then_eq_eq, hf.eqIff, hg.eqIff]
    exact ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  leTrans p q r hpq hqr := then_leTrans hf (fun _ _ => hg.leTrans p.2 q.2 r.2) hpq hqr

/-- Lexicographic order on lists, a proper prefix below its extension. -/
def listLex {α : Type} (f : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (f a b).then (listLex f as bs)

theorem lawful_listLex {α : Type} {f : α → α → Ordering} (hf : Lawful f) : Lawful (listLex f) where
  swap := by
    intro as
    induction as with
    | nil =>
      intro bs; cases bs <;> rfl
    | cons a as ih =>
      intro bs
      cases bs with
      | nil => rfl
      | cons b bs =>
        simp only [listLex]
        rw [hf.swap a b, ih bs]
        cases f b a <;> cases listLex f bs as <;> rfl
  eqIff := by
    intro as
    induction as with
    | nil =>
      intro bs; cases bs <;> simp [listLex]
    | cons a as ih =>
      intro bs
      cases bs with
      | nil => simp [listLex]
      | cons b bs => simp [listLex, Ordering.then_eq_eq, hf.eqIff, ih]
  leTrans := by
    intro as
    induction as with
    | nil =>
      intro bs cs _ hbc
      cases bs <;> cases cs <;> simp_all [listLex]
    | cons a as ih =>
      intro bs cs hab hbc
      cases bs with
      | nil => simp [listLex] at hab
      | cons b bs =>
        cases cs with
        | nil => simp [listLex] at hbc
        | cons c cs =>
          simp only [listLex] at hab hbc ⊢
          exact then_leTrans hf (fun _ _ => ih bs cs) hab hbc

theorem lawful_nat : Lawful nat where
  swap a b := by
    unfold nat
    by_cases h1 : a < b
    · have : ¬b < a := by omega
      have : b ≠ a := by omega
      simp [*, Ordering.swap]
    · by_cases h2 : a = b
      · subst h2
        simp [Ordering.swap]
      · have : b < a := by omega
        simp [*, Ordering.swap]
  eqIff a b := by
    unfold nat
    by_cases h1 : a < b
    · simp [h1]
      omega
    · by_cases h2 : a = b <;> simp [h1, h2]
  leTrans a b c hab hbc := by
    unfold nat at *
    by_cases h1 : a < c
    · simp [h1]
    · by_cases h2 : a = c
      · simp [h2]
      · have hb1 : ¬a > b := by
          intro h
          have : ¬a < b := by omega
          have : a ≠ b := by omega
          simp [*] at hab
        have hb2 : ¬b > c := by
          intro h
          have : ¬b < c := by omega
          have : b ≠ c := by omega
          simp [*] at hbc
        omega

theorem lawful_char : Lawful fun a b : Char => nat a.toNat b.toNat where
  swap a b := lawful_nat.swap a.toNat b.toNat
  eqIff a b := (lawful_nat.eqIff a.toNat b.toNat).trans Char.toNat_inj
  leTrans a b c := lawful_nat.leTrans a.toNat b.toNat c.toNat

theorem chars_eq : chars = listLex fun a b : Char => nat a.toNat b.toNat := by
  funext as bs
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [chars, listLex, ih]

theorem lawful_chars : Lawful chars := chars_eq ▸ lawful_listLex lawful_char

theorem lawful_ident : Lawful ident where
  swap a b := by
    cases a <;> cases b <;> simp only [ident] <;>
      first
      | rfl
      | exact lawful_nat.swap _ _
      | exact lawful_chars.swap _ _
  eqIff a b := by cases a <;> cases b <;> simp [ident, lawful_nat.eqIff, lawful_chars.eqIff]
  leTrans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp only [ident] at hab hbc ⊢ <;>
      first
      | exact absurd rfl hab
      | exact absurd rfl hbc
      | exact lawful_nat.leTrans _ _ _ hab hbc
      | exact lawful_chars.leTrans _ _ _ hab hbc
      | (simp; done)

theorem idents_eq : idents = listLex ident := by
  funext as bs
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [idents, listLex, ih]

theorem lawful_idents : Lawful idents := idents_eq ▸ lawful_listLex lawful_ident

theorem lawful_pre : Lawful pre where
  swap a b := by
    cases a <;> cases b <;> simp only [pre] <;>
      first
      | rfl
      | exact lawful_idents.swap _ _
  eqIff a b := by cases a <;> cases b <;> simp [pre, lawful_idents.eqIff]
  leTrans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp only [pre] at hab hbc ⊢ <;>
      first
      | exact absurd rfl hab
      | exact absurd rfl hbc
      | exact lawful_idents.leTrans _ _ _ hab hbc
      | (simp; done)

/-- The comparison key: everything but the build metadata. -/
def key (v : Version) : Nat × Nat × Nat × List Ident := (v.major, v.minor, v.patch, v.pre)

theorem lawful_key :
    Lawful fun (p q : Nat × Nat × Nat × List Ident) =>
      (nat p.1 q.1).then
        ((nat p.2.1 q.2.1).then ((nat p.2.2.1 q.2.2.1).then (pre p.2.2.2 q.2.2.2))) :=
  lawful_pair lawful_nat (lawful_pair lawful_nat (lawful_pair lawful_nat lawful_pre))

theorem compare_key (a b : Version) :
    compare a b =
      (nat (key a).1 (key b).1).then
        ((nat (key a).2.1 (key b).2.1).then
          ((nat (key a).2.2.1 (key b).2.2.1).then (pre (key a).2.2.2 (key b).2.2.2))) := rfl

theorem swap : Fvdep.Semver.Compare.V1_0_0.swap := by
  intro a b
  rw [compare_key, compare_key]
  exact lawful_key.swap (key a) (key b)

theorem trans : Fvdep.Semver.Compare.V1_0_0.trans := by
  intro a b c hab hbc
  rw [compare_key] at hab hbc ⊢
  exact lawful_key.leTrans (key a) (key b) (key c) hab hbc

theorem eqIff : Fvdep.Semver.Compare.V1_0_0.eqIff := by
  intro a b
  rw [compare_key, lawful_key.eqIff]
  cases a
  cases b
  simp [key]

/-! ## `precedence`: `compare` answers `.lt` exactly on §11's first-difference relation -/

theorem listBefore_nil_nil {α : Type} (R : α → α → Prop) : ¬ListBefore R [] [] := by
  rintro (⟨k, x, y, -, hx, -, -⟩ | ⟨h, -⟩)
  · simp at hx
  · simp at h

theorem listBefore_nil_cons {α : Type} (R : α → α → Prop) (y : α) (q : List α) :
    ListBefore R [] (y :: q) := .inr ⟨by simp, by simp⟩

theorem listBefore_cons_nil {α : Type} (R : α → α → Prop) (x : α) (p : List α) :
    ¬ListBefore R (x :: p) [] := by
  rintro (⟨k, a, b, -, -, hb, -⟩ | ⟨h, -⟩)
  · simp at hb
  · simp at h

theorem listBefore_cons_cons {α : Type} (R : α → α → Prop) (x y : α) (p q : List α) :
    ListBefore R (x :: p) (y :: q) ↔ R x y ∨ x = y ∧ ListBefore R p q := by
  constructor
  · rintro (⟨k, a, b, ht, ha, hb, hr⟩ | ⟨hl, he⟩)
    · cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
        subst ha
        subst hb
        exact .inl hr
      | succ k =>
        simp only [List.take_succ_cons, List.cons.injEq] at ht
        simp only [List.getElem?_cons_succ] at ha hb
        exact .inr ⟨ht.1, .inl ⟨k, a, b, ht.2, ha, hb, hr⟩⟩
    · simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at hl he
      exact .inr ⟨he.1, .inr ⟨by omega, he.2⟩⟩
  · rintro (hr | ⟨rfl, ⟨k, a, b, ht, ha, hb, hr⟩ | ⟨hl, he⟩⟩)
    · exact .inl ⟨0, x, y, rfl, rfl, rfl, hr⟩
    · exact .inl ⟨k + 1, a, b, by simp [ht], by simpa using ha, by simpa using hb, hr⟩
    · refine .inr ⟨by simpa using hl, ?_⟩
      simp only [List.length_cons, List.take_succ_cons]
      exact congrArg _ he

theorem then_eq_lt (o p : Ordering) : o.then p = .lt ↔ o = .lt ∨ o = .eq ∧ p = .lt := by
  cases o <;> cases p <;> decide

theorem listLex_lt_iff {α : Type} {f : α → α → Ordering} {R : α → α → Prop}
    (hlt : ∀ a b, f a b = .lt ↔ R a b) (heq : ∀ a b, f a b = .eq ↔ a = b) :
    ∀ p q, listLex f p q = .lt ↔ ListBefore R p q
  | [], [] => by simp [listLex, listBefore_nil_nil]
  | [], y :: q => by simp [listLex, listBefore_nil_cons]
  | x :: p, [] => by simp [listLex, listBefore_cons_nil]
  | x :: p, y :: q => by
    rw [listBefore_cons_cons, ← listLex_lt_iff hlt heq p q, ← hlt x y, ← heq x y]
    exact then_eq_lt _ _

theorem nat_lt (a b : Nat) : nat a b = .lt ↔ a < b := by
  unfold nat
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : a = b <;> simp [h1, h2]

theorem ident_lt (x y : Ident) : ident x y = .lt ↔ IdentBefore x y := by
  cases x <;> cases y
  · exact nat_lt _ _
  · simp [ident, IdentBefore]
  · simp [ident, IdentBefore]
  · simp only [ident, IdentBefore, chars_eq]
    exact listLex_lt_iff (fun a b : Char => nat_lt a.toNat b.toNat) lawful_char.eqIff _ _

theorem idents_lt (p q : List Ident) : idents p q = .lt ↔ ListBefore IdentBefore p q := by
  rw [idents_eq]
  exact listLex_lt_iff ident_lt lawful_ident.eqIff p q

theorem pre_lt (p q : List Ident) : pre p q = .lt ↔ PreBefore p q := by
  cases p <;> cases q <;> simp [pre, PreBefore, idents_lt]

theorem precedence : Fvdep.Semver.Compare.V1_0_0.precedence := by
  intro a b
  simp only [Fvdep.Semver.Compare.V1_0_0.compare, Precedes, then_eq_lt, nat_lt, pre_lt,
    lawful_nat.eqIff, and_or_left]

end FvdepProofs.Semver.Compare.V1_0_0
