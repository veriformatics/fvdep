import Fvdep.Semver.Parse.V1_0_0
/-!
# semver.compare 1.0.0 — Semantic Versioning 2.0.0 §11: precedence

Numeric core, then release > pre-release, then ids left to right (numeric < alphanumeric,
numerics by value, alphanumerics by ASCII), shorter prefix lower. Build metadata never
affects precedence. Protocol op `compare a b` parses both with `semver.parse@1.0.0`.
-/
namespace Fvdep.Semver.Compare.V1_0_0
open Fvdep.Semver.Parse.V1_0_0

/-! ## Precedence -/

def cmpNat (a b : Nat) : Ordering := if a < b then .lt else if a = b then .eq else .gt

def cmpChars : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmpNat a.toNat b.toNat).then (cmpChars as bs)

def cmpIdent : Ident → Ident → Ordering
  | .num a, .num b => cmpNat a b
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt
  | .alnum a, .alnum b => cmpChars a b

def cmpIds : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmpIdent a b).then (cmpIds as bs)

/-- Release (`[]`) ranks above any pre-release. -/
def cmpPre : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | a, b => cmpIds a b

def compare (a b : Version) : Ordering :=
  (cmpNat a.major b.major).then <| (cmpNat a.minor b.minor).then <|
    (cmpNat a.patch b.patch).then (cmpPre a.pre b.pre)

/-! ## Obligations -/

theorem cmpNat_swap (a b : Nat) : (cmpNat a b).swap = cmpNat b a := by
  unfold cmpNat
  by_cases h1 : a < b
  · have : ¬b < a := by omega
    have : b ≠ a := by omega
    simp [*, Ordering.swap]
  · by_cases h3 : a = b
    · subst h3; simp [Ordering.swap]
    · have : b < a := by omega
      simp [*, Ordering.swap]

theorem then_swap (o p : Ordering) : (o.then p).swap = o.swap.then p.swap := by
  cases o <;> cases p <;> rfl

theorem cmpChars_swap (a b : List Char) : (cmpChars a b).swap = cmpChars b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b <;> simp_all [cmpChars, then_swap, cmpNat_swap]

theorem cmpIdent_swap (a b : Ident) : (cmpIdent a b).swap = cmpIdent b a := by
  cases a <;> cases b <;> simp [cmpIdent, cmpNat_swap, cmpChars_swap]

theorem cmpIds_swap (a b : List Ident) : (cmpIds a b).swap = cmpIds b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b <;> simp_all [cmpIds, then_swap, cmpIdent_swap]

theorem cmpPre_swap (a b : List Ident) : (cmpPre a b).swap = cmpPre b a := by
  rcases a with _ | ⟨x, xs⟩ <;> rcases b with _ | ⟨y, ys⟩ <;> simp [cmpPre, cmpIds_swap]

/-- Antisymmetry: `a < b` exactly when `b > a`. -/
theorem compare_swap (a b : Version) : (compare a b).swap = compare b a := by
  simp [compare, then_swap, cmpNat_swap, cmpPre_swap]

theorem cmpChars_refl (a : List Char) : cmpChars a a = .eq := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [cmpChars, cmpNat, ih]

theorem compare_refl (a : Version) : compare a a = .eq := by
  have hi : ∀ i, cmpIdent i i = .eq := by
    intro i; cases i <;> simp [cmpIdent, cmpNat, cmpChars_refl]
  have hl : ∀ l, cmpIds l l = .eq := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => simp [cmpIds, hi, ih]
  have hp : cmpPre a.pre a.pre = .eq := by
    rcases h : a.pre with _ | ⟨x, xs⟩ <;> simp [cmpPre, hl]
  simp [compare, cmpNat, hp]

/-- Build metadata never affects precedence (§10). -/
theorem compare_ignores_build (a b : Version) (b₁ b₂ : List (List Char)) :
    compare { a with build := b₁ } { b with build := b₂ } = compare a b := rfl

/-- Precedence is transitive (a total preorder). OPEN: proof pending. -/
theorem compare_trans (a b c : Version) (hab : compare a b = .lt) (hbc : compare b c = .lt) :
    compare a c = .lt := by
  sorry

end Fvdep.Semver.Compare.V1_0_0
