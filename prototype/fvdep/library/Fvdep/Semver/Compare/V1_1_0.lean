import Fvdep.Semver.Compare.V1_0_0
import Fvdep.Semver.Parse.V1_1_0
/-!
# semver.compare 1.1.0 — same precedence as 1.0.0, transitivity proven

`compare` is unchanged (`unchanged`, by `rfl`), so every proof against 1.0.0 carries over.
The protocol op parses both texts with `semver.parse@1.1.0` (the same grammar as 1.0.0).
The 1.0.0 obligation `compare_trans` was open; here it is proven (`compare_trans`), along with
the fact that two versions of equal precedence differ at most in build metadata (`compare_eq`).
-/
namespace Fvdep.Semver.Compare.V1_1_0
open Fvdep.Semver.Parse.V1_0_0 (Version Ident)
open Fvdep.Semver.Compare.V1_0_0 (cmpNat cmpChars cmpIdent cmpIds cmpPre)

def compare := V1_0_0.compare

theorem unchanged : compare = V1_0_0.compare := rfl

/-! ## Lemmas -/

theorem then_eq_lt (o p : Ordering) : o.then p = .lt ↔ o = .lt ∨ (o = .eq ∧ p = .lt) := by
  cases o <;> cases p <;> simp [Ordering.then]

theorem then_eq_eq (o p : Ordering) : o.then p = .eq ↔ o = .eq ∧ p = .eq := by
  cases o <;> cases p <;> simp [Ordering.then]

theorem cmpNat_lt (a b : Nat) : cmpNat a b = .lt ↔ a < b := by
  unfold cmpNat; split <;> (try split) <;> simp_all <;> omega

theorem cmpNat_eq (a b : Nat) : cmpNat a b = .eq ↔ a = b := by
  unfold cmpNat; split <;> (try split) <;> simp_all <;> omega

theorem cmpChars_eq (a b : List Char) : cmpChars a b = .eq → a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpChars]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpChars]
    | cons y ys =>
      simp only [cmpChars, then_eq_eq, cmpNat_eq]
      rintro ⟨h1, h2⟩
      rw [Char.toNat_inj.mp h1, ih ys h2]

theorem cmpChars_trans (a b c : List Char) :
    cmpChars a b = .lt → cmpChars b c = .lt → cmpChars a c = .lt := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp [cmpChars]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpChars]
    | cons y ys =>
      cases c with
      | nil => simp [cmpChars]
      | cons z zs =>
        simp only [cmpChars, then_eq_lt, cmpNat_lt, cmpNat_eq]
        rintro (h1 | ⟨h1, h2⟩) (h3 | ⟨h3, h4⟩)
        · exact .inl (by omega)
        · exact .inl (by omega)
        · exact .inl (by omega)
        · exact .inr ⟨by omega, ih _ _ h2 h4⟩

theorem cmpIdent_eq (a b : Ident) : cmpIdent a b = .eq → a = b := by
  cases a <;> cases b <;> simp [cmpIdent, cmpNat_eq]
  exact cmpChars_eq _ _

theorem cmpIdent_trans (a b c : Ident) :
    cmpIdent a b = .lt → cmpIdent b c = .lt → cmpIdent a c = .lt := by
  cases a <;> cases b <;> cases c <;> simp [cmpIdent, cmpNat_lt]
  · omega
  · exact cmpChars_trans _ _ _

theorem cmpIds_eq (a b : List Ident) : cmpIds a b = .eq → a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpIds]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpIds]
    | cons y ys =>
      simp only [cmpIds, then_eq_eq]
      rintro ⟨h1, h2⟩
      rw [cmpIdent_eq _ _ h1, ih ys h2]

theorem cmpIds_trans (a b c : List Ident) :
    cmpIds a b = .lt → cmpIds b c = .lt → cmpIds a c = .lt := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp [cmpIds]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpIds]
    | cons y ys =>
      cases c with
      | nil => simp [cmpIds]
      | cons z zs =>
        simp only [cmpIds, then_eq_lt]
        rintro (h1 | ⟨h1, h2⟩) (h3 | ⟨h3, h4⟩)
        · exact .inl (cmpIdent_trans _ _ _ h1 h3)
        · rw [← cmpIdent_eq _ _ h3]; exact .inl h1
        · rw [cmpIdent_eq _ _ h1]; exact .inl h3
        · rw [cmpIdent_eq _ _ h1]; exact .inr ⟨h3, ih _ _ h2 h4⟩

theorem cmpPre_eq (a b : List Ident) : cmpPre a b = .eq → a = b := by
  rcases a with _ | ⟨x, xs⟩ <;> rcases b with _ | ⟨y, ys⟩ <;> simp [cmpPre]
  exact fun h => by simpa using cmpIds_eq _ _ h

theorem cmpPre_trans (a b c : List Ident) :
    cmpPre a b = .lt → cmpPre b c = .lt → cmpPre a c = .lt := by
  rcases a with _ | ⟨x, xs⟩ <;> rcases b with _ | ⟨y, ys⟩ <;> rcases c with _ | ⟨z, zs⟩ <;>
    simp [cmpPre]
  exact cmpIds_trans _ _ _

/-! ## Obligations -/

/-- Every version equals itself in precedence. -/
theorem compare_refl (a : Version) : compare a a = .eq := V1_0_0.compare_refl a

/-- Antisymmetry: `a < b` exactly when `b > a`. -/
theorem compare_swap (a b : Version) : (compare a b).swap = compare b a := V1_0_0.compare_swap a b

/-- Build metadata never affects precedence. -/
theorem compare_ignores_build (a b : Version) (b₁ b₂ : List (List Char)) :
    compare { a with build := b₁ } { b with build := b₂ } = compare a b := rfl

/-- Two versions of equal precedence are the same version apart from build metadata. -/
theorem compare_eq (a b : Version) (h : compare a b = .eq) :
    { a with build := [] } = { b with build := [] } := by
  obtain ⟨a1, a2, a3, ap, ab⟩ := a
  obtain ⟨b1, b2, b3, bp, bb⟩ := b
  simp only [compare, V1_0_0.compare, then_eq_eq, cmpNat_eq] at h
  obtain ⟨rfl, rfl, rfl, h⟩ := h
  rw [cmpPre_eq _ _ h]

/-- Precedence is transitive: if `a` is lower than `b` and `b` lower than `c`, then `a` is lower
than `c`. -/
theorem compare_trans (a b c : Version) (hab : compare a b = .lt) (hbc : compare b c = .lt) :
    compare a c = .lt := by
  simp only [compare, V1_0_0.compare, then_eq_lt, cmpNat_lt, cmpNat_eq] at *
  have := cmpPre_trans a.pre b.pre c.pre
  have e := cmpPre_eq a.pre b.pre
  have e' := cmpPre_eq b.pre c.pre
  rcases hab with h | ⟨h1, h | ⟨h2, h | ⟨h3, h⟩⟩⟩ <;>
    rcases hbc with g | ⟨g1, g | ⟨g2, g | ⟨g3, g⟩⟩⟩ <;>
    first
    | (left; omega)
    | (right; refine ⟨by omega, ?_⟩; left; omega)
    | (right; refine ⟨by omega, ?_⟩; right; refine ⟨by omega, ?_⟩; left; omega)
    | (right; refine ⟨by omega, ?_⟩; right; refine ⟨by omega, ?_⟩; right;
       exact ⟨by omega, this h g⟩)

end Fvdep.Semver.Compare.V1_1_0
