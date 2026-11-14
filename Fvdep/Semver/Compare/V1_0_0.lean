import Fvdep.Semver.Version.V1_0_0

/-! `semver.compare@1.0.0`: SemVer 2.0.0 §11 precedence, extended to the whole type
(`docs/library.md`): `major`, `minor`, `patch` numerically, in that order; then `pre`: empty above
nonempty; two nonempty lists element by element (`num` vs `num` numerically, `alnum` vs `alnum` by
code point, `num` below `alnum`), a proper prefix below its extension; `build` ignored. -/

namespace Fvdep.Semver.Compare.V1_0_0

open Fvdep.Semver.Version.V1_0_0

/-- Numeric order. -/
def nat (a b : Nat) : Ordering := if a < b then .lt else if a = b then .eq else .gt

/-- Code-point order of identifier text, a proper prefix first (§11.4.2 "ASCII sort order",
extended to every scalar). -/
def chars : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (nat a.toNat b.toNat).then (chars as bs)

/-- §11.4.1–§11.4.3: numeric by value, alphanumeric by text, numeric below alphanumeric. -/
def ident : Ident → Ident → Ordering
  | .num a, .num b => nat a b
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt
  | .alnum a, .alnum b => chars a b

/-- §11.4: left to right; a proper prefix below its extension (§11.4.4). -/
def idents : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (ident a b).then (idents as bs)

/-- §11.3: a version without pre-release identifiers above one with them. -/
def pre : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | a :: as, b :: bs => idents (a :: as) (b :: bs)

def compare (a b : Version) : Ordering :=
  (nat a.major b.major).then <|
    (nat a.minor b.minor).then <| (nat a.patch b.patch).then (pre a.pre b.pre)

/-! ## §11 written apart: a first-difference relation -/

/-- `p` before `q` in the first-difference order of `R`: they agree on a prefix, then `p`'s next
element is `R`-before `q`'s; or `p` is a proper prefix of `q` (§11.4.4). -/
def ListBefore {α : Type} (R : α → α → Prop) (p q : List α) : Prop :=
  (∃ k x y, p.take k = q.take k ∧ p[k]? = some x ∧ q[k]? = some y ∧ R x y) ∨
    (p.length < q.length ∧ p = q.take p.length)

/-- §11.4.1–§11.4.3: numeric identifiers by value, numeric before alphanumeric, alphanumeric by
code point (§11.4.2's ASCII order, extended to every scalar). -/
def IdentBefore : Ident → Ident → Prop
  | .num a, .num b => a < b
  | .num _, .alnum _ => True
  | .alnum _, .num _ => False
  | .alnum s, .alnum t => ListBefore (fun a b : Char => a.toNat < b.toNat) s t

/-- §11.3: a pre-release version before its release; two pre-releases by their identifiers. -/
def PreBefore (p q : List Ident) : Prop := p ≠ [] ∧ (q = [] ∨ q ≠ [] ∧ ListBefore IdentBefore p q)

/-- §11: `a` precedes `b`: the first of major, minor, patch that differs is lower in `a`, or the
three are equal and `a`'s pre-release part comes first; build metadata plays no part. -/
def Precedes (a b : Version) : Prop :=
  a.major < b.major ∨
    a.major = b.major ∧ a.minor < b.minor ∨
    a.major = b.major ∧ a.minor = b.minor ∧ a.patch < b.patch ∨
    a.major = b.major ∧ a.minor = b.minor ∧ a.patch = b.patch ∧ PreBefore a.pre b.pre

/-- `compare` answers `.lt` exactly when §11 puts `a` first. -/
def precedence : Prop := ∀ a b : Version, compare a b = .lt ↔ Precedes a b

/-- Antisymmetry: swapping the arguments swaps the result. -/
def swap : Prop := ∀ a b : Version, compare a b = (compare b a).swap

/-- Transitivity of "not above". -/
def trans : Prop := ∀ a b c : Version, compare a b ≠ .gt → compare b c ≠ .gt → compare a c ≠ .gt

/-- Equal precedence exactly when the versions differ in build metadata alone (§10). -/
def eqIff : Prop :=
  ∀ a b : Version, compare a b = .eq ↔ { a with build := [] } = { b with build := [] }

end Fvdep.Semver.Compare.V1_0_0
