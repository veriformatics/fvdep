/-!
# semver spec v1.0.0 — Semantic Versioning 2.0.0 (semver.org): parse + precedence

Models: npm `semver` (`valid`, `compare`), crates.io `semver` (`Version::parse`, `Ord`),
PyPI `semver` (`Version.parse`, `compare`). Ranges (`^1.2`, `~1.2`) = not in this version.
Strict grammar (§2, §9, §10): `MAJOR.MINOR.PATCH`, no leading zeros, optional
`-pre.ids` (non-empty `[0-9A-Za-z-]`, numeric ids without leading zeros), optional
`+build.ids` (non-empty `[0-9A-Za-z-]`). No `v` prefix, no whitespace.
Precedence (§11): numeric core, then release > pre-release, then ids left to right
(numeric < alphanumeric, numerics by value, alphanumerics by ASCII), shorter prefix lower.
Build metadata never affects precedence.
-/
namespace Fvdep.Semver.V1_0_0

inductive Ident where
  | num (n : Nat)
  | alnum (s : List Char)
  deriving DecidableEq, Repr

structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List Ident
  build : List (List Char)
  deriving DecidableEq, Repr

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

/-! ## Grammar -/

def isIdChar (c : Char) : Bool := c.isAlphanum || c = '-'

def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOn sep cs
    else match splitOn sep cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- Numeric: digits, no leading zero (except `0` itself). -/
def parseNum : List Char → Option Nat
  | [] => none
  | ['0'] => some 0
  | '0' :: _ :: _ => none
  | cs => if cs.all Char.isDigit then some (cs.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)
          else none

def parseIdent (cs : List Char) : Option Ident :=
  if cs.isEmpty || !cs.all isIdChar then none
  else if cs.all Char.isDigit then (parseNum cs).map .num
  else some (.alnum cs)

def parseBuild (cs : List Char) : Option (List Char) :=
  if cs.isEmpty || !cs.all isIdChar then none else some cs

/-- First occurrence of `sep` splits; `none` = absent. -/
def splitFirst (sep : Char) (cs : List Char) : List Char × Option (List Char) :=
  match cs.idxOf? sep with
  | some i => (cs.take i, some (cs.drop (i + 1)))
  | none => (cs, none)

def parse (s : List Char) : Option Version := do
  let (main, build?) := splitFirst '+' s
  let (core, pre?) := splitFirst '-' main
  let [ma, mi, pa] := splitOn '.' core | none
  let major ← parseNum ma; let minor ← parseNum mi; let patch ← parseNum pa
  let pre ← match pre? with
    | none => some []
    | some p => (splitOn '.' p).mapM parseIdent
  let build ← match build? with
    | none => some []
    | some b => (splitOn '.' b).mapM parseBuild
  some ⟨major, minor, patch, pre, build⟩

def renderNat (n : Nat) : List Char := (toString n).toList

def renderIdent : Ident → List Char
  | .num n => renderNat n
  | .alnum s => s

def joinDot : List (List Char) → List Char
  | [] => []
  | [w] => w
  | w :: ws => w ++ '.' :: joinDot ws

def render (v : Version) : List Char :=
  renderNat v.major ++ '.' :: renderNat v.minor ++ '.' :: renderNat v.patch ++
    (if v.pre.isEmpty then [] else '-' :: joinDot (v.pre.map renderIdent)) ++
    (if v.build.isEmpty then [] else '+' :: joinDot v.build)

def parseStr (s : String) : Option Version := parse s.toList
def renderStr (v : Version) : String := String.ofList (render v)

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

/-- Every valid version renders to a string that parses back to it. OPEN: proof pending. -/
theorem parse_render (v : Version) (h : parse (render v) ≠ none) :
    parse (render v) = some v := by
  sorry

end Fvdep.Semver.V1_0_0
