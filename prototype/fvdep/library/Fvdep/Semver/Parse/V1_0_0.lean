/-!
# semver.parse 1.0.0 — Semantic Versioning 2.0.0 (semver.org) §2, §9, §10: grammar

Strict grammar: `MAJOR.MINOR.PATCH`, no leading zeros, optional `-pre.ids` (non-empty
`[0-9A-Za-z-]`, numeric ids without leading zeros), optional `+build.ids` (non-empty
`[0-9A-Za-z-]`). No `v` prefix, no whitespace. Protocol result = the normalized text.
Ranges (`^1.2`, `~1.2`) = not in this module.
-/
namespace Fvdep.Semver.Parse.V1_0_0

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

/-- Every valid version renders to a string that parses back to it. OPEN: proof pending. -/
theorem parse_render (v : Version) (h : parse (render v) ≠ none) :
    parse (render v) = some v := by
  sorry

end Fvdep.Semver.Parse.V1_0_0
