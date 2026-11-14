import Fvdep.Semver.Version.V1_0_0

/-! `semver.parse@1.0.0`: SemVer 2.0.0 §2, §9, §10 grammar. `<major>.<minor>.<patch>` numeric
identifiers (`0` or no leading zero, any size); optional `-` + dot-separated pre-release identifiers
(numeric → `num`, without a leading zero; `[0-9A-Za-z-]+` holding a non-digit → `alnum`); optional
`+` + dot-separated build identifiers `[0-9A-Za-z-]+` (leading zeros allowed). The first `+` starts
the build part, the first `-` before it the pre-release part. ASCII alone; no `v`, no whitespace.
The obligations pin `parse` against `Valid` + `render`:
`parse s = some v ↔ Valid v ∧ render v = s`. -/

namespace Fvdep.Semver.Parse.V1_0_0

open Fvdep.Semver.Version.V1_0_0

/-- `[0-9A-Za-z-]` (§9, §10). -/
def identChar (c : Char) : Bool := c.isDigit || c.isAlpha || c == '-'

/-- Split at every `sep`: `a.b..c` → `[a, b, [], c]`; `[]` → `[[]]`. -/
def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOn sep cs
    else
      match splitOn sep cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- Split at the first `sep`: the part before it + the part after it (`none` without a `sep`). -/
def splitFirst (sep : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = sep then ([], some cs)
    else
      match splitFirst sep cs with
      | (a, b) => (c :: a, b)

/-- A numeric identifier (§2, §9): `0`, or digits without a leading zero, of any size. -/
def numeric (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit || (cs.head? == some '0' && cs.length > 1) then none
  else some (cs.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)

/-- A pre-release identifier (§9). -/
def preIdent (cs : List Char) : Option Ident :=
  if cs.isEmpty || !cs.all identChar then none
  else if cs.all Char.isDigit then (numeric cs).map .num else some (.alnum cs)

/-- A build identifier (§10). -/
def buildIdent (cs : List Char) : Option (List Char) :=
  if cs.isEmpty || !cs.all identChar then none else some cs

def parse (s : List Char) : Option Version := do
  let (main, build?) := splitFirst '+' s
  let (core, pre?) := splitFirst '-' main
  let [ma, mi, pa] := splitOn '.' core | none
  let major ← numeric ma
  let minor ← numeric mi
  let patch ← numeric pa
  let pre ←
    match pre? with
    | none =>
      some []
    | some p =>
      (splitOn '.' p).mapM preIdent
  let build ←
    match build? with
    | none =>
      some []
    | some b =>
      (splitOn '.' b).mapM buildIdent
  some { major, minor, patch, pre, build }

/-! ## The language `parse` accepts, written apart -/

/-- §9 + §10 identifier rules on a value: each alphanumeric pre-release identifier is nonempty over
`[0-9A-Za-z-]` with a non-digit; each build identifier is nonempty over `[0-9A-Za-z-]`. -/
def Valid (v : Version) : Prop :=
  (∀ i ∈ v.pre,
      match i with
      | .num _ => True
      | .alnum s => s ≠ [] ∧ (∀ c ∈ s, identChar c = true) ∧ ∃ c ∈ s, c.isDigit = false) ∧
    ∀ b ∈ v.build, b ≠ [] ∧ ∀ c ∈ b, identChar c = true

/-- The digit character for 0–9. -/
def digit (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal spelling of `n`: no leading zero (`0` for zero). -/
def decimal (n : Nat) : List Char :=
  if n < 10 then [digit n] else decimal (n / 10) ++ [digit (n % 10)]
termination_by n
decreasing_by omega

/-- Words joined by `.`. -/
def joinDot : List (List Char) → List Char
  | [] => []
  | [w] => w
  | w :: v :: ws => w ++ '.' :: joinDot (v :: ws)

def renderIdent : Ident → List Char
  | .num n => decimal n
  | .alnum s => s

/-- `major.minor.patch`, then `-` + the pre-release identifiers joined by `.` when there are any,
then `+` + the build identifiers joined by `.` when there are any. -/
def render (v : Version) : List Char :=
  decimal v.major ++ '.' :: decimal v.minor ++ '.' :: decimal v.patch ++
    (if v.pre.isEmpty then [] else '-' :: joinDot (v.pre.map renderIdent)) ++
    if v.build.isEmpty then [] else '+' :: joinDot v.build

/-- `parse` returns valid versions alone. -/
def onlyValid : Prop := ∀ (s : List Char) (v : Version), parse s = some v → Valid v

/-- `parse` accepts a string only in its canonical spelling. -/
def canonical : Prop := ∀ (s : List Char) (v : Version), parse s = some v → render v = s

/-- Every valid version's spelling parses back to it. -/
def complete : Prop := ∀ v : Version, Valid v → parse (render v) = some v

end Fvdep.Semver.Parse.V1_0_0
