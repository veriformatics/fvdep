import FvdepCore.Ids
import FvdepCore.Oracle.Wire

/-! Spec of the internal wire codec (contract `docs/contracts/U5b-oracle.md` W1–W2, W4), written
from the contract apart from `FvdepCore.Oracle.Wire`: each token's layout (hex by powers of 16,
decimals = U2's `FvdepCore.Ids.decimal`, UTF-8 = core's `List.utf8Encode`), a request line, a result
line + the replies a result type admits. -/

namespace FvdepAudit.Oracle.Wire.Spec

open FvdepCore.Protocol Fvdep.Semver.Version.V1_0_0

-- The spec's UTF-8 = core's `List.utf8Encode`, a noncomputable definition: no spec runs.
noncomputable section

/-- A lowercase hex digit (`d < 16`). -/
def hexChar (d : Nat) : Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'].getD d '0'

/-- `w` hex digits of `n`, most significant first. -/
def hexOf (w n : Nat) : List Char := (List.range w).reverse.map fun i => hexChar (n / 16 ^ i % 16)

/-- Bytes as hex, two digits each. -/
def hexBytes (bs : List UInt8) : List Char := bs.flatMap fun b => hexOf 2 b.toNat

/-- A canonical decimal (U2's printer). -/
def dec (n : Nat) : List Char := FvdepCore.Ids.decimal n

/-- UTF-8 bytes (core's encoder). -/
def utf8Bytes (cs : List Char) : List UInt8 := cs.utf8Encode.data.toList

/-- Pieces joined by `sep` (none for zero pieces or one). -/
def joined (sep : Char) : List (List Char) → List Char
  | [] => []
  | p :: ps => p ++ ps.flatMap fun q => sep :: q

/-- W1: a pre-release identifier: `n<decimal>` | `a<hex of UTF-8>`. -/
def identLayout : Ident → List Char
  | .num n => 'n' :: dec n
  | .alnum s => 'a' :: hexBytes (utf8Bytes s)

/-- W1: a build identifier: `x<hex of UTF-8>`. -/
def buildLayout (s : List Char) : List Char := 'x' :: hexBytes (utf8Bytes s)

/-- W1: `<major>.<minor>.<patch>/<pre>/<build>` (the lists `.`-joined, empty = empty). -/
def versionLayout (v : Version) : List Char :=
  dec v.major ++ ['.'] ++ dec v.minor ++ ['.'] ++ dec v.patch ++ ['/'] ++
    joined '.' (v.pre.map identLayout) ++
    ['/'] ++
    joined '.' (v.build.map buildLayout)

/-- W1: an int: its absolute value's decimal, `-` first when negative (no `-0`). -/
def intLayout (i : Int) : List Char := if i < 0 then '-' :: dec i.natAbs else dec i.natAbs

def orderingLayout : Ordering → List Char
  | .lt => ['l', 't']
  | .eq => ['e', 'q']
  | .gt => ['g', 't']

/-- W1: a value's token `<tag>:<payload>`. -/
def tokenLayout : Val → List Char
  | .bytes b => ['b', ':'] ++ hexBytes b
  | .text s => ['t', ':'] ++ hexBytes (utf8Bytes s)
  | .utf16 u => ['u', ':'] ++ u.flatMap fun x => hexOf 4 x.toNat
  | .nat n => ['n', ':'] ++ dec n
  | .int i => ['i', ':'] ++ intLayout i
  | .ordering o => ['o', ':'] ++ orderingLayout o
  | .version v => ['v', ':'] ++ versionLayout v

/-- W1: a request line: the tokens in argument order, space-separated. -/
def argsLayout (xs : List Val) : String := String.ofList (joined ' ' (xs.map tokenLayout))

/-- W2: a reply's result line (`invalid` has none). -/
def resultLayout : Reply → String
  | .ok v => String.ofList (['o', 'k', ' '] ++ tokenLayout v)
  | .err => String.ofList ['e', 'r', 'r']
  | .invalid _ => ""

/-- W2: the replies a result type admits: a value of its type; `err` for an optional one alone. -/
def Typed : RTy → Reply → Prop
  | .plain t, .ok v => v.ty = t
  | .option t, .ok v => v.ty = t
  | .option _, .err => True
  | _, _ => False

end

end FvdepAudit.Oracle.Wire.Spec
