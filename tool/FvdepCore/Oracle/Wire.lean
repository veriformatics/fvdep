import FvdepCore.Protocol.Types

/-! The internal wire codec between fvdep + the evaluation step (contract
`docs/contracts/U5b-oracle.md` W1–W5): a request = one line of tagged payloads in argument order, a
result = one line (`ok <token>` | `err`). Pure + self-contained (Init + the protocol types): the
step compiles this very text after its import lines (W0), so its conversions are these functions.
Each line reader reads loosely, then keeps a result only when printing it gives back the very line
(the print check: exact readers from round trips alone). -/

namespace FvdepCore.Oracle.Wire

open FvdepCore.Protocol Fvdep.Semver.Version.V1_0_0

/-! ## Digits -/

/-- A lowercase hex digit of `n < 16`. -/
def hexDigit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

/-- The value of a lowercase hex digit. -/
def hexVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat && c.toNat ≤ 102 then some (c.toNat - 87) else none

/-- A byte as two hex digits. -/
def hexByte (b : UInt8) : List Char := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- A UTF-16 code unit as four hex digits. -/
def hexUnit (u : UInt16) : List Char :=
  [hexDigit (u.toNat / 4096), hexDigit (u.toNat / 256 % 16), hexDigit (u.toNat / 16 % 16),
    hexDigit (u.toNat % 16)]

/-- Bytes from hex digit pairs (an odd count or another character → `none`). -/
def unhexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest =>
    match hexVal a, hexVal b, unhexBytes rest with
    | some x, some y, some r => some ((x * 16 + y).toUInt8 :: r)
    | _, _, _ => none
  | [_] => none

/-- Code units from hex digit quads. -/
def unhexUnits : List Char → Option (List UInt16)
  | [] => some []
  | a :: b :: c :: d :: rest =>
    match hexVal a, hexVal b, hexVal c, hexVal d, unhexUnits rest with
    | some w, some x, some y, some z, some r =>
      some ((((w * 16 + x) * 16 + y) * 16 + z).toUInt16 :: r)
    | _, _, _, _, _ => none
  | _ => none

/-- The canonical decimal of `n` (no leading zero). -/
def decimal (n : Nat) : List Char :=
  if h : n < 10 then [Char.ofNat (48 + n)]
  else
    have : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
    decimal (n / 10) ++ [Char.ofNat (48 + n % 10)]
termination_by n

/-- A decimal digit's value. -/
def decVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- The digits' value, most significant first (`acc` so far). -/
def readDigits (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
    match decVal c with
    | some d => readDigits (acc * 10 + d) cs
    | none => none

/-- Decimal digits' value (nonempty; leading zeros are left to the print check). -/
def readDecimal : List Char → Option Nat
  | [] => none
  | cs => readDigits 0 cs

/-! ## Tokens (W1) -/

/-- Split at each `sep`: `[a, b]` for `a ++ sep :: b`, the pieces in order. -/
def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == sep then [] :: splitOn sep cs
    else
      match splitOn sep cs with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

/-- Join with `sep`. -/
def joinWith (sep : Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ sep :: joinWith sep ps

/-- UTF-8 bytes of characters (core's string bytes: `List.utf8Encode` itself is noncomputable). -/
def utf8 (cs : List Char) : List UInt8 := (String.ofList cs).toUTF8.data.toList

/-- Characters of UTF-8 bytes (core's strict decoder). -/
def unutf8 (bs : List UInt8) : Option (List Char) :=
  (ByteArray.mk bs.toArray).utf8Decode?.map (·.toList)

/-- A pre-release identifier: `n<decimal>` | `a<hex of UTF-8>`. -/
def identPayload : Ident → List Char
  | .num n => 'n' :: decimal n
  | .alnum s => 'a' :: (utf8 s).flatMap hexByte

def readIdent : List Char → Option Ident
  | 'n' :: cs => (readDecimal cs).map .num
  | 'a' :: cs => (unhexBytes cs).bind unutf8 |>.map .alnum
  | _ => none

/-- A build identifier: `x<hex of UTF-8>`. -/
def buildPayload (s : List Char) : List Char := 'x' :: (utf8 s).flatMap hexByte

def readBuild : List Char → Option (List Char)
  | 'x' :: cs => (unhexBytes cs).bind unutf8
  | _ => none

/-- A `.`-joined list (empty list = empty text). -/
def dotted (ps : List (List Char)) : List Char := joinWith '.' ps

/-- Each `.`-separated piece read (empty text = empty list). -/
def readDotted {α : Type} (read : List Char → Option α) : List Char → Option (List α)
  | [] => some []
  | cs => (splitOn '.' cs).mapM read

/-- `<major>.<minor>.<patch>/<pre>/<build>`. -/
def versionPayload (v : Version) : List Char :=
  joinWith '/'
    [joinWith '.' [decimal v.major, decimal v.minor, decimal v.patch],
      dotted (v.pre.map identPayload), dotted (v.build.map buildPayload)]

def readVersion (cs : List Char) : Option Version :=
  match splitOn '/' cs with
  | [core, pre, build] =>
    match splitOn '.' core with
    | [a, b, c] =>
      match readDecimal a, readDecimal b, readDecimal c, readDotted readIdent pre,
        readDotted readBuild build with
      | some x, some y, some z, some p, some q => some ⟨x, y, z, p, q⟩
      | _, _, _, _, _ => none
    | _ => none
  | _ => none

/-- A value's token: `<tag>:<payload>`. -/
def token : Val → List Char
  | .bytes b => 'b' :: ':' :: b.flatMap hexByte
  | .text s => 't' :: ':' :: (utf8 s).flatMap hexByte
  | .utf16 u => 'u' :: ':' :: u.flatMap hexUnit
  | .nat n => 'n' :: ':' :: decimal n
  | .int i => 'i' :: ':' :: (if i < 0 then '-' :: decimal i.natAbs else decimal i.natAbs)
  | .ordering .lt => ['o', ':', 'l', 't']
  | .ordering .eq => ['o', ':', 'e', 'q']
  | .ordering .gt => ['o', ':', 'g', 't']
  | .version v => 'v' :: ':' :: versionPayload v

/-- A token read as a value of type `t`. -/
def readToken : Ty → List Char → Option Val
  | .bytes, 'b' :: ':' :: cs => (unhexBytes cs).map .bytes
  | .text, 't' :: ':' :: cs => (unhexBytes cs).bind unutf8 |>.map .text
  | .utf16, 'u' :: ':' :: cs => (unhexUnits cs).map .utf16
  | .nat, 'n' :: ':' :: cs => (readDecimal cs).map .nat
  | .int, 'i' :: ':' :: cs =>
    if cs.head? == some '-' then
      match readDecimal (cs.drop 1) with
      | some (n + 1) => some (.int (-((n + 1 : Nat) : Int)))
      | _ => none
    else (readDecimal cs).map fun n => .int n
  | .ordering, ['o', ':', 'l', 't'] => some (.ordering .lt)
  | .ordering, ['o', ':', 'e', 'q'] => some (.ordering .eq)
  | .ordering, ['o', ':', 'g', 't'] => some (.ordering .gt)
  | .version, 'v' :: ':' :: cs => (readVersion cs).map .version
  | _, _ => none

/-! ## Lines (W1–W3) -/

/-- W1: a request line: the tokens in argument order, space-separated. -/
def encodeArgs (xs : List Val) : String := String.ofList (joinWith ' ' (xs.map token))

/-- A request line's tokens read against the argument types (before the print check). -/
def readArgs (ts : List Ty) (s : String) : Option (List Val) :=
  match ts with
  | [] => if s.toList.isEmpty then some [] else none
  | _ =>
    let toks := splitOn ' ' s.toList
    if toks.length == ts.length then (ts.zip toks).mapM fun p => readToken p.1 p.2 else none

/-- W1: a request line read against the signature's argument types: the values read, kept when
their types are `ts` + `encodeArgs` writes the very line. -/
def decodeArgs (ts : List Ty) (s : String) : Option (List Val) :=
  match readArgs ts s with
  | some xs => if xs.map Val.ty == ts && encodeArgs xs == s then some xs else none
  | none => none

/-- W2: a result line: `ok <token>`. -/
def printResult (v : Val) : String := String.ofList ('o' :: 'k' :: ' ' :: token v)

/-- W2: an optional result's `none`. -/
def printNone : String := String.ofList ['e', 'r', 'r']

/-- W2: a reply's line (`invalid` has none: no result line carries it). -/
def resultLine : Reply → String
  | .ok v => printResult v
  | .err => printNone
  | .invalid _ => ""

/-- W2: the replies a result type admits: a value of its type; `err` for an optional one. -/
def admits : RTy → Reply → Bool
  | .plain t, .ok v => v.ty == t
  | .option t, .ok v => v.ty == t
  | .option _, .err => true
  | _, _ => false

/-- A result line read (before the print check). -/
def readResult (rt : RTy) (s : String) : Option Reply :=
  match rt, s.toList with
  | .option _, ['e', 'r', 'r'] => some .err
  | .plain t, 'o' :: 'k' :: ' ' :: tok | .option t, 'o' :: 'k' :: ' ' :: tok =>
    (readToken t tok).map .ok
  | _, _ => none

/-- W2: a result line read against the result type: the reply read, kept when `rt` admits it +
its line is the very line. -/
def parseResult (rt : RTy) (s : String) : Option Reply :=
  match readResult rt s with
  | some r => if admits rt r && resultLine r == s then some r else none
  | none => none

/-! ## The native bridge (W3, W5) -/

/-- A served representation: its protocol type + the value conversions. -/
class Native (α : Type) where
  ty : Ty
  toVal : α → Val
  ofVal : Val → Option α

instance bytesNative : Native (List UInt8) where
  ty := .bytes
  toVal := .bytes
  ofVal
    | .bytes b => some b
    | _ => none

instance byteArrayNative : Native ByteArray where
  ty := .bytes
  toVal b := .bytes b.data.toList
  ofVal
    | .bytes b => some ⟨b.toArray⟩
    | _ => none

instance textNative : Native (List Char) where
  ty := .text
  toVal := .text
  ofVal
    | .text s => some s
    | _ => none

instance utf16Native : Native (List UInt16) where
  ty := .utf16
  toVal := .utf16
  ofVal
    | .utf16 u => some u
    | _ => none

instance natNative : Native Nat where
  ty := .nat
  toVal := .nat
  ofVal
    | .nat n => some n
    | _ => none

instance intNative : Native Int where
  ty := .int
  toVal := .int
  ofVal
    | .int i => some i
    | _ => none

instance orderingNative : Native Ordering where
  ty := .ordering
  toVal := .ordering
  ofVal
    | .ordering o => some o
    | _ => none

instance versionNative : Native Version where
  ty := .version
  toVal := .version
  ofVal
    | .version v => some v
    | _ => none

/-- A served result: its result type + its line. -/
class Answer (β : Type) where
  rty : RTy
  line : β → String

instance plainAnswer {β : Type} [Native β] : Answer β where
  rty := .plain (Native.ty β)
  line b := printResult (Native.toVal b)

instance optionAnswer {β : Type} [Native β] : Answer (Option β) where
  rty := .option (Native.ty β)
  line
    | some b => printResult (Native.toVal b)
    | none => printNone

/-- W5: a spec function served: its argument types, its result type + its application to the
decoded arguments (one per argument in order, each through `Native.ofVal`). -/
class Serve (f : Type) where
  args : List Ty
  rty : RTy
  call : f → List Val → Option String

instance resultServe {β : Type} [Answer β] : Serve β where
  args := []
  rty := Answer.rty β
  call b
    | [] => some (Answer.line b)
    | _ => none

instance argServe {α β : Type} [Native α] [Serve β] : Serve (α → β) where
  args := Native.ty α :: Serve.args β
  rty := Serve.rty β
  call f
    | v :: vs => (Native.ofVal v).bind fun a => Serve.call (f a) vs
    | [] => none

/-- W5: one request line answered by `f` (a line the decoder or `f`'s types refuse → `malformed`,
which `parseResult` never accepts). -/
def answer {F : Type} [Serve F] (f : F) (line : String) : String :=
  match decodeArgs (Serve.args F) line with
  | some vs => (Serve.call f vs).getD "malformed"
  | none => "malformed"

end FvdepCore.Oracle.Wire
