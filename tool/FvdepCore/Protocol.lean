import Fvdep.Semver.Version.V1_0_0
import FvdepCore.Hash.Frame
import FvdepCore.Ids
import FvdepCore.Json

/-! Adapter protocol v1 (`docs/interface.md` §8), the oracle side (contract
`docs/contracts/U4-library.md` B): typed values, request lines, replies, line framing. Requests ride
J's profile (J1 bounds); replies print whole (a result is never clipped for its size). -/

namespace FvdepCore.Protocol

open Fvdep.Semver.Version.V1_0_0

/-- §8's value types. -/
inductive Ty where
  | bytes
  | text
  | utf16
  | nat
  | int
  | ordering
  | version
  deriving DecidableEq, Repr

/-- A result type: a value, or an optional value (`none` = the reply `err`). -/
inductive RTy where
  | plain (t : Ty)
  | option (t : Ty)
  deriving DecidableEq, Repr

/-- A typed value. -/
inductive Val where
  | bytes (b : List UInt8)
  | text (s : List Char)
  | utf16 (u : List UInt16)
  | nat (n : Nat)
  | int (i : Int)
  | ordering (o : Ordering)
  | version (v : Version)
  deriving DecidableEq, Repr

/-- A value's type (`HasTy x t` ⟺ `x.ty = t`). -/
def Val.ty : Val → Ty
  | .bytes _ => .bytes
  | .text _ => .text
  | .utf16 _ => .utf16
  | .nat _ => .nat
  | .int _ => .int
  | .ordering _ => .ordering
  | .version _ => .version

/-- An operation: its name, argument types (at least one) + result type. -/
structure Sig where
  op : String
  args : List Ty
  result : RTy
  deriving DecidableEq, Repr

/-- A reply: a result, an optional result's `none` (wire `{"err":"none"}`), or a refused request. -/
inductive Reply where
  | ok (v : Val)
  | err
  | invalid (reason : String)
  deriving DecidableEq, Repr

/-! ## Values (§8) -/

/-- A natural number: a JSON integer within 2^53 − 1, else its canonical decimal as a string. -/
def encodeNat (n : Nat) : Json.Value :=
  if n ≤ Json.maxInt then .int n else .str (String.ofList (Ids.decimalFast n))

/-- An integer: a JSON integer within ±(2^53 − 1), else its canonical decimal (`-` for a negative
value) as a string. -/
def encodeInt (i : Int) : Json.Value :=
  if i.natAbs ≤ Json.maxInt then .int i
  else
    if i < 0 then .str (String.ofList ('-' :: Ids.decimalFast i.natAbs))
    else .str (String.ofList (Ids.decimalFast i.natAbs))

def encodeOrdering : Ordering → Json.Value
  | .lt => .str "lt"
  | .eq => .str "eq"
  | .gt => .str "gt"

def encodeIdent : Ident → Json.Value
  | .num n => .obj [("num", encodeNat n)]
  | .alnum s => .obj [("alnum", .str (String.ofList s))]

/-- A version: its five members in key order (`build`, `major`, `minor`, `patch`, `pre`). -/
def encodeVersion (v : Version) : Json.Value :=
  .obj
    [("build", .arr (v.build.map fun b => .str (String.ofList b))), ("major", encodeNat v.major),
      ("minor", encodeNat v.minor), ("patch", encodeNat v.patch),
      ("pre", .arr (v.pre.map encodeIdent))]

/-- A value's §8 encoding. -/
def encodeVal : Val → Json.Value
  | .bytes b => .str (Hash.hex ⟨b.toArray⟩)
  | .text s => .str (String.ofList s)
  | .utf16 u => .arr (u.map fun c => .int c.toNat)
  | .nat n => encodeNat n
  | .int i => encodeInt i
  | .ordering o => encodeOrdering o
  | .version v => encodeVersion v

/-- Lowercase hex digit pairs → bytes. -/
def unhex : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest => do
    let h ← Ids.hexOf? hi
    let l ← Ids.hexOf? lo
    let t ← unhex rest
    some ((h.val * 16 + l.val).toUInt8 :: t)
  | [_] => none

def decodeNat : Json.Value → Option Nat
  | .int n => if 0 ≤ n ∧ n ≤ Json.maxInt then some n.toNat else none
  | .str s =>
    match Ids.parseNat s.toList with
    | some n => if Json.maxInt < n then some n else none
    | none => none
  | _ => none

def decodeInt : Json.Value → Option Int
  | .int n => if n.natAbs ≤ Json.maxInt then some n else none
  | .str s =>
    match s.toList with
    | '-' :: ds =>
      match Ids.parseNat ds with
      | some n => if Json.maxInt < n then some (-(n : Int)) else none
      | none => none
    | ds =>
      match Ids.parseNat ds with
      | some n => if Json.maxInt < n then some n else none
      | none => none
  | _ => none

def decodeOrdering : Json.Value → Option Ordering
  | .str "lt" => some .lt
  | .str "eq" => some .eq
  | .str "gt" => some .gt
  | _ => none

def decodeUnit (v : Json.Value) : Option UInt16 :=
  match v with
  | .int n => if 0 ≤ n ∧ n ≤ 65535 then some n.toNat.toUInt16 else none
  | _ => none

def decodeIdent : Json.Value → Option Ident
  | .obj [("num", x)] => (decodeNat x).map .num
  | .obj [("alnum", .str s)] => some (.alnum s.toList)
  | _ => none

def decodeText : Json.Value → Option (List Char)
  | .str s => some s.toList
  | _ => none

/-- A version: an object holding exactly the five members (J's decoded objects list their members
in ascending key order, keys unique). -/
def decodeVersion : Json.Value → Option Version
  |
  .obj
      [("build", .arr build), ("major", major), ("minor", minor), ("patch", patch),
        ("pre", .arr pre)] =>
    do
    let build ← build.mapM decodeText
    let major ← decodeNat major
    let minor ← decodeNat minor
    let patch ← decodeNat patch
    let pre ← pre.mapM decodeIdent
    some { major, minor, patch, pre, build }
  | _ => none

/-- The value of type `t` a JSON value encodes, if any. -/
def decodeVal : Ty → Json.Value → Option Val
  | .bytes, .str s => (unhex s.toList).map .bytes
  | .text, .str s => some (.text s.toList)
  | .utf16, .arr xs => (xs.mapM decodeUnit).map .utf16
  | .nat, v => (decodeNat v).map .nat
  | .int, v => (decodeInt v).map .int
  | .ordering, v => (decodeOrdering v).map .ordering
  | .version, v => (decodeVersion v).map .version
  | _, _ => none

/-! ## Requests, replies, lines -/

/-- Each argument decoded at its type, in order. -/
def decodeArgs : List Ty → List Json.Value → Option (List Val)
  | [], [] => some []
  | t :: ts, a :: as => do
    let x ← decodeVal t a
    let xs ← decodeArgs ts as
    some (x :: xs)
  | _, _ => none

/-- A request line (its bytes, LF excluded) → its typed arguments, or why it is refused. -/
def decodeRequest (sig : Sig) (line : ByteArray) : Except String (List Val) :=
  match Json.decode line with
  | .error .malformed => .error "not a JSON text"
  | .error .tooLarge => .error "beyond the codec limits"
  | .error (.duplicateKey _) => .error "a repeated key"
  | .ok (.obj [("args", .arr args), ("op", .str op)]) =>
    if op != sig.op then .error "unknown op"
    else
      if args.length != sig.args.length then .error "wrong number of arguments"
      else
        match decodeArgs sig.args args with
        | some xs => .ok xs
        | none => .error "an argument outside its encoding"
  | .ok _ => .error "not an object with exactly `args` + `op`"

/-- A reply's JSON value. -/
def replyValue : Reply → Json.Value
  | .ok v => .obj [("ok", encodeVal v)]
  | .err => .obj [("err", .str "none")]
  | .invalid reason => .obj [("invalid", .str reason)]

/-- A reply line: canonical JSON + LF. -/
def encodeReply (r : Reply) : ByteArray := (Json.print (replyValue r)).push 0x0A

/-- Lines of a byte list: split at LF; a nonempty final fragment = one more line; EOF adds none. -/
def splitLines : List UInt8 → List UInt8 → List (List UInt8)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | b :: rest, acc =>
    if b == 0x0A then acc.reverse :: splitLines rest [] else splitLines rest (b :: acc)

/-- The request lines of an input: split at LF (each line, the empty one included, is a request);
a nonempty final fragment without LF is one request; EOF adds none. -/
def lines (input : ByteArray) : List ByteArray :=
  (splitLines input.data.toList []).map fun l => ⟨l.toArray⟩

end FvdepCore.Protocol
