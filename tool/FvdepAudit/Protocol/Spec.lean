import FvdepAudit.Hash.Spec
import FvdepAudit.Json.Spec
import FvdepCore.Protocol.Sig

/-! Specs for adapter protocol v1, the oracle side (contract `docs/contracts/U4-library.md` B4;
`docs/interface.md` §8), written from §8 apart from `FvdepCore.Protocol`'s code: each value class's
wire layout, the request + reply objects, the line rule, the type table. -/

namespace FvdepAudit.Protocol.Spec

open FvdepCore.Json FvdepCore.Protocol Fvdep.Semver.Version.V1_0_0

/-- §8's integer bound: 2^53 − 1. -/
def safe : Nat := 9007199254740991

/-- §8 bytes: two lowercase hex digits per byte, high nibble first (H1's text). -/
def bytesSpec (b : List UInt8) : String := FvdepAudit.Hash.Spec.hexSpec ⟨b.toArray⟩

/-- §8 `Nat`: an integer within the bound, else the canonical decimal (digits, no leading zero). -/
def natSpec (n : Nat) : Value :=
  if n ≤ safe then .int n else .str (String.ofList (FvdepCore.Ids.decimal n))

/-- §8 `Int`: an integer within ±bound, else the canonical decimal, `-` first for a negative
value. -/
def intSpec (i : Int) : Value :=
  if i.natAbs ≤ safe then .int i
  else .str (String.ofList ((if i < 0 then ['-'] else []) ++ FvdepCore.Ids.decimal i.natAbs))

def orderingSpec : Ordering → String
  | .lt => "lt"
  | .eq => "eq"
  | .gt => "gt"

/-- A tagged identifier: `num` and `alnum` never share an encoding. -/
def identSpec : Ident → Value
  | .num n => .obj [("num", natSpec n)]
  | .alnum s => .obj [("alnum", .str (String.ofList s))]

/-- §8 `Version`: exactly `build`, `major`, `minor`, `patch`, `pre`, in key order. -/
def versionSpec (v : Version) : Value :=
  .obj
    [("build", .arr (v.build.map fun b => .str (String.ofList b))), ("major", natSpec v.major),
      ("minor", natSpec v.minor), ("patch", natSpec v.patch), ("pre", .arr (v.pre.map identSpec))]

/-- A value's wire layout. -/
def valSpec : Val → Value
  | .bytes b => .str (bytesSpec b)
  | .text s => .str (String.ofList s)
  | .utf16 u => .arr (u.map fun c => .int c.toNat)
  | .nat n => natSpec n
  | .int i => intSpec i
  | .ordering o => .str (orderingSpec o)
  | .version v => versionSpec v

/-- A request object: exactly `args` + `op`. -/
def requestLayout (op : String) (args : List Value) : Value :=
  .obj [("args", .arr args), ("op", .str op)]

/-- A reply object: exactly one of `ok`, `err` (text `none`), `invalid`. -/
def replyLayout : Reply → Value
  | .ok v => .obj [("ok", valSpec v)]
  | .err => .obj [("err", .str "none")]
  | .invalid reason => .obj [("invalid", .str reason)]

/-- The segments between LF bytes (one more than the LFs). -/
def segments : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
    match segments rest with
    | s :: ss => if b == 0x0A then [] :: s :: ss else (b :: s) :: ss
    | [] => [[b]]

/-- §8 + B3's lines: the LF-separated segments, the last dropped when empty (EOF adds no line). -/
def linesSpec (l : List UInt8) : List (List UInt8) :=
  let ss := segments l
  if ss.getLast? = some [] then ss.dropLast else ss

/-- `e` with its outer metadata layers removed (the kernel reads `mdata d e` as `e`). -/
def stripMData : Lean.Expr → Lean.Expr
  | .mdata _ e => stripMData e
  | e => e

/-- B1's type table over Lean types: `Expr` shapes without reduction, metadata transparent at
every position the table reads. -/
inductive TyIs : Lean.Expr → Ty → Prop
  |
  listUInt8 (e f x : Lean.Expr) (u : Lean.Level) :
    stripMData e = .app f x →
      stripMData f = .const ``List [u] → stripMData x = .const ``UInt8 [] → TyIs e .bytes
  |
  listChar (e f x : Lean.Expr) (u : Lean.Level) :
    stripMData e = .app f x →
      stripMData f = .const ``List [u] → stripMData x = .const ``Char [] → TyIs e .text
  |
  listUInt16 (e f x : Lean.Expr) (u : Lean.Level) :
    stripMData e = .app f x →
      stripMData f = .const ``List [u] → stripMData x = .const ``UInt16 [] → TyIs e .utf16
  | byteArray (e : Lean.Expr) : stripMData e = .const ``ByteArray [] → TyIs e .bytes
  | nat (e : Lean.Expr) : stripMData e = .const ``Nat [] → TyIs e .nat
  | int (e : Lean.Expr) : stripMData e = .const ``Int [] → TyIs e .int
  | ordering (e : Lean.Expr) : stripMData e = .const ``Ordering [] → TyIs e .ordering
  |
  version (e : Lean.Expr) :
    stripMData e = .const ``Fvdep.Semver.Version.V1_0_0.Version [] → TyIs e .version

/-- A result: `Option X` → `option`, any other encodable type → `plain`. -/
inductive RTyIs : Lean.Expr → RTy → Prop
  |
  option (e f x : Lean.Expr) (u : Lean.Level) (t : Ty) :
    stripMData e = .app f x → stripMData f = .const ``Option [u] → TyIs x t → RTyIs e (.option t)
  | plain (e : Lean.Expr) (t : Ty) : TyIs e t → RTyIs e (.plain t)

/-- A spec type: non-dependent arrows from encodable arguments to an encodable result (metadata
transparent: around the whole type + each codomain). -/
inductive SigIs : Lean.Expr → List Ty → RTy → Prop
  |
  last (n : Lean.Name) (a b : Lean.Expr) (bi : Lean.BinderInfo) (t : Ty) (r : RTy) :
    TyIs a t → b.hasLooseBVars = false → RTyIs b r → SigIs (.forallE n a b bi) [t] r
  |
  cons (n : Lean.Name) (a b : Lean.Expr) (bi : Lean.BinderInfo) (t : Ty) (ts : List Ty) (r : RTy) :
    TyIs a t → b.hasLooseBVars = false → SigIs b ts r → SigIs (.forallE n a b bi) (t :: ts) r
  |
  mdata (d : Lean.MData) (e : Lean.Expr) (ts : List Ty) (r : RTy) :
    SigIs e ts r → SigIs (.mdata d e) ts r

end FvdepAudit.Protocol.Spec
