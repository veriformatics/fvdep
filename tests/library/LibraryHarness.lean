import Fvdep.Base64.Decode.V1_0_0
import Fvdep.Base64.DecodeUrl.V1_0_0
import Fvdep.Semver.Compare.V1_0_0
import Fvdep.Semver.Parse.V1_0_0
import FvdepCore.Protocol.Sig

namespace LibraryTest

open FvdepCore.Json
open FvdepCore.Protocol
open Fvdep.Semver.Version.V1_0_0

-- Independent transport: tags + length-prefixed payloads, wrapped in hex lines.
def digit (n : Nat) : Char := Char.ofNat (if n < 10 then n + 48 else n + 87)

def hex (b : ByteArray) : String :=
  b.data.foldl (fun s x => (s.push (digit (x.toNat / 16))).push (digit (x.toNat % 16))) ""

def unhex (s : String) : Except String ByteArray := do
  let mut hi : Option Nat := none
  let mut b := ByteArray.empty
  for c in s.toList do
    let n ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else throw "transport hex"
    match hi with
    | none => hi := some n
    | some h =>
      b := b.push (UInt8.ofNat (h * 16 + n))
      hi := none
  if hi.isSome then throw "transport odd hex"
  return b

def net (s : String) : ByteArray := s!"{s.utf8ByteSize}:".toUTF8 ++ s.toUTF8

partial def wire : Value → ByteArray
  | .null => "n".toUTF8
  | .bool b => (if b then "t" else "f").toUTF8
  | .int n => s!"i{n};".toUTF8
  | .str s => "s".toUTF8 ++ net s
  | .arr xs => xs.foldl (fun b x => b ++ wire x) s!"a{xs.length}:".toUTF8
  | .obj ms => ms.foldl (fun b p => b ++ net p.1 ++ wire p.2) s!"o{ms.length}:".toUTF8

partial def readUntil (b : ByteArray) (i : Nat) (stop : UInt8)
    (acc : ByteArray := ByteArray.empty) : Except String (String × Nat) := do
  if i ≥ b.size then throw "transport delimiter"
  let c := b[i]!
  if c == stop then
    let some s := String.fromUTF8? acc | throw "transport utf8"
    return (s, i + 1)
  readUntil b (i + 1) stop (acc.push c)

def count (b : ByteArray) (i : Nat) : Except String (Nat × Nat) := do
  let (s, j) ← readUntil b i 58
  let some n := s.toNat? | throw "transport count"
  return (n, j)

def textAt (b : ByteArray) (i : Nat) : Except String (String × Nat) := do
  let (n, j) ← count b i
  if j + n > b.size then throw "transport short string"
  let some s := String.fromUTF8? (b.extract j (j + n)) | throw "transport utf8"
  return (s, j + n)

partial def readWire (b : ByteArray) (i : Nat) : Except String (Value × Nat) := do
  if i ≥ b.size then throw "transport short value"
  match b[i]!.toNat with
  | 110 => return (.null, i + 1)
  | 102 => return (.bool false, i + 1)
  | 116 => return (.bool true, i + 1)
  | 105 =>
    let (s, j) ← readUntil b (i + 1) 59
    let some n := s.toInt? | throw "transport int"
    return (.int n, j)
  | 115 =>
    let (s, j) ← textAt b (i + 1)
    return (.str s, j)
  | 97 =>
    let (n, start) ← count b (i + 1)
    let mut xs := []
    let mut j := start
    for _ in [:n] do
      let (x, k) ← readWire b j
      xs := x :: xs
      j := k
    return (.arr xs.reverse, j)
  | 111 =>
    let (n, start) ← count b (i + 1)
    let mut ms := []
    let mut j := start
    for _ in [:n] do
      let (key, k) ← textAt b j
      let (x, next) ← readWire b k
      ms := (key, x) :: ms
      j := next
    return (.obj ms.reverse, j)
  | _ => throw "transport tag"

def str : Value → Except String String
  | .str s => .ok s
  | _ => .error "transport string"

def arr : Value → Except String (List Value)
  | .arr xs => .ok xs
  | _ => .error "transport array"

def nat : Value → Except String Nat
  | .int (.ofNat n) => .ok n
  | _ => .error "transport nat"

def field (ms : List (String × Value)) (key : String) : Except String Value :=
  match ms.find? (fun p => p.1 == key) with
  | some p => .ok p.2
  | none => .error s!"transport field {key}"

def identIn : Value → Except String Ident
  | .obj [("num", v)] => return .num (← nat v)
  | .obj [("alnum", .str s)] => .ok (.alnum s.toList)
  | _ => .error "transport ident"

def versionIn : Value → Except String Version
  | .obj ms => do
    return {
      major := ← nat (← field ms "major")
      minor := ← nat (← field ms "minor")
      patch := ← nat (← field ms "patch")
      pre := ← (← arr (← field ms "pre")).mapM identIn
      build := ← (← arr (← field ms "build")).mapM (fun x => return (← str x).toList)
    }
  | _ => .error "transport version"

def versionOut (v : Version) : Value :=
  .obj [
    ("build", .arr (v.build.map fun s => .str (String.ofList s))),
    ("major", .int (Int.ofNat v.major)),
    ("minor", .int (Int.ofNat v.minor)),
    ("patch", .int (Int.ofNat v.patch)),
    ("pre", .arr (v.pre.map fun x => match x with
      | .num n => .obj [("num", .int (Int.ofNat n))]
      | .alnum s => .obj [("alnum", .str (String.ofList s))]))]

def orderingOut : Ordering → Value
  | .lt => .str "lt"
  | .eq => .str "eq"
  | .gt => .str "gt"

def tyIn : String → Except String Ty
  | "bytes" => .ok .bytes
  | "text" => .ok .text
  | "utf16" => .ok .utf16
  | "nat" => .ok .nat
  | "int" => .ok .int
  | "ordering" => .ok .ordering
  | "version" => .ok .version
  | _ => .error "transport type"

def tyOut : Ty → Value
  | .bytes => .str "bytes"
  | .text => .str "text"
  | .utf16 => .str "utf16"
  | .nat => .str "nat"
  | .int => .str "int"
  | .ordering => .str "ordering"
  | .version => .str "version"

def valIn : Value → Except String Val
  | .arr [.str "bytes", .str s] => return .bytes (← unhex s).data.toList
  | .arr [.str "text", .str s] => .ok (.text s.toList)
  | .arr [.str "utf16", .arr xs] =>
    return .utf16 (← xs.mapM fun x => return UInt16.ofNat (← nat x))
  | .arr [.str "nat", v] => return .nat (← nat v)
  | .arr [.str "int", .int i] => .ok (.int i)
  | .arr [.str "ordering", .str "lt"] => .ok (.ordering .lt)
  | .arr [.str "ordering", .str "eq"] => .ok (.ordering .eq)
  | .arr [.str "ordering", .str "gt"] => .ok (.ordering .gt)
  | .arr [.str "version", v] => return .version (← versionIn v)
  | _ => .error "transport typed value"

def valOut : Val → Value
  | .bytes xs => .arr [.str "bytes", .str (hex ⟨xs.toArray⟩)]
  | .text xs => .arr [.str "text", .str (String.ofList xs)]
  | .utf16 xs => .arr [.str "utf16", .arr (xs.map fun x => .int (Int.ofNat x.toNat))]
  | .nat n => .arr [.str "nat", .int (Int.ofNat n)]
  | .int i => .arr [.str "int", .int i]
  | .ordering o => .arr [.str "ordering", orderingOut o]
  | .version v => .arr [.str "version", versionOut v]

def optional (v : Option Value) : Value := .arr v.toList

def specEncode := Fvdep.Base64.Encode.V1_0_0.encode

def specEncodeUrl := Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl

def specDecode := Fvdep.Base64.Decode.V1_0_0.decode

def specDecodeUrl := Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl

def specParse := Fvdep.Semver.Parse.V1_0_0.parse

def specCompare := Fvdep.Semver.Compare.V1_0_0.compare

def decoded (v : Option (List UInt8)) : Value :=
  optional (v.map fun b => .str (hex ⟨b.toArray⟩))

def signatureIn : Value → Except String Sig
  | .arr [.str op, .arr args, .arr [.str mode, .str result]] => do
    let t ← tyIn result
    let r ← match mode with
      | "plain" => pure (RTy.plain t)
      | "option" => pure (RTy.option t)
      | _ => throw "transport result type"
    return ⟨op, ← args.mapM (fun x => do tyIn (← str x)), r⟩
  | _ => .error "transport signature"

partial def exprIn : Value → Except String Lean.Expr
  | .str "Nat" => .ok (Lean.mkConst ``Nat)
  | .str "Int" => .ok (Lean.mkConst ``Int)
  | .str "UInt8" => .ok (Lean.mkConst ``UInt8)
  | .str "UInt16" => .ok (Lean.mkConst ``UInt16)
  | .str "Char" => .ok (Lean.mkConst ``Char)
  | .str "Ordering" => .ok (Lean.mkConst ``Ordering)
  | .str "Version" => .ok (Lean.mkConst ``Version)
  | .str "ByteArray" => .ok (Lean.mkConst ``ByteArray)
  | .str "String" => .ok (Lean.mkConst ``String)
  | .str "Bool" => .ok (Lean.mkConst ``Bool)
  | .str "Unit" => .ok (Lean.mkConst ``Unit)
  | .str "Prop" => .ok (.sort .zero)
  | .str "Type" => .ok (.sort (.succ .zero))
  | .str "dependent" =>
    .ok (.forallE `n (Lean.mkConst ``Nat) (.bvar 0) .default)
  | .arr [.str "arrow", a, b] =>
    return .forallE .anonymous (← exprIn a) (← exprIn b) .default
  | .arr [.str "implicit", a, b] =>
    return .forallE .anonymous (← exprIn a) (← exprIn b) .implicit
  | .arr [.str "list", a] =>
    return Lean.mkApp (Lean.mkConst ``List [.zero]) (← exprIn a)
  | .arr [.str "option", a] =>
    return Lean.mkApp (Lean.mkConst ``Option [.zero]) (← exprIn a)
  | .arr [.str "mdata", a] => return .mdata {} (← exprIn a)
  | _ => .error "transport expr"

def sigOut : Option (List Ty × RTy) → Value
  | none => .null
  | some (args, result) =>
    let r := match result with
      | .plain t => .arr [.str "plain", tyOut t]
      | .option t => .arr [.str "option", tyOut t]
    .arr [.arr (args.map tyOut), r]

partial def dispatch : Value → Except String Value
  | .arr [.str "base64", .arr inputs] => do
    return .arr (← inputs.mapM fun x => do
      let b := (← unhex (← str x)).data.toList
      let s := specEncode b
      let u := specEncodeUrl b
      return .arr [.str (String.ofList s), .str (String.ofList u),
        decoded (specDecode s), decoded (specDecodeUrl u)])
  | .arr [.str "spec", .str "encode", .str h] =>
    return .str (String.ofList (specEncode (← unhex h).data.toList))
  | .arr [.str "spec", .str "encodeUrl", .str h] =>
    return .str (String.ofList (specEncodeUrl (← unhex h).data.toList))
  | .arr [.str "spec", .str "decode", .str s] => .ok (decoded (specDecode s.toList))
  | .arr [.str "spec", .str "decodeUrl", .str s] => .ok (decoded (specDecodeUrl s.toList))
  | .arr [.str "spec", .str "parse", .str s] =>
    .ok (optional ((specParse s.toList).map versionOut))
  | .arr [.str "spec", .str "compare", a, b] =>
    return orderingOut (specCompare (← versionIn a) (← versionIn b))
  | .arr [.str "spec", .str "render", a] =>
    return .str (String.ofList (Fvdep.Semver.Parse.V1_0_0.render (← versionIn a)))
  | .arr [.str "encodeVal", x] => return encodeVal (← valIn x)
  | .arr [.str "decodeVal", .str t, x] =>
    return optional ((decodeVal (← tyIn t) x).map valOut)
  | .arr [.str "request", s, .str h] => do
    match decodeRequest (← signatureIn s) (← unhex h) with
    | .ok xs => return .arr [.str "ok", .arr (xs.map valOut)]
    | .error why => return .arr [.str "invalid", .str why]
  | .arr [.str "reply", .str "ok", x] =>
    return .str (hex (encodeReply (.ok (← valIn x))))
  | .arr [.str "reply", .str "none"] => return .str (hex (encodeReply .err))
  | .arr [.str "reply", .str "invalid", .str s] =>
    return .str (hex (encodeReply (.invalid s)))
  | .arr [.str "lines", .str h] =>
    return .arr ((lines (← unhex h)).map fun b => .str (hex b))
  | .arr [.str "sig", e] => return sigOut (sigOf (← exprIn e))
  | .arr [.str "batch", .arr xs] => return .arr (← xs.mapM dispatch)
  | _ => .error "transport command"

def one (s : String) : Except String String := do
  let b ← unhex s
  let (v, j) ← readWire b 0
  if j != b.size then throw "transport trailing"
  return hex (wire (← dispatch v))

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match one line.trimAscii.toString with
    | .ok s => stdout.putStrLn s
    | .error why =>
      IO.eprintln why
      return 2
  return 0

end LibraryTest
