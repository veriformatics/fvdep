import FvdepCore.Oracle

/-! Fuzz target `oracle-result` (contract U5b W4, Q4): byte 0 even = raw (bytes 2.. as a line, when
UTF-8, through `parseResult` + `decodeArgs` against types from byte 1: no panic, no hang; an
accepted reply or argument list prints back to the very line, else panic); odd = generated (a value
of the type byte 1 picks, built from the rest, printed by `printResult` + `encodeArgs`, read back:
a mismatch panics). -/

namespace FvdepFuzz

open FvdepCore.Protocol FvdepCore.Oracle Fvdep.Semver.Version.V1_0_0

/-- Byte `i` of `b`, 0 past the end. -/
def byteAt (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then b[i].toNat else 0

def tyOf (n : Nat) : Ty :=
  match n % 7 with
  | 0 => .bytes
  | 1 => .text
  | 2 => .utf16
  | 3 => .nat
  | 4 => .int
  | 5 => .ordering
  | _ => .version

def rtyOf (n : Nat) : RTy := if n % 2 == 0 then .plain (tyOf (n / 2)) else .option (tyOf (n / 2))

/-- Characters across UTF-8's 1–4 byte forms + the line's separators. -/
def charOf (n : Nat) : Char :=
  ['a', 'Z', '0', ' ', ':', '/', '.', '-', '\n', 'é', '中', '😀', '\x00', 'x'].getD (n % 14) 'a'

/-- A value of type `t` from the bytes at `i`. -/
def valOf (b : ByteArray) (t : Ty) (i : Nat) : Val :=
  let n := byteAt b i % 6
  let xs := (List.range n).map fun k => byteAt b (i + 1 + k)
  let big := xs.foldl (fun a x => a * 256 + x) 0
  match t with
  | .bytes => .bytes (xs.map (·.toUInt8))
  | .text => .text (xs.map charOf)
  | .utf16 =>
    .utf16 <|
      (List.range (n / 2)).map fun k => (xs.getD (2 * k) 0 * 256 + xs.getD (2 * k + 1) 0).toUInt16
  | .nat => .nat big
  | .int => .int (if byteAt b (i + 7) % 2 == 0 then big else -(big : Int) - 1)
  | .ordering => .ordering (if big % 3 == 0 then .lt else if big % 3 == 1 then .eq else .gt)
  | .version =>
    let pre :=
      xs.map fun x => if x % 2 == 0 then Ident.num x else .alnum ((List.range (x % 3)).map charOf)
    .version ⟨big, byteAt b (i + 7), byteAt b (i + 8), pre, (xs.take 2).map fun x => [charOf x]⟩

@[export fvdep_fuzz_oracle]
def oracleTarget (b : ByteArray) : UInt8 :=
  let rt := rtyOf (byteAt b 1)
  let t :=
    match rt with
    | .plain t | .option t => t
  if byteAt b 0 % 2 == 0 then
    match String.fromUTF8? (b.extract 2 b.size) with
    | some s =>
      let r :=
        match Wire.parseResult rt s with
        | some r => if Wire.resultLine r == s then 0 else panic! "oracle-result: a reply misprints"
        | none => 0
      let a :=
        match Wire.decodeArgs [t, .nat] s with
        | some xs => if Wire.encodeArgs xs == s then 0 else panic! "oracle-result: args misprint"
        | none => 0
      r + a
    | none => 0
  else
    let v := valOf b t 2
    let w := valOf b (tyOf (byteAt b 9)) 10
    let line := Wire.printResult v
    let ok :=
      Wire.parseResult (.plain v.ty) line == some (.ok v) &&
        Wire.parseResult (.option v.ty) line == some (.ok v) &&
        Wire.parseResult (.option v.ty) Wire.printNone == some .err &&
        Wire.decodeArgs [v.ty, w.ty] (Wire.encodeArgs [v, w]) == some [v, w]
    if ok then 0 else panic! "oracle-result: a generated value did not read back"

end FvdepFuzz
