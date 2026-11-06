import Fvdep
/-!
Reference oracle compiled from the library. Protocol = adapter protocol (`PROTOCOL.md`):
argv[1] = a contract module `<dep>.<op>@<version>` or a package profile `<eco>:<pkg>@<version>`;
stdin lines `op\targ[\targ]`; stdout one line each:
`ok\t<result>` | `err` (rejected input) | `unsupported` (op not served by this handler).
Bytes travel as lowercase hex.
-/
open Fvdep

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def toHex (bs : List Nat) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b / 16), hexDigit (b % 16)])
def hexVal (c : Char) : Option Nat := "0123456789abcdef".toList.idxOf? c
def fromHex : List Char → Option (List Nat)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexVal a; let y ← hexVal b; let t ← fromHex rest; some ((x * 16 + y) :: t)
  | _ => none

def okOr (r : Option String) : String := match r with | some s => s!"ok\t{s}" | none => "err"

abbrev Handler := String → List String → String

/-- Unary byte → text op. -/
def enc (f : List Nat → List Char) : Handler := fun _ args => match args with
  | [h] => okOr ((fromHex h.toList).map (String.ofList ∘ f))
  | _ => "unsupported"

/-- Unary text → bytes op. -/
def dec (f : List Char → Option (List Nat)) : Handler := fun _ args => match args with
  | [s] => okOr ((f s.toList).map toHex)
  | _ => "unsupported"

/-- One handler per op name; other names → `unsupported`. -/
def ops (hs : List (String × Handler)) : Handler := fun op args =>
  match hs.lookup op with | some h => h op args | none => "unsupported"

def semverParse : Handler := fun _ args => match args with
  | [s] => okOr ((Semver.Parse.V1_0_0.parseStr s).map Semver.Parse.V1_0_0.renderStr)
  | _ => "unsupported"

def semverCompare : Handler := fun _ args => match args with
  | [a, b] => okOr do
    let x ← Semver.Parse.V1_0_0.parseStr a; let y ← Semver.Parse.V1_0_0.parseStr b
    some (match Semver.Compare.V1_0_0.compare x y with | .lt => "lt" | .eq => "eq" | .gt => "gt")
  | _ => "unsupported"

def handler : String → Option Handler
  | "base64.encode@1.0.0" => some (ops [("encode", enc Base64.Encode.V1_0_0.encode)])
  | "base64.decode@1.0.0" => some (ops [("decode", dec Base64.Decode.V1_0_0.decode)])
  | "base64.decode@1.1.0" => some (ops [("decode", dec Base64.Decode.V1_1_0.decode)])
  | "base64.encode_url@1.0.0" => some (ops [("encode_url", enc Base64.EncodeUrl.V1_0_0.encodeUrl)])
  | "base64.decode_url@1.0.0" => some (ops [("decode_url", dec Base64.DecodeUrl.V1_0_0.decodeUrl)])
  | "semver.parse@1.0.0" => some (ops [("parse", semverParse)])
  | "semver.compare@1.0.0" => some (ops [("compare", semverCompare)])
  | "cpython:base64@3.14" => some (ops [("encode", enc Profiles.CpythonBase64.V3_14.encode),
      ("decode", dec Profiles.CpythonBase64.V3_14.decode)])
  | "npm:base64-js@1.5.1" => some (ops [("encode", enc Profiles.NpmBase64Js.V1_5_1.encode),
      ("decode", dec Profiles.NpmBase64Js.V1_5_1.decode)])
  | "crates:base64@0.22.1" => some (ops [("encode", enc Profiles.CratesBase64.V0_22_1.encode),
      ("decode", dec Profiles.CratesBase64.V0_22_1.decode),
      ("encode_url", enc Profiles.CratesBase64.V0_22_1.encodeUrl),
      ("decode_url", dec Profiles.CratesBase64.V0_22_1.decodeUrl)])
  | _ => none

partial def loop (h : Handler) (i : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← i.getLine
  if line.isEmpty then return
  let line := String.ofList (line.toList.filter (· != '\n'))
  match line.splitOn "\t" with
  | op :: args => o.putStrLn (h op args)
  | [] => o.putStrLn "unsupported"
  o.flush
  loop h i o

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [spec] => match handler spec with
    | some h => loop h (← IO.getStdin) (← IO.getStdout); return 0
    | none => IO.eprintln s!"fvdep-oracle: unknown module or profile {spec}"; return 2
  | _ => IO.eprintln "usage: fvdep-oracle <module>@<version> | <eco>:<pkg>@<version>"; return 2
