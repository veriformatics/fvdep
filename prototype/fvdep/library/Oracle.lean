import Fvdep.Base64.V1_1_0
import Fvdep.Semver.V1_0_0
/-!
Reference oracle compiled from the specs. Protocol (= adapter protocol, `docs/PROTOCOL.md`):
argv[1] = `<dep>@<version>`; stdin lines `op\targ[\targ]`; stdout one line each:
`ok\t<result>` | `err` (spec rejects the input) | `unsupported` (op not in this spec version).
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

def base64 (url : Bool) (op : String) (args : List String) : String :=
  open Base64.V1_1_0 in
  match op, args with
  | "encode", [h] => okOr ((fromHex h.toList).map encodeStr)
  | "decode", [s] => okOr ((decodeStr s).map toHex)
  | "encode_url", [h] => if url then okOr ((fromHex h.toList).map encodeUrlStr) else "unsupported"
  | "decode_url", [s] => if url then okOr ((decodeUrlStr s).map toHex) else "unsupported"
  | _, _ => "unsupported"

def semver (op : String) (args : List String) : String :=
  open Semver.V1_0_0 in
  match op, args with
  | "parse", [s] => okOr ((parseStr s).map renderStr)
  | "compare", [a, b] => okOr do
    let x ← parseStr a; let y ← parseStr b
    some (match compare x y with | .lt => "lt" | .eq => "eq" | .gt => "gt")
  | _, _ => "unsupported"

def handler : String → Option (String → List String → String)
  | "base64@1.0.0" => some (base64 false)
  | "base64@1.1.0" => some (base64 true)
  | "semver@1.0.0" => some semver
  | _ => none

partial def loop (h : String → List String → String) (i : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
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
    | none => IO.eprintln s!"fvdep-oracle: unknown spec {spec}"; return 2
  | _ => IO.eprintln "usage: fvdep-oracle <dep>@<version>"; return 2
