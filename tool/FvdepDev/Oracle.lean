import Fvdep.Base64.Decode.V1_0_0
import Fvdep.Base64.DecodeUrl.V1_0_0
import Fvdep.Semver.Compare.V1_0_0
import Fvdep.Semver.Parse.V1_0_0
import FvdepCore.Protocol

/-! `fvdep-dev oracle <id>@<ver>` (contract U4 B5): adapter protocol v1 over the six launch specs
compiled in — the spec evidence's driver (tester-1's oracle cases + spec mutants); never shipped.
The shipped `fvdep oracle` (U5b) evaluates a snapshot's spec instead of a compiled-in one. -/

namespace FvdepDev.Oracle

open FvdepCore.Protocol

/-- A served spec: its signature + its function on typed arguments (`none` = arguments that do
not fit the signature: `decodeRequest` never lets one through). -/
structure Served where
  sig : Sig
  eval : List Val → Option Reply

def optBytes : Option (List UInt8) → Reply
  | some b => .ok (.bytes b)
  | none => .err

def table : List (String × Served) :=
  [("base64.encode@1.0.0",
      ⟨⟨"encode", [.bytes], .plain .text⟩, fun
        | [.bytes b] => some (.ok (.text (Fvdep.Base64.Encode.V1_0_0.encode b)))
        | _ => none⟩),
    ("base64.decode@1.0.0",
      ⟨⟨"decode", [.text], .option .bytes⟩, fun
        | [.text s] => some (optBytes (Fvdep.Base64.Decode.V1_0_0.decode s))
        | _ => none⟩),
    ("base64.encode_url@1.0.0",
      ⟨⟨"encodeUrl", [.bytes], .plain .text⟩, fun
        | [.bytes b] => some (.ok (.text (Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl b)))
        | _ => none⟩),
    ("base64.decode_url@1.0.0",
      ⟨⟨"decodeUrl", [.text], .option .bytes⟩, fun
        | [.text s] => some (optBytes (Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl s))
        | _ => none⟩),
    ("semver.parse@1.0.0",
      ⟨⟨"parse", [.text], .option .version⟩, fun
        | [.text s] =>
          some <|
            match Fvdep.Semver.Parse.V1_0_0.parse s with
            | some v => .ok (.version v)
            | none => .err
        | _ => none⟩),
    ("semver.compare@1.0.0",
      ⟨⟨"compare", [.version, .version], .plain .ordering⟩, fun
        | [.version a, .version b] =>
          some (.ok (.ordering (Fvdep.Semver.Compare.V1_0_0.compare a b)))
        | _ => none⟩)]

def usage : String := "usage: fvdep-dev oracle <id>@<version>\n"

def serve (s : Served) (line : ByteArray) : Reply :=
  match decodeRequest s.sig line with
  | .error reason => .invalid reason
  | .ok args => (s.eval args).getD (.invalid "arguments outside the signature")

def run : List String → IO UInt32
  | [target] => do
    match table.lookup target with
    | none =>
      IO.eprintln s!"fvdep-dev oracle: unknown target {target}"
      return 2
    | some s =>
      let input ← (← IO.getStdin).readBinToEnd
      let stdout ← IO.getStdout
      for line in lines input do
        stdout.write (encodeReply (serve s line))
      stdout.flush
      return 0
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Oracle
