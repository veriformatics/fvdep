import Fvdep.Base64.Decode.V1_0_0
import Fvdep.Base64.DecodeUrl.V1_0_0
import Fvdep.Semver.Compare.V1_0_0
import Fvdep.Semver.Parse.V1_0_0
import FvdepCore.Cli
import FvdepCore.Protocol
import FvdepIO.Run

/-! Never shipped. `fvdep-dev spec <id>@<ver>` (contract U4 B5): adapter protocol v1 over the six
launch specs compiled in — the spec evidence's driver (tester-5's library suite + spec mutants).
`fvdep-dev oracle <target> [--project <dir>] [--limit <name>=<n>]… [--replies <file>]` (contract
U5b Q3): the shipped `fvdep oracle` plan + interpreter under T overrides; `--replies` = the evaluate
effect answers the file's bytes (the evaluation step is not run), so malformed, missing, extra +
mistyped driver lines reach the merge through the command path. -/

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

def usage : String :=
  "usage: fvdep-dev spec <id>@<version>\n" ++
    "       fvdep-dev oracle <target> [--project <dir>] [--limit <name>=<n>]... " ++
    "[--replies <file>]\n"

def serve (s : Served) (line : ByteArray) : Reply :=
  match decodeRequest s.sig line with
  | .error reason => .invalid reason
  | .ok args => (s.eval args).getD (.invalid "arguments outside the signature")

def runSpec : List String → IO UInt32
  | [target] => do
    match table.lookup target with
    | none =>
      IO.eprintln s!"fvdep-dev spec: unknown target {target}"
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

/-- The oracle seam's options. -/
structure Opts where
  target : Option String := none
  project : Option String := none
  limits : FvdepCore.Oracle.Command.Limits := {}
  replies : Option String := none

def parse (o : Opts) : List String → Option Opts
  | [] => some o
  | "--project" :: d :: rest =>
    if o.project.isNone then parse { o with project := some d } rest else none
  | "--limit" :: kv :: rest =>
    match kv.splitOn "=" with
    | [k, v] => (v.toNat?.bind (o.limits.set k)).bind fun l => parse { o with limits := l } rest
    | _ => none
  | "--replies" :: f :: rest =>
    if o.replies.isNone then parse { o with replies := some f } rest else none
  | t :: rest =>
    if !t.startsWith "-" && o.target.isNone then parse { o with target := some t } rest else none

/-- `fvdep-dev oracle …` (Q3). -/
def run (args : List String) : IO UInt32 := do
  let fail : IO UInt32 := do
    IO.eprint usage
    return 2
  match parse {} args with
  | some { target := some t, project, limits, replies } =>
    match FvdepCore.Oracle.Target.parse t with
    | none =>
      fail
    | some tgt =>
      let r ←
        match replies with
        | some f =>
          some <$> IO.FS.readBinFile f
        | none =>
          pure none
      FvdepIO.executeWith r (FvdepCore.Oracle.Command.plan FvdepCore.Cli.sha limits tgt project)
  | _ =>
    fail

end FvdepDev.Oracle
