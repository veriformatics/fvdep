import FvdepDev.Sandbox
import FvdepIO.Phase
import FvdepIO.Profile
import FvdepIO.Snapshot

/-! `fvdep-dev profile check` (contract `docs/contracts/U6-profile.md` D1; never shipped): one batch
through the shipped profile step — S1's snapshot, T1's tools, the request (P5a), the step (or
`--results`: a record's bytes, no spawn; `--child`: another program staged as `fvdep-parse`), P5c,
P5b's intake + B3 — reported line by line (interface §1's line rule). -/

namespace FvdepDev.ProfileCheck

open FvdepCore.Profile FvdepDev.Sandbox

def usage : String :=
  "usage: fvdep-dev profile check --role consumer|library [--library <dir>] " ++
    "[--limit <name>=<n>]... [--results <file> | --child <file>] <src dir> <module>...\n"

/-- D1's options: P6's limits (`limits`, `seconds`) + the step's `frameBytes`/`fileBytes`. -/
structure Options where
  role : Option Role := none
  library : Option String := none
  limits : Limits := {}
  seconds : Nat := 120
  frameBytes : Option Nat := none
  fileBytes : Option Nat := none
  results : Option String := none
  child : Option String := none
  positional : List String := []

/-- J's integer range: `n` ≤ 2^53 − 1. -/
def jMax : Nat := 9007199254740991

/-- `--limit <name>=<n>`: a P6 or step limit, n a canonical decimal in 1..2^53 − 1. -/
def setLimit (o : Options) (v : String) : Except String Options :=
  match v.splitOn "=" with
  | [name, n] =>
    match (if isPositive n then n.toNat? else none) with
    | some k =>
      if jMax < k then .error s!"--limit {v}: the value passes 2^53 - 1"
      else
        match name with
        | "depth" => .ok { o with limits := { o.limits with depth := k } }
        | "nodes" => .ok { o with limits := { o.limits with nodes := k } }
        | "batchNodes" => .ok { o with limits := { o.limits with batchNodes := k } }
        | "seconds" => .ok { o with seconds := k }
        | "frameBytes" => .ok { o with frameBytes := some k }
        | "fileBytes" => .ok { o with fileBytes := some k }
        | _ => .error s!"--limit names no limit {name}"
    | none => .error s!"--limit {v}: not a whole number ≥ 1"
  | _ => .error s!"--limit takes <name>=<n>, got {v}"

def parse (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--role" :: "consumer" :: rest => parse { o with role := some .consumer } rest
  | "--role" :: "library" :: rest => parse { o with role := some .library } rest
  | "--library" :: d :: rest => parse { o with library := some d } rest
  | "--results" :: f :: rest => parse { o with results := some f } rest
  | "--child" :: f :: rest => parse { o with child := some f } rest
  | "--limit" :: v :: rest =>
    match setLimit o v with
    | .ok o => parse o rest
    | .error e => .error e
  | a :: rest =>
    if a.startsWith "--" then .error s!"unknown or incomplete option {a}"
    else parse { o with positional := o.positional ++ [a] } rest

/-- D1's batch: named modules, each of U3 T3's syntax + size, none twice, at least one. -/
def batchOk (ms : List String) : Option String :=
  if ms.isEmpty then some "no module named"
  else
    match ms.find? (!isModule ·) with
    | some m => some s!"{m} is not a module name"
    | none => if ms.eraseDups.length != ms.length then some "a module is named twice" else none

/-- D1's grammar lines: each module whose record grammar is nonempty, in batch order. -/
def grammarLines (r : Record) : List String :=
  r.modules.filterMap fun m =>
    if m.grammar.isEmpty then none else some s!"grammar {m.module} {" ".intercalate m.grammar}"

/-- D1's tail after the request line: grammar + outcome lines, or the infra line; + the exit. -/
def report : Verdict → List String × UInt32
  | .accepted r => (grammarLines r ++ ["accepted"], 0)
  | .refused r f =>
    (grammarLines r ++
        [s!"refused {f.module} {f.line}:{f.column} {" ".intercalate (f.rule :: f.detail)}"],
      1)
  | .infra c d => ([s!"infra {FvdepIO.Cache.infraText c}: {d}"], 2)

/-- D1 + D2's profile step once T1 ran: P5a's request over the frozen batch + the library rows, the
step (or `--results`: the record's bytes, no spawn) → the request's digest + the verdict. -/
def runProfile (o : Options) (role : Role) (rows : List LibModule)
    (frozen : List (String × ByteArray)) (bwrap : String) (sys run : System.FilePath)
    (fp : String) : IO (String × Verdict) := do
  let req := requestOf role rows o.limits (frozen.map fun x => (x.1, FvdepIO.Hash.sha256Hex x.2)) fp
  let reqBytes := FvdepCore.Json.print req.toJson
  let digest := FvdepIO.Hash.sha256Hex reqBytes
  let lim : FvdepCore.Sandbox.Limits :=
    { deadline := o.seconds
      frameBytes := o.frameBytes.getD ({} : FvdepCore.Sandbox.Limits).frameBytes
      fileBytes := o.fileBytes }
  match o.results with
  | some f =>
    match ← (IO.FS.readBinFile f).toBaseIO with
    | .ok b =>
      return (digest, verdictOf req digest b)
    | .error e =>
      return (digest, .infra .io s!"the record {f} could not be read: {e}")
  | none =>
    match ← FvdepIO.Profile.installParse run (o.child.map System.FilePath.mk) with
    | .error e =>
      return (digest, .infra .toolMissing e)
    | .ok () =>
      let r ← FvdepIO.Profile.runStep bwrap sys run reqBytes frozen lim
      return (digest, judge req digest o.seconds lim.frameBytes r)

/-- D1's `module` lines: each frozen module + its SHA-256, in batch order. -/
def moduleLines (frozen : List (String × ByteArray)) : List String :=
  frozen.map fun x => s!"module {x.1} {FvdepIO.Hash.sha256Hex x.2}"

def check (o : Options) (role : Role) (src : String) (mods : List String) : IO UInt32 := do
  let ms := mods.mergeSort fun a b => decide (a ≤ b)
  let frozen ←
    match ← FvdepIO.Snapshot.read (System.FilePath.mk src) ms [] with
    | .ok s =>
      pure s.impl
    | .error d =>
      say [s!"infra io: {d}"]
      return 2
  say (moduleLines frozen)
  let some root ← FvdepIO.Tools.cacheRoot |
    do
      say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
      return 2
  let bwrap ←
    match ← FvdepIO.Tools.preflightBwrap with
    | .ok b =>
      pure b
    | .error e =>
      say [s!"infra tool_missing: {e}"]
      return 2
  let run ← FvdepIO.Phase.runDir root
  try
    let (sys, fp) ←
      match ← FvdepIO.Tools.tools root run with
      | .ok x =>
        pure x
      | .error e =>
        say [s!"infra tool_missing: {e}"]
        return 2
    let rows ←
      match o.library with
      | none =>
        pure []
      | some d =>
        match ← FvdepIO.Profile.libraryRows d with
        | .ok rs =>
          pure rs
        | .error e =>
          say [s!"infra io: {e}"]
          return 2
    let (digest, verdict) ← runProfile o role rows frozen bwrap sys run fp
    let (ls, rc) := report verdict
    say (s!"request {digest}" :: ls)
    return rc
  finally
    try
      IO.FS.removeDirAll run
    catch ex =>
      IO.eprintln s!"fvdep-dev: the run directory {run} stayed: {ex}"

def run (args : List String) : IO UInt32 := do
  let usageError (why : String) : IO UInt32 := do
    IO.eprint s!"fvdep-dev: profile check: {why}\n{usage}"
    return 2
  match parse {} args with
  | .error e =>
    usageError e
  | .ok o =>
    let some role := o.role | usageError "--role consumer|library is required"
    if role == .library && o.library.isSome then
      return ← usageError "--library serves the consumer role alone"
    if o.results.isSome && o.child.isSome then
      return ← usageError "--results and --child exclude each other"
    match o.positional with
    | [] =>
      usageError "no source directory"
    | src :: mods =>
      if let some why := batchOk mods then
        return ← usageError why
      let lim : FvdepCore.Sandbox.Limits := { fileBytes := o.fileBytes }
      if let some why := lim.check then
        return ← usageError why
      check o role src mods

end FvdepDev.ProfileCheck
