import FvdepIO.Sandbox
import FvdepIO.Sha256

/-! `fvdep-dev sandbox run` (contract `docs/contracts/U5-sandbox.md` D2; never shipped): one step in
R's layout; prints its outcome, streams, frame + framed files, each line through interface §1's
line rule. -/

namespace FvdepDev.Sandbox

open FvdepCore.Sandbox FvdepIO.Sandbox

def usage : String :=
  "usage: fvdep-dev sandbox run [--src <dir>] [--deadline <s>] [--work-bytes <n>] " ++
    "[--tmp-bytes <n>] [--diagnostic-bytes <n>] [--frame-bytes <n>] [--file-bytes <n>] " ++
    "-- <argv>\n"

structure Options where
  src : Option String := none
  limits : Limits := {}
  argv : List String := []

/-- A positive whole number in decimal digits. -/
def positive (s : String) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none
  else
    match s.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 with
    | 0 => none
    | n => some n

def number (flag v : String) : Except String Nat :=
  match positive v with
  | some n => .ok n
  | none => .error s!"{flag} takes a positive whole number, got {v}"

def parse (o : Options) : List String → Except String Options
  | "--src" :: d :: rest => parse { o with src := some d } rest
  | "--deadline" :: v :: rest =>
    match number "--deadline" v with
    | .ok n => parse { o with limits := { o.limits with deadline := n } } rest
    | .error e => .error e
  | "--work-bytes" :: v :: rest =>
    match number "--work-bytes" v with
    | .ok n => parse { o with limits := { o.limits with workBytes := n } } rest
    | .error e => .error e
  | "--tmp-bytes" :: v :: rest =>
    match number "--tmp-bytes" v with
    | .ok n => parse { o with limits := { o.limits with tmpBytes := n } } rest
    | .error e => .error e
  | "--diagnostic-bytes" :: v :: rest =>
    match number "--diagnostic-bytes" v with
    | .ok n => parse { o with limits := { o.limits with diagnosticBytes := n } } rest
    | .error e => .error e
  | "--frame-bytes" :: v :: rest =>
    match number "--frame-bytes" v with
    | .ok n => parse { o with limits := { o.limits with frameBytes := n } } rest
    | .error e => .error e
  | "--file-bytes" :: v :: rest =>
    match number "--file-bytes" v with
    | .ok n => parse { o with limits := { o.limits with fileBytes := some n } } rest
    | .error e => .error e
  | "--" :: a :: rest => .ok { o with argv := a :: rest }
  | _ => .error "missing or unknown arguments"

/-- `bubblewrap X.Y.Z` (the first line) → its version. -/
def bwrapVersion (out : String) : Option (Nat × Nat × Nat) :=
  let line := (out.splitOn "\n").headD ""
  if line.startsWith "bubblewrap " then
    match (String.ofList (line.toList.drop 11)).splitOn "." with
    | [a, b, c] => do
      pure (← a.toNat?, ← b.toNat?, ← c.toNat?)
    | _ => none
  else none

def atLeast (v w : Nat × Nat × Nat) : Bool :=
  w.1 < v.1 || w.1 == v.1 && (w.2.1 < v.2.1 || w.2.1 == v.2.1 && w.2.2 ≤ v.2.2)

/-- T1: the first `bwrap` on `PATH`, at least 0.8.0 (`--disable-userns`). -/
def preflightBwrap : IO (Except String String) := do
  let dirs := ((← IO.getEnv "PATH").getD "").splitOn ":"
  let mut found := none
  for d in dirs do
    if found.isNone && !d.isEmpty then
      let p := System.FilePath.mk d / "bwrap"
      if ← p.pathExists then
        found := some p
  let some p := found | return .error "bwrap is not on PATH"
  let out ←
    try
      IO.Process.output { cmd := p.toString, args := #["--version"] }
    catch e =>
      return .error s!"bwrap at {p} did not run: {e}"
  match bwrapVersion out.stdout with
  | some v =>
    if atLeast v (0, 8, 0) then
      return .ok p.toString
    else
      return .error s!"bwrap {v.1}.{v.2.1}.{v.2.2} at {p} is older than 0.8.0"
  | none =>
    return .error s!"bwrap at {p} reported no version"

/-- I1 + T1: fvdep's own toolchain (elan resolves the release fvdep was built with), holding
`bin/lean` + `bin/leanexport`. -/
def preflightSysroot (run : System.FilePath) : IO (Except String System.FilePath) := do
  IO.FS.writeFile (run / "lean-toolchain") (FvdepCore.Index.Command.toolchain ++ "\n")
  let out ←
    try
      IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := run }
    catch e =>
      return .error s!"lean did not run: {e}"
  if out.exitCode != 0 then
    return .error s!"lean --print-prefix exited with code {out.exitCode}"
  let sys : System.FilePath := (out.stdout.splitOn "\n").headD ""
  for tool in ["lean", "leanexport"] do
    unless ← (sys / "bin" / tool).pathExists do
      return .error s!"{tool} is missing from the toolchain at {sys}"
  return .ok sys

/-- A copy of `src` (directories + regular files; anything else named + skipped). -/
partial def copyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    let md ← e.path.symlinkMetadata
    match md.type with
    | .dir =>
      copyTree e.path (dst / e.fileName)
    | .file =>
      IO.FS.writeBinFile (dst / e.fileName) (← IO.FS.readBinFile e.path)
    | _ =>
      IO.eprintln s!"fvdep-dev: --src: skipped {e.path} (a link or special file)"

/-- R8: a copy of the step helper beside the running executable, at `<run>/step/fvdep-step` (the
directory bound at `/fvdep/step`). -/
def installHelper (run : System.FilePath) : IO (Except String Unit) := do
  let helper := ((← IO.appPath).parent.getD ".") / "fvdep-step"
  unless ← helper.pathExists do
    return .error s!"fvdep-step is missing beside fvdep-dev ({helper})"
  IO.FS.createDirAll (run / "step")
  IO.FS.writeBinFile (run / "step" / "fvdep-step") (← IO.FS.readBinFile helper)
  IO.setAccessRights (run / "step" / "fvdep-step")
      { user := { read := true, write := true, execution := true }
        group := { read := true, execution := true }
        other := { read := true, execution := true } }
  return .ok ()

def outcomeLine : Outcome → String
  | .exited n => s!"outcome exited {n}"
  | .timedOut => "outcome timed_out"
  | .setupFailed d => s!"outcome setup_failed: {d}"
  | .protocol => "outcome protocol"

/-- A kept stream line by line (its final line feed ends the last line). -/
def relay (pre : String) (b : ByteArray) : List String :=
  let segs := (FvdepCore.Index.Command.textOfBytes b).splitOn "\n"
  let segs := if segs.getLast? == some "" then segs.dropLast else segs
  segs.map (pre ++ ·)

def report (obs : Observation) : List String :=
  let frame :=
    match obs.frame with
    | .ok o =>
      "frame complete" ::
        o.files.map fun f => s!"file {f.1} {f.2.size} {FvdepIO.Hash.sha256Hex f.2}"
    | .overflow => ["frame overflow"]
    | .invalid => ["frame invalid"]
  [outcomeLine obs.outcome, s!"stdout {obs.stdout.total} dropped {obs.stdout.dropped}",
      s!"stderr {obs.stderr.total} dropped {obs.stderr.dropped}"] ++
    frame ++
    relay "out: " obs.stdout.kept ++
    relay "err: " obs.stderr.kept

def say (ms : List String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (FvdepCore.Index.Command.lines ms)
  out.flush

/-- D2 after its arguments parse: T1, the run directory, one step, the report (R7: the run
directory removed). -/
def step (o : Options) : IO UInt32 := do
  match ← preflightBwrap with
  | .error e =>
    say [s!"infra tool_missing: {e}"]
    return 2
  | .ok bwrap =>
    let run ← IO.FS.createTempDir
    try
      match ← preflightSysroot run with
      | .error e =>
        say [s!"infra tool_missing: {e}"]
        return 2
      | .ok sys =>
        if let .error e← installHelper run then
          say [s!"infra tool_missing: {e}"]
          return 2
        match o.src with
        | some d =>
          copyTree d (run / "src")
        | none =>
          IO.FS.createDirAll (run / "src")
        let spec : Spec :=
          { ro :=
              [(sys.toString, .sysroot), ((run / "step").toString, .step),
                ((run / "src").toString, .src)]
            env :=
              [("PATH", "/fvdep/sysroot/bin:/usr/bin"), ("HOME", "/fvdep/work"), ("TMPDIR", "/tmp"),
                ("LC_ALL", "C")]
            workBytes := o.limits.workBytes
            tmpBytes := o.limits.tmpBytes
            argv := ["--mkdir", "out", "--file-bytes", toString o.limits.fileCap, "--"] ++ o.argv }
        match ← FvdepIO.Sandbox.run bwrap spec o.limits with
        | .error e =>
          say [s!"infra sandbox_setup: {e}"]
          return 2
        | .ok obs =>
          say (report obs)
          return 0
    finally
      try
        IO.FS.removeDirAll run
      catch e =>
        IO.eprintln s!"fvdep-dev: the run directory {run} stayed: {e}"

def run (args : List String) : IO UInt32 := do
  match parse {} args with
  | .error e =>
    IO.eprint s!"fvdep-dev: {e}\n{usage}"
    return 2
  | .ok o =>
    match o.limits.check with
    | some e =>
      IO.eprint s!"fvdep-dev: {e}\n{usage}"
      return 2
    | none =>
      step o

end FvdepDev.Sandbox
