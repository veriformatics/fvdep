import FvdepCore.Profile.Barrier
import FvdepIO.Parse
import FvdepIO.Sandbox

/-! The profile step's supervisor side (contract `docs/contracts/U6-profile.md` P1, P5a, P5c, B;
ledger residues `lean-parser` (the library headers read in-process: trusted text, B1's allowed
read) + `sandbox-spawn` (the step)): the library rows of the request, the step's layout, the step,
its run as P5c reads it. The verdict = the pure `judge`. Callers: U7's admission + U8's `check`,
before any compile, fill or view (B1). -/

namespace FvdepIO.Profile

open FvdepCore.Profile

/-- P5a: the explicit imports of a trusted header (a library module's), in source order. -/
def headerImports (path : String) (bytes : ByteArray) : IO (Except String (List String)) := do
  let some text := String.fromUTF8? bytes | return .error s!"{path} is not UTF-8"
  let (item, _, _) ← FvdepIO.Parse.headItem {} ⟨0, 0⟩ (Lean.Parser.mkInputContext text path)
  match item with
  | .tree h _ =>
    return .ok (importsOf h)
  | .stop (.finding f) =>
    return .error s!"the header of {path} does not parse: {" ".intercalate f.detail}"
  | .stop .over =>
    return .error s!"the header of {path} passes the profile's caps"

/-- The `.lean` files under `dir / rel` (paths relative to `dir`, `/`-separated). -/
partial def leanFiles (dir : System.FilePath) (rel : String) : IO (List String) := do
  let mut out := []
  for e in ← (dir / rel).readDir do
    let r := rel ++ "/" ++ e.fileName
    if ← e.path.isDir then
      out := out ++ (← leanFiles dir r)
    else
      if r.endsWith ".lean" then
        out := out ++ [r]
  return out

/-- P5a's library rows of a library tree at `dir` (D1's `--library` working copy): `Fvdep.lean` +
`Fvdep/**/*.lean`, each module with its header's explicit imports in source order. -/
def libraryRows (dir : System.FilePath) : IO (Except String (List LibModule)) := do
  let mut files := []
  if ← (dir / "Fvdep.lean").pathExists then
    files := ["Fvdep.lean"]
  if ← (dir / "Fvdep").isDir then
    files := files ++ (← leanFiles dir "Fvdep")
  let mut rows := #[]
  for f in files do
    let m := (String.ofList (f.toList.take (f.length - 5))).map fun c => if c == '/' then '.' else c
    unless isModule m do
      return .error s!"the library file {f} names no module"
    match ← headerImports f (← IO.FS.readBinFile (dir / f)) with
    | .ok is =>
      rows := rows.push ⟨m, is⟩
    | .error e =>
      return .error e
  return .ok rows.toList

/-- `i` to its end into `o`, 1 MiB at a time (the child is ≈ 240 MB). -/
partial def copyChunks (i o : IO.FS.Handle) : IO Unit := do
  let chunk ← i.read 1048576
  unless chunk.isEmpty do
    o.write chunk
    copyChunks i o

/-- P1's layout: the parse child at `<run>/step/fvdep-parse` (bound at `/fvdep/step`, beside the
step helper), copied from beside the running executable, or `child` (D1's `--child`: the same
name, argv + layout). -/
def installParse (run : System.FilePath) (child : Option System.FilePath) :
    IO (Except String Unit) := do
  let src := child.getD (((← IO.appPath).parent.getD ".") / "fvdep-parse")
  unless ← src.pathExists do
    return .error s!"fvdep-parse is missing ({src})"
  IO.FS.createDirAll (run / "step")
  let dst := run / "step" / "fvdep-parse"
  IO.FS.withFile src .read fun i => IO.FS.withFile dst .write fun o => copyChunks i o
  IO.setAccessRights dst
      { user := { read := true, write := true, execution := true }
        group := { read := true, execution := true }
        other := { read := true, execution := true } }
  return .ok ()

/-- U5's observation of the parse step as P5c reads it. -/
def runOf (obs : FvdepIO.Sandbox.Observation) : Run :=
  match obs.outcome with
  | .setupFailed d => .setup d
  | .protocol => .setup "the step reported two exit codes"
  | .timedOut => .timedOut
  | .exited n =>
    match obs.frame with
    | .ok o => .framed n o
    | .overflow => .overflow
    | .invalid => .invalid

/-- P1 + P5a: the profile step — `<run>/profile-src` = the request + the frozen batch at their paths
(read-only at `/fvdep/src`), the sysroot + `<run>/step` (helper + child) read-only, U5's runner with
`lim` (its deadline = P6's `seconds`); the child writes `out/results.json`. -/
def runStep (bwrap : String) (sysroot run : System.FilePath) (reqBytes : ByteArray)
    (sources : List (String × ByteArray)) (lim : FvdepCore.Sandbox.Limits) : IO Run := do
  let src := run / "profile-src"
  IO.FS.createDirAll src
  IO.FS.writeBinFile (src / "request.json") reqBytes
  for (m, bytes) in sources do
    let f := src / modulePath m
    if let some p := f.parent then
      IO.FS.createDirAll p
    IO.FS.writeBinFile f bytes
  let spec : FvdepCore.Sandbox.Spec :=
    { ro := [(sysroot.toString, .sysroot), ((run / "step").toString, .step), (src.toString, .src)]
      env := [("LEAN_ABORT_ON_PANIC", "1")]
      workBytes := lim.workBytes
      tmpBytes := lim.tmpBytes
      argv :=
        ["--mkdir", "out", "--file-bytes", toString lim.fileCap, "--", "/fvdep/step/fvdep-parse"] }
  match ← FvdepIO.Sandbox.run bwrap spec lim with
  | .error why =>
    return .setup why
  | .ok obs =>
    return runOf obs

end FvdepIO.Profile
