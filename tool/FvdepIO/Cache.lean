import FvdepCore.Build
import FvdepCore.Phase
import FvdepIO.Header
import FvdepIO.Sandbox
import FvdepIO.Sha256
import FvdepIO.Sys

/-! The library build cache's effects (contract `docs/contracts/U5-sandbox.md` K2–K5, K7; residue
`cache-fs`): per-key `flock` pins, validation over the observed entries (`validate`), fills through
one step each + durable publication, views of hard links, `used` stamps, eviction under
`evict.lock` (`evictPlan`). Layout under `FVDEP_CACHE/build/v1/`: `entries/<key>/` (the artifacts
in module layout + `manifest.json` + `used`), `locks/<key>` (never deleted), `tmp/<key>.<pid>.<n>`
(a fill's entry under construction, its view `….lib`, an entry being removed), `evict.lock`. -/

namespace FvdepIO.Cache

open FvdepCore.Build FvdepCore.Sandbox

/-- K4: `link(src, dst)`. -/
@[extern "fvdep_cache_link"]
opaque link (src dst : @& String) : IO (Except Nat Unit)

/-- K5: the `used` stamp set to now (`utimensat`). -/
@[extern "fvdep_cache_touch"]
opaque touch (path : @& String) : IO (Except Nat Unit)

/-- A cache command's setting: the cache root (`FVDEP_CACHE`), T1's tools (bwrap, the sysroot, a
directory holding `fvdep-step`), the library recipe (its fingerprint = T1's), the limits, K7's trace
file, the command's supervisor-only run directory, + its state: one lock handle per key (`flock`
belongs to an open file description: a second handle to one key would contend with the first) + the
temp-name counter. -/
structure Env where
  root : System.FilePath
  bwrap : String
  sysroot : System.FilePath
  helper : System.FilePath
  recipe : Recipe
  limits : CacheLimits
  step : Limits
  trace : Option System.FilePath
  run : System.FilePath
  handles : IO.Ref (Array (String × IO.FS.Handle))
  counter : IO.Ref Nat

def Env.dir (e : Env) : System.FilePath := e.root / "build" / "v1"

def Env.entries (e : Env) : System.FilePath := e.dir / "entries"

def Env.locks (e : Env) : System.FilePath := e.dir / "locks"

def Env.tmp (e : Env) : System.FilePath := e.dir / "tmp"

/-- An infrastructure failure: its interface code (`infraText`: `io`, `sandbox_setup`, …) +
detail. -/
structure Failure where
  code : FvdepCore.Evidence.Infra
  detail : String

def io (detail : String) : Failure := { code := .io, detail }

def infraText : FvdepCore.Evidence.Infra → String
  | .sandboxSetup => "sandbox_setup"
  | .toolMissing => "tool_missing"
  | .adapter => "adapter"
  | .fetchFailed => "fetch_failed"
  | .io => "io"

/-- A fresh temp name for `key`: `<key>.<pid>.<n>` (two holders of one name never coexist: a temp of
`key` is made + used under `key`'s exclusive lock). -/
def fresh (e : Env) (key : String) : IO String := do
  let n ← e.counter.modifyGet fun n => (n, n + 1)
  return s!"{key}.{← IO.Process.getPID}.{n}"

/-- `locks/<key>`, opened once per command (created when absent, never deleted). -/
def handle (e : Env) (key : String) : IO IO.FS.Handle := do
  match (← e.handles.get).find? (·.1 == key) with
  | some (_, h) =>
    return h
  | none =>
    IO.FS.createDirAll e.locks
    let h ← IO.FS.Handle.mk (e.locks / key) .append
    e.handles.modify (·.push (key, h))
    return h

/-- The final unpin: every lock of the command released. -/
def unpinAll (e : Env) : IO Unit := do
  for (_, h) in ← e.handles.get do
    h.unlock
  e.handles.set #[]

/-- `LOCK_EX` by `deadline` (monotonic ms; polled: `flock` has no timeout). -/
partial def exclusive (h : IO.FS.Handle) (deadline : Nat) : IO Bool := do
  if ← h.tryLock (exclusive := true) then
    return true
  if deadline ≤ (← IO.monoMsNow) then
    return false
  IO.sleep 50
  exclusive h deadline

/-- An entry directory's files, recursively (path relative to the entry, size, SHA-256 when `hash`,
else `""`); a link or special file → `none` (such an entry never validates). -/
partial def listing (dir : System.FilePath) (hash : Bool) (rel : String := "") :
    IO (Option (Array FileRec)) := do
  let mut acc := #[]
  for d in ← (if rel.isEmpty then dir else dir / rel).readDir do
    let r := if rel.isEmpty then d.fileName else rel ++ "/" ++ d.fileName
    let md ← d.path.symlinkMetadata
    match md.type with
    | .dir =>
      match ← listing dir hash r with
      | some xs =>
        acc := acc ++ xs
      | none =>
        return none
    | .file =>
      let sha ←
        if hash then
          FvdepCore.Hash.hex <$> FvdepIO.Hash.sha256File d.path
        else
          pure ""
      acc := acc.push { path := r, size := md.byteSize.toNat, sha256 := sha }
    | _ =>
      return none
  return some acc

/-- K6 over the observed entry `key`: its manifest (canonical intake) when `validate` accepts it;
an unreadable or vanished entry = invalid (a miss). -/
def valid (e : Env) (key : String) : IO (Option Manifest) :=
  tryCatch
    (do
      let dir := e.entries / key
      let some files ← listing dir true | return none
      let some m := manifestOf (← IO.FS.readBinFile (dir / "manifest.json"))
        | return none
      return if validate FvdepIO.Hash.sha256Hex key m files.toList then some m else none)
    fun _ => pure none

/-- K5: entry `key`'s `used` stamp set to now. -/
def stamp (e : Env) (key : String) : IO (Except Failure Unit) := do
  match ← touch (e.entries / key / "used").toString with
  | .ok () =>
    return .ok ()
  | .error n =>
    return .error (io s!"the use stamp of entry {key} failed: {FvdepIO.Spawn.errnoText n}")

/-- An entry out of `entries/` at once (renamed into `tmp/`: a crash leaves a temp, reclaimed under
its key's lock), then deleted. -/
def remove (e : Env) (key : String) : IO Unit := do
  IO.FS.createDirAll e.tmp
  let aside := e.tmp / (← fresh e key)
  IO.FS.rename (e.entries / key) aside
  IO.FS.removeDirAll aside

/-- K3: every temp of `key` removed (its exclusive lock held: no other process works in one). -/
def reclaim (e : Env) (key : String) : IO Unit := do
  unless ← e.tmp.pathExists do
    return
  for d in ← e.tmp.readDir do
    if d.fileName.startsWith (key ++ ".") then
      if (← d.path.symlinkMetadata).type == .dir then
        IO.FS.removeDirAll d.path
      else
        IO.FS.removeFile d.path

/-- `path` ← `bytes`, durably (create, write, fsync, close: F2's writer). -/
def writeDurable (path : System.FilePath) (bytes : ByteArray) : IO (Except String Unit) := do
  let some p := FvdepIO.Sys.Path.ofString? path.toString
    | return .error s!"{path}: a path with NUL"
  match ← FvdepIO.Sys.Writer.create p with
  | .error e =>
    return .error e.reason
  | .ok w =>
    let r ← w.write bytes
    let r ←
      match r with
      | .ok () =>
        w.sync
      | .error e =>
        pure (.error e)
    let c ← w.close
    match r, c with
    | .ok (), .ok () =>
      return .ok ()
    | .error e, _ =>
      return .error e.reason
    | _, .error e =>
      return .error e.reason

/-- `fsync` of each directory. -/
def syncDirs (dirs : List System.FilePath) : IO (Except String Unit) := do
  for d in dirs do
    let some p := FvdepIO.Sys.Path.ofString? d.toString
      | return .error s!"{d}: a path with NUL"
    match ← FvdepIO.Sys.syncDir p with
    | .error e =>
      return .error e.reason
    | .ok () =>
      pure ()
  return .ok ()

/-- K4: a fresh view at `dir` = hard links to the artifacts of `deps` (key, manifest) in module
layout (an unsupported link → a failure, never a partial view). -/
def view (e : Env) (dir : System.FilePath) (deps : List (String × Manifest)) :
    IO (Except Failure Unit) := do
  IO.FS.createDirAll dir
  for (key, m) in deps do
    for a in m.artifacts do
      let dst := dir / a.path
      if let some p := dst.parent then
        IO.FS.createDirAll p
      match ← link (e.entries / key / a.path).toString dst.toString with
      | .ok () =>
        pure ()
      | .error n =>
        return .error
            (io s!"the view could not link {a.path} of entry {key}: {FvdepIO.Spawn.errnoText n}")
  return .ok ()

/-- A failing compile's first error (B1's capture while pumping: stdout's first `lean --json`
message of severity `error`, else stderr's first text-form error; its first line), else stderr's
first nonempty line (presentation; the phase reasons = B1's `FvdepCore.Bundle.reason`). -/
def diagnostic (obs : FvdepIO.Sandbox.Observation) : String :=
  match obs.firstOut <|> obs.firstErr with
  | some d => FvdepCore.Bundle.firstLine d.message
  | none =>
    ((FvdepCore.Index.Command.textOfBytes obs.stderr.kept).splitOn "\n").find? (!·.isEmpty) |>.getD
      "lean exited without a diagnostic"

/-- P5's view of a fill step: the frame complete iff it holds exactly the family `fam` (P2). -/
def result (fam : List String) (obs : FvdepIO.Sandbox.Observation) : FvdepCore.Phase.StepResult :=
  match obs.frame with
  | .ok o =>
    let paths := o.files.map (·.1)
    { outcome := obs.outcome
      frame :=
        .ok o.status.child
          (paths.length == fam.length && fam.all paths.contains && paths.all fam.contains)
      exhausted := o.status.workFull || o.status.tmpFull
      diagnostic := diagnostic obs }
  | .overflow =>
    { outcome := obs.outcome, frame := .overflow, exhausted := false, diagnostic := diagnostic obs }
  | .invalid =>
    { outcome := obs.outcome, frame := .invalid, exhausted := false, diagnostic := diagnostic obs }

/-- The directories from `root` down to `path`'s parent (`path` relative, `/`-separated), deepest
first: the ones a file at `path` adds an entry to. -/
def parents (root : System.FilePath) (path : String) : List System.FilePath :=
  let parts := (path.splitOn "/").dropLast
  (List.range (parts.length + 1)).reverse.map fun n =>
    (parts.take n).foldl (fun (d : System.FilePath) (c : String) => d / c) root

/-- The step's `--mkdir` for a module's outputs (`out/A` for `A.B`; `out` for a one-part name). -/
def outDir (module : String) : String :=
  match ((FvdepCore.Phase.stem module).splitOn "/").dropLast with
  | [] => "out"
  | ps => "out/" ++ "/".intercalate ps

/-- K3's fill of entry `key` (its exclusive lock held): one step compiles the source (the bytes read
once, at `/fvdep/src`) against the view of `deps` → the artifact family (P2) + `manifest.json` +
an empty `used` into a temp entry, each file + directory fsynced → an invalid entry at the key
removed → renamed to `entries/<key>` → `entries/` fsynced → K7's trace line. -/
def fill (e : Env) (key : String) (input : KeyInput) (src : ByteArray) (isModule : Bool)
    (deps : List (String × Manifest)) : IO (Except Failure Unit) := do
  let name ← fresh e key
  let tmp := e.tmp / name
  let lib := e.tmp / (name ++ ".lib")
  let srcDir := e.run / ("src-" ++ name)
  try
    IO.FS.createDirAll tmp
    if let .error f← view e lib deps then
      return .error f
    let file := srcDir / (FvdepCore.Phase.stem input.module ++ ".lean")
    if let some p := file.parent then
      IO.FS.createDirAll p
    IO.FS.writeBinFile file src
    let spec : Spec :=
      { ro :=
          [(e.sysroot.toString, .sysroot), (e.helper.toString, .step), (srcDir.toString, .src),
            (lib.toString, .lib)]
        env := stepEnv e.recipe
        workBytes := e.step.workBytes
        tmpBytes := e.step.tmpBytes
        argv :=
          ["--mkdir", outDir input.module, "--file-bytes", toString e.step.fileCap, "--"] ++
            FvdepCore.Phase.compileArgv e.recipe input.module }
    let obs ←
      match ← FvdepIO.Sandbox.run e.bwrap spec e.step with
      | .ok obs =>
        pure obs
      | .error why =>
        return .error { code := .sandboxSetup, detail := why }
    let fam := FvdepCore.Phase.family isModule input.module
    match FvdepCore.Phase.stepVerdict (.compile input.module) (result fam obs) with
    | .infra code detail =>
      return .error { code, detail := s!"library module {input.module}: {detail}" }
    | .failed reason =>
      return .error (io s!"library module {input.module} did not build: {reason}")
    | .pass =>
      pure ()
    let .ok o := obs.frame
      | return .error (io s!"library module {input.module}: a passing step without its frame")
    let mut arts := #[]
    let mut dirs := #[]
    for (path, bytes) in o.files ++ [("manifest.json", .empty), ("used", .empty)] do
      for d in parents tmp path do
        unless dirs.contains d do
          IO.FS.createDirAll d
          dirs := dirs.push d
      let bytes :=
        if path == "manifest.json" then
          manifestText { schema := 1, input, artifacts := arts.toList }
        else bytes
      if let .error why← writeDurable (tmp / path) bytes then
        return .error (io why)
      unless path == "manifest.json" || path == "used" do
        arts := arts.push { path, size := bytes.size, sha256 := FvdepIO.Hash.sha256Hex bytes }
    if let .error why← syncDirs dirs.toList then
      return .error (io why)
    if ← (e.entries / key).pathExists then
      remove e key
    IO.FS.createDirAll e.entries
    IO.FS.rename tmp (e.entries / key)
    if let .error why← syncDirs [e.entries] then
      return .error (io why)
    if let some t := e.trace then
      let h ← IO.FS.Handle.mk t .append
      h.putStr (traceLine key input.module)
      h.flush
    return .ok ()
  catch ex =>
    return .error (io s!"library module {input.module}: {ex}")
  finally
    for d in [tmp, lib, srcDir] do
      if ← d.pathExists then
        IO.FS.removeDirAll d

/-- K5 now: under `evict.lock`, every entry directory observed (charge = its files but `used`;
`used`'s modification time, 0 when absent; pinned = its `LOCK_EX` not free) → `evictPlan` → each
entry it names removed under that lock (taken without waiting: a new pin skips it) → (entries
removed, the charged total left). -/
def evict (e : Env) (target : Nat) : IO (Except Failure (Nat × Nat)) := do
  IO.FS.createDirAll e.dir
  let lk ← IO.FS.Handle.mk (e.dir / "evict.lock") .append
  lk.lock (exclusive := true)
  try
    let mut seen : Array Entry := #[]
    if ← e.entries.pathExists then
      IO.FS.createDirAll e.locks
      for d in ← e.entries.readDir do
        let bytes :=
          match ← tryCatch (listing d.path false) fun _ => pure none with
          | some fs => (fs.filter (·.path != "used")).foldl (· + ·.size) 0
          | none => 0
        let used ←
          tryCatch
              (do
                let t := (← (d.path / "used").symlinkMetadata).modified
                pure (t.sec.toNat * 1000000000 + t.nsec.toNat))
              fun _ => pure 0
        let probe ← IO.FS.Handle.mk (e.locks / d.fileName) .append
        let free ← probe.tryLock (exclusive := true)
        if free then
          probe.unlock
        seen := seen.push { key := d.fileName, bytes, used, pinned := !free }
    let mut removed := 0
    let mut left := seen.foldl (· + ·.bytes) 0
    for k in evictPlan seen.toList target do
      let probe ← IO.FS.Handle.mk (e.locks / k) .append
      if ← probe.tryLock (exclusive := true) then
        tryFinally (remove e k) probe.unlock
        removed := removed + 1
        left := left - ((seen.find? (·.key == k)).map (·.bytes)).getD 0
    return .ok (removed, left)
  catch ex =>
    return .error (io s!"eviction: {ex}")
  finally
    lk.unlock

/-- How a closure module's entry was had: valid already (`reused`) or filled by this command. -/
inductive Use where
  | reused
  | built
  deriving DecidableEq, Repr

/-- K3: entry `key` valid + pinned (`LOCK_SH`, held until `unpinAll`), `fillIt` run under `LOCK_EX`
(within `lockWait`, the key's temps reclaimed, rechecked first) when it is absent or invalid; after
a fill the new entry is revalidated under `LOCK_SH` + K5's eviction runs. -/
def resolve (e : Env) (key : String) (fillIt : IO (Except Failure Unit)) :
    IO (Except Failure (Use × Manifest)) := do
  let h ← handle e key
  h.lock (exclusive := false)
  if let some m← valid e key then
    return (← stamp e key).map fun () => (.reused, m)
  h.unlock
  unless ← exclusive h ((← IO.monoMsNow) + e.limits.lockWait * 1000) do
    return .error (io s!"the lock of entry {key} stayed held past {e.limits.lockWait} s")
  let use ←
    tryFinally
        (do
          reclaim e key
          if (← valid e key).isSome then
            pure (Except.ok Use.reused)
          else
            match ← fillIt with
            | .ok () =>
              pure (.ok .built)
            | .error f =>
              pure (.error f))
        h.unlock
  let use ←
    match use with
    | .ok u =>
      pure u
    | .error f =>
      return .error f
  h.lock (exclusive := false)
  let some m ← valid e key | return .error (io s!"entry {key} does not validate after its fill")
  if let .error f← stamp e key then
    return .error f
  if use == .built then
    if let .error f← evict e e.limits.cacheBytes then
      return .error f
  return .ok (use, m)

/-- One library module of a build: its source bytes (read once) + observed header. -/
structure Source where
  module : String
  bytes : ByteArray
  header : FvdepIO.Header.Observed

/-- K2's discovery: the library modules `roots` reach through imports (toolchain modules = leaves),
each source read once + its header observed, each module visited once (an import cycle ends here;
`plan` names it); an import whose source is absent stays unread (`plan` names it). -/
def discover (lib : System.FilePath) (roots : List String) : IO (Except Failure (Array Source)) :=
  do
  let mut todo := roots
  let mut seen : Array Source := #[]
  let mut visited : Array String := #[]
  repeat
    match todo with
    | [] =>
      break
    | m :: rest =>
      todo := rest
      if visited.contains m || toolchainModule m then
        continue
      visited := visited.push m
      let rel := FvdepCore.Phase.stem m ++ ".lean"
      unless ← (lib / rel).pathExists do
        continue
      let bytes ← IO.FS.readBinFile (lib / rel)
      match ← FvdepIO.Header.observe rel bytes with
      | .error why =>
        return .error (io s!"library module {m}: {why}")
      | .ok h =>
        seen := seen.push { module := m, bytes, header := h }
        todo := todo ++ (h.imports.map (·.module)).filter (!toolchainModule ·)
  return .ok seen

/-- K2's refusal as text (in the library: infrastructure, never a consumer verdict). -/
def refusalText : Refusal → String
  | .duplicate n => s!"library module {n} is listed twice"
  | .missing (some a) t => s!"library module {a} imports {t}, which has no source in the library"
  | .missing none t => s!"{t} has no source in the library"
  | .stuck ms => s!"library modules import each other: {", ".intercalate ms}"

/-- One closure module's entry as `build` resolved it. -/
structure Resolved where
  module : String
  key : String
  use : Use
  manifest : Manifest

/-- K: the closure of `roots` in the library at `lib`, each module's entry valid + pinned (in plan
order: module, key, how it was had, its manifest). -/
def build (e : Env) (lib : System.FilePath) (roots : List String) :
    IO (Except Failure (List Resolved)) := do
  let sources ←
    match ← discover lib roots with
    | .ok s =>
      pure s
    | .error f =>
      return .error f
  let nodes : List Node :=
    sources.toList.map fun s =>
      { name := s.module, imports := (s.header.imports.map (·.module)).filter (!toolchainModule ·) }
  let order ←
    match plan nodes roots with
    | .ok o =>
      pure o
    | .error r =>
      return .error (io (refusalText r))
  let mut done : Array (String × String × Use × Manifest) := #[]
  for m in order do
    let some s := sources.find? (·.module == m)
      | return .error (io s!"internal: {m} has no source")
    let imports :=
      s.header.imports.map fun i =>
        { module := i.module
          isPublic := i.isPublic
          isMeta := i.isMeta
          all := i.all
          key :=
            if toolchainModule i.module then e.recipe.fingerprint
            else ((done.find? (·.1 == i.module)).map (·.2.1)).getD "" :
          Import }
    let input : KeyInput :=
      { recipe := e.recipe
        module := m
        path := FvdepCore.Phase.stem m ++ ".lean"
        source := FvdepIO.Hash.sha256Hex s.bytes
        imports }
    let key := keyOf FvdepIO.Hash.sha256Hex input
    let deps :=
      (closure nodes (importsOf nodes m)).filterMap fun d =>
        (done.find? (·.1 == d)).map fun x => (x.2.1, x.2.2.2)
    match ← resolve e key (fill e key input s.bytes s.header.isModule deps) with
    | .ok (use, man) =>
      done := done.push (m, key, use, man)
    | .error f =>
      return .error f
  return .ok
      (done.toList.map fun x =>
        { module := x.1, key := x.2.1, use := x.2.2.1, manifest := x.2.2.2 })

/-- `cache list`: every valid entry (key, charge = its artifacts + manifest, module), by key. -/
def list (e : Env) : IO (List (String × Nat × String)) := do
  unless ← e.entries.pathExists do
    return []
  let mut out := #[]
  for d in ← e.entries.readDir do
    if let some m← valid e d.fileName then
      let manifest := (manifestText m).size
      out := out.push (d.fileName, m.artifacts.foldl (· + ·.size) manifest, m.input.module)
  return (out.qsort fun a b => a.1 < b.1).toList

end FvdepIO.Cache
