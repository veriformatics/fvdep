import FvdepDev.Cache
import FvdepIO.Bundle
import FvdepIO.Snapshot
import FvdepIO.Toml

/-! `fvdep-dev phase check` (contract `docs/contracts/U5-sandbox.md` D1; never shipped): a
manifest entry's two phases over a library working copy — S's snapshot, K's views, P's steps, B2's
bundle on a failure — reported line by line (interface §1's line rule). -/

namespace FvdepDev.Phase

open FvdepCore.Build FvdepCore.Sandbox FvdepCore.Evidence FvdepDev.Sandbox FvdepIO.Tools

def usage : String :=
  "usage: fvdep-dev phase check <project dir> <id> --library <library dir> --spec-module <M> " ++
    "--spec <constant> [--abi-module <M> --abi <constant>] [--roots1 <c>…] [--roots2 <c>…] " ++
    "[--deadline <s>] [--work-bytes <n>] [--frame-bytes <n>] [--export-bytes <n>] " ++
    "[--artifacts <dir>]\n       fvdep-dev phase rerun <bundle dir>\n"

structure Options where
  project : String := ""
  id : String := ""
  library : String := ""
  specModule : String := ""
  spec : String := ""
  abiModule : Option String := none
  abi : Option String := none
  roots1 : Option (List String) := none
  roots2 : Option (List String) := none
  limits : Limits := {}
  artifacts : Option String := none

/-- The values after a list option, up to the next option. -/
def values (args : List String) : List String × List String :=
  (args.takeWhile fun a => !a.startsWith "--", args.dropWhile fun a => !a.startsWith "--")

partial def parse (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--library" :: v :: rest => parse { o with library := v } rest
  | "--spec-module" :: v :: rest => parse { o with specModule := v } rest
  | "--spec" :: v :: rest => parse { o with spec := v } rest
  | "--abi-module" :: v :: rest => parse { o with abiModule := some v } rest
  | "--abi" :: v :: rest => parse { o with abi := some v } rest
  | "--artifacts" :: v :: rest => parse { o with artifacts := some v } rest
  | "--roots1" :: rest =>
    match values rest with
    | ([], _) => .error "--roots1 takes at least one constant"
    | (cs, rest) => parse { o with roots1 := some cs } rest
  | "--roots2" :: rest =>
    match values rest with
    | ([], _) => .error "--roots2 takes at least one constant"
    | (cs, rest) => parse { o with roots2 := some cs } rest
  | "--deadline" :: v :: rest =>
    match number "--deadline" v with
    | .ok n => parse { o with limits := { o.limits with deadline := n } } rest
    | .error e => .error e
  | "--work-bytes" :: v :: rest =>
    match number "--work-bytes" v with
    | .ok n => parse { o with limits := { o.limits with workBytes := n } } rest
    | .error e => .error e
  | "--frame-bytes" :: v :: rest =>
    match number "--frame-bytes" v with
    | .ok n => parse { o with limits := { o.limits with frameBytes := n } } rest
    | .error e => .error e
  | "--export-bytes" :: v :: rest =>
    match number "--export-bytes" v with
    | .ok n => parse { o with limits := { o.limits with exportBytes := some n } } rest
    | .error e => .error e
  | _ => .error "missing or unknown arguments"

def obsLine : Obs → String
  | .phase1 (.ok e) => s!"phase1 built {e}"
  | .phase1 (.failed r) => s!"phase1 failed: {r}"
  | .phase2 e1 (.ok e2) => s!"phase2 built {e2} on {e1}"
  | .phase2 _ (.failed r) => s!"phase2 failed: {r}"
  | .infra c d => s!"infra {FvdepIO.Cache.infraText c}: {d}"
  | _ => "infra io: internal: an observation a phase never makes"

/-- D1's exit: infrastructure 2, a failed phase 1, both built 0. -/
def exitOf (obs : List Obs) : UInt32 :=
  if obs.any fun o => o matches .infra .. then 2
  else
    if obs.any fun o => o matches .phase1 (.failed _) || o matches .phase2 _ (.failed _) then 1
    else 0

/-- The retained files (`--artifacts`): each printed artifact + export copied under `dir` + the
canonical `manifest.json` in printed order. -/
def retain (dir run : System.FilePath) (files : List (String × FileRec)) : IO Unit := do
  IO.FS.createDirAll dir
  let mut entries := #[]
  for (phase, f) in files do
    let (src, rel) :=
      if phase == "exports" then (run / "exports" / f.path, f.path)
      else (run / phase / f.path, f.path)
    let dst := dir / phase / rel
    if let some p := dst.parent then
      IO.FS.createDirAll p
    IO.FS.writeBinFile dst (← IO.FS.readBinFile src)
    entries :=
      entries.push
        (FvdepCore.Json.Value.obj
          [("path", .str rel), ("phase", .str phase), ("sha256", .str f.sha256),
            ("size", .int f.size)])
  IO.FS.writeBinFile (dir / "manifest.json")
      (FvdepCore.Json.print (.obj [("files", .arr entries.toList), ("schema", .int 1)]))

def check (o : Options) : IO UInt32 := do
  let usageError (why : String) : IO UInt32 := do
    IO.eprint s!"fvdep-dev: {why}\n{usage}"
    return 2
  if
      o.project.isEmpty || o.id.isEmpty || o.library.isEmpty || o.specModule.isEmpty ||
        o.spec.isEmpty then
    return ← usageError "missing arguments"
  if o.abiModule.isSome != o.abi.isSome then
    return ← usageError "--abi-module and --abi go together"
  if let some why := o.limits.check then
    return ← usageError why
  let some r ← FvdepIO.Tools.cacheRoot |
    do
      say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
      return 2
  let t ←
    match ← FvdepDev.Cache.target with
    | .ok t =>
      pure t
    | .error why =>
      return ← usageError why
  let lib : System.FilePath := o.library
  if let some why← FvdepDev.Cache.toolchainOk lib then
    say [s!"infra toolchain: {why}"]
    return 2
  let proj : System.FilePath := o.project
  let text ←
    try
      IO.FS.readBinFile (proj / "fvdep.toml")
    catch ex =>
      say [s!"infra io: fvdep.toml could not be read: {ex}"]
      return 2
  let mf ←
    match ← FvdepIO.Toml.readManifest text with
    | .ok m =>
      pure m
    | .error e =>
      say [s!"infra io: fvdep.toml: {e.detail}"]
      return 2
  let some entry := mf.modules.find? fun e => toString e.decl.module == o.id |
    do
      say [s!"infra io: fvdep.toml has no entry {o.id}"]
      return 2
  let (some impl, some proof) := (entry.decl.impl, entry.decl.proof) |
    do
      say [s!"infra io: the entry {o.id} names no implementation + proof constant"]
      return 2
  let src ←
    match ← FvdepIO.Snapshot.read proj entry.implModules entry.proofModules with
    | .ok s =>
      pure s
    | .error d =>
      say [s!"infra io: {d}"]
      return 2
  let bwrap ←
    match ← preflightBwrap with
    | .ok b =>
      pure b
    | .error e =>
      say [s!"infra tool_missing: {e}"]
      return 2
  let run ← FvdepIO.Phase.runDir r
  try
    let (sys, fp) ←
      match ← FvdepIO.Tools.tools r run with
      | .ok x =>
        pure x
      | .error e =>
        say [s!"infra tool_missing: {e}"]
        return 2
    let e ← FvdepIO.Tools.env r run { cacheBytes := t } bwrap sys (run / "step") fp
    let abi :=
      match o.abiModule, o.abi with
      | some m, some c => some (m, c)
      | _, _ => none
    let setup : FvdepIO.Phase.Setup :=
      { cache := e
        recipe := consumer FvdepIO.Toolchain.release fp
        limits := o.limits
        library := lib }
    let req : FvdepIO.Phase.Request :=
      { impl := src.impl
        proof := src.proof
        specModule := o.specModule
        spec := o.spec
        abi
        roots1 := o.roots1.getD ([impl, o.spec] ++ (o.abi.map ([·])).getD [])
        roots2 := o.roots2.getD [proof] }
    let rep ← tryFinally (FvdepIO.Phase.check setup req) (FvdepIO.Cache.unpinAll e)
    let obs := rep.runs.map (·.obs)
    let mut bundleLines := #[]
    for x in rep.runs do
      if let some c := x.capture then
        match ← FvdepIO.Bundle.write r setup.recipe setup.limits c with
        | .ok (d, complete) =>
          bundleLines :=
            bundleLines.push s!"bundle {d} {if complete then "complete" else "incomplete"}"
        | .error why =>
          IO.eprintln s!"fvdep-dev: warning: {why}"
    let frozenOf (n : Nat) (x : FvdepIO.Phase.PhaseRun) : List (String × FileRec) :=
      match x.frozen with
      | some f => (f.artifacts.map fun a => (s!"phase{n}", a)) ++ [("exports", f.exported)]
      | none => []
    let files :=
      (rep.runs.head?.map (frozenOf 1)).getD [] ++ (rep.runs.tail.head?.map (frozenOf 2)).getD []
    let fileLines :=
      files.map fun (phase, f) =>
        if phase == "exports" then
          s!"export phase{if f.path == "e1.ndjson" then 1 else 2} exports/{f.path} " ++
            s!"{f.size} {f.sha256}"
        else s!"artifact {phase} {f.path} {f.size} {f.sha256}"
    say
        ([s!"impl_sources {rep.implSources}", s!"proof_sources {rep.proofSources}"] ++
          obs.map obsLine ++
          fileLines ++
          bundleLines.toList)
    if let some dir := o.artifacts then
      try
        retain dir run files
      catch ex =>
        say [s!"infra io: the artifacts could not be kept in {dir}: {ex}"]
        return 2
    return exitOf obs
  finally
    try
      IO.FS.removeDirAll run
    catch ex =>
      IO.eprintln s!"fvdep-dev: the run directory {run} stayed: {ex}"

/-- A bundle's `src` files as (module, bytes) pairs (`A/B.lean` → `A.B`). -/
partial def sources (dir : System.FilePath) (rel : String := "") : IO (List (String × ByteArray)) :=
  do
  unless ← dir.pathExists do
    return []
  let mut out := []
  for e in ← (if rel.isEmpty then dir else dir / rel).readDir do
    let r := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
    if (← e.path.symlinkMetadata).type == .dir then
      out := out ++ (← sources dir r)
    else
      if r.endsWith ".lean" then
        let stem := String.ofList (r.toList.take (r.length - 5))
        out := out ++ [(stem.map fun c => if c == '/' then '.' else c, ← IO.FS.readBinFile e.path)]
  return out

/-- D4: the recorded failing step of the bundle at `dir` re-executed from its copies (B2) → D1's
line for it (no promise of the same result: arbitrary proof IO, races, resources). -/
def rerun (dir : String) : IO UInt32 := do
  let d : System.FilePath := dir
  let bytes ←
    try
      IO.FS.readBinFile (d / "bundle.json")
    catch ex =>
      say [s!"infra io: {d / "bundle.json"} could not be read: {ex}"]
      return 2
  let some rc := FvdepCore.Bundle.Record.ofBytes bytes |
    do
      say [s!"infra io: {d / "bundle.json"} holds no bundle record (schema 1, canonical)"]
      return 2
  let omitted := rc.inputs.filter (!·.kept)
  unless omitted.isEmpty do
    say
        [s!"infra io: the bundle is incomplete; omitted inputs: " ++
            ", ".intercalate (omitted.map fun i => i.role ++ "/" ++ i.path)]
    return 2
  for i in rc.inputs do
    let f := d / "inputs" / i.role / i.path
    let same ←
      try
        pure (FvdepIO.Hash.sha256Hex (← IO.FS.readBinFile f) == i.sha256)
      catch _ =>
        pure false
    unless same do
      say [s!"infra io: the bundle's copy {i.role}/{i.path} differs from its record"]
      return 2
  let some r ← FvdepIO.Tools.cacheRoot |
    do
      say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
      return 2
  let bwrap ←
    match ← preflightBwrap with
    | .ok b =>
      pure b
    | .error e =>
      say [s!"infra tool_missing: {e}"]
      return 2
  let run ← IO.FS.createTempDir
  try
    let (sys, fp) ←
      match ← FvdepIO.Tools.tools r run with
      | .ok x =>
        pure x
      | .error e =>
        say [s!"infra tool_missing: {e}"]
        return 2
    if fp != rc.recipe.fingerprint then
      say
          [s!"infra toolchain: the bundle was recorded under toolchain fingerprint " ++
              s!"{rc.recipe.fingerprint}; this one is {fp}"]
      return 2
    let role (x : String) : IO System.FilePath := do
      let p := d / "inputs" / x
      if ← p.pathExists then
        return p
      IO.FS.createDirAll (run / ("empty-" ++ x))
      return run / ("empty-" ++ x)
    let (src, view, prior) := (← role "src", ← role "lib", ← role "prior")
    let e ← FvdepIO.Tools.env r run {} bwrap sys (run / "step") fp
    let setup : FvdepIO.Phase.Setup :=
      { cache := e
        recipe := rc.recipe
        limits := rc.limits
        library := view }
    let n := rc.phase
    let failed (reason : String) : IO UInt32 := do
      say [s!"phase{n} failed: {reason}"]
      return 1
    if rc.step == "graph" then
      let built := (rc.presence.filter (·.2 == "built")).map (·.1)
      match
        ←
          FvdepIO.Phase.graph n (← sources src) built fun m =>
              pure (rc.presence.lookup m == some "library") with
      | .error (reason, _) =>
        return ← failed reason
      | .ok _ =>
        say [s!"phase{n} step passed"]
        return 0
    let step : FvdepCore.Phase.Step :=
      match rc.step with
      | "compile" => .compile rc.module
      | "library-roots" => .libraryRoots
      | "roots" => .consumerRoots
      | _ => .exportStep
    let isModule ←
      match step with
      | .compile m =>
        match
          ←
            FvdepIO.Header.observe (FvdepCore.Phase.stem m ++ ".lean")
                (← IO.FS.readBinFile (src / (FvdepCore.Phase.stem m ++ ".lean"))) with
        | .ok h =>
          pure h.isModule
        | .error _ =>
          pure false
      | _ =>
        pure false
    match
      ←
        FvdepIO.Phase.judge setup n step src view prior rc.imports rc.roots isModule rc.limits
            none with
    | .error why =>
      say [s!"infra sandbox_setup: {why}"]
      return 2
    | .ok (res, _, _, _) =>
      match FvdepCore.Phase.stepVerdict step res with
      | .pass =>
        say [s!"phase{n} step passed"]
        return 0
      | .failed reason =>
        failed reason
      | .infra c why =>
        say [s!"infra {FvdepIO.Cache.infraText c}: phase {n}, {FvdepIO.Phase.stepName step}: {why}"]
        return 2
  finally
    try
      IO.FS.removeDirAll run
    catch ex =>
      IO.eprintln s!"fvdep-dev: the run directory {run} stayed: {ex}"

def run (args : List String) : IO UInt32 := do
  match args with
  | "check" :: project :: id :: rest =>
    match parse { project, id } rest with
    | .ok o =>
      check o
    | .error why =>
      IO.eprint s!"fvdep-dev: {why}\n{usage}"
      return 2
  | ["rerun", dir] =>
    rerun dir
  | _ =>
    IO.eprint usage
    return 2

end FvdepDev.Phase
