import FvdepCore.Oracle.Command
import FvdepIO.Library
import FvdepIO.Phase
import FvdepIO.Project
import FvdepIO.Toml
import FvdepIO.Tools

/-! `fvdep oracle`'s observation effects (contract `docs/contracts/U5b-oracle.md` O2; residues
`library-store`, `git`, `cache-fs`, `bwrap`, `sandbox-spawn`, `step-helper`, `lean-toolchain`,
`oracle-driver`): each effect → its observation, returned raw; the plan decides. One run directory
per command on the cache's filesystem (`<cache>/runs/…`: the view = hard links into the cache)
holds the view, the export + evaluation inputs; it goes at the end. The discovery the coherence
check hashed is the one the view builds (kept between the two effects). -/

namespace FvdepIO.Oracle

open FvdepCore FvdepCore.Oracle FvdepCore.Phase FvdepCore.Build FvdepCore.Sandbox

/-- The command's state: its run directory + cache setting once T1 ran, the last discovery, the
dev seam's substitute replies. -/
structure State where
  run : Option System.FilePath := none
  env : Option FvdepIO.Cache.Env := none
  discovered : Option (String × List String × Array FvdepIO.Cache.Source) := none
  replies : Option ByteArray := none

def noCache : String := "no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"

/-- P1. -/
def project (explicit : Option String) : IO Response := do
  return .project (← FvdepIO.Project.observe explicit)

/-- P2: `dir/fvdep.toml`, at most 64 KiB + 1 bytes (more = `tooLarge`). -/
def manifest (dir : String) : IO Response := do
  match FvdepIO.Sys.Path.ofString? dir, FvdepIO.Sys.Name.ofString? "fvdep.toml" with
  | some p, some n =>
    match ← FvdepIO.Sys.readFile p n (FvdepCore.Manifest.maxBytes + 1) with
    | .ok (some b) =>
      return .manifest (.bytes b)
    | .ok none =>
      return .manifest .absent
    | .error e =>
      if e.cause matches .tooLarge then
        return .manifest .tooLarge
      return .manifest (.failed e.reason)
  | _, _ =>
    return .manifest (.failed "its path holds a NUL")

/-- U3 T1: Lake's parse + `ofLake`. -/
def parse (text : String) : IO Response := do
  return .parse (← FvdepIO.Toml.parseTree text)

/-- L: the snapshot of `pin` from `FVDEP_LIBRARY_URL` (anchored at the working directory) under
`FVDEP_CACHE`, + the served tree's `lean-toolchain` + `index.json` (each ≤ L4's 1 MiB per file). -/
def snapshot (pin : Option String) (lim : FvdepCore.Library.Limits) : IO Response := do
  let some root ← FvdepIO.Tools.cacheRoot | return .snapshot (.error s!"infra io: {noCache}")
  let source :=
    FvdepCore.Library.anchor (← IO.currentDir).toString
      (FvdepCore.Library.sourceOf (← IO.getEnv "FVDEP_LIBRARY_URL"))
  match ← FvdepIO.Library.snapshot (← FvdepIO.Library.Store.of root source lim) pin with
  | .error r =>
    return .snapshot (.error r)
  | .ok s =>
    tryCatch
        (do
          let toolchain ← IO.FS.readBinFile (s.tree / "lean-toolchain")
          let index ← IO.FS.readBinFile (s.tree / "index.json")
          return .snapshot
              (.ok
                { commit := s.commit
                  tree := s.tree.toString
                  notice := s.notice
                  toolchain
                  index }))
      fun e =>
      return .snapshot
          (.error
            (s!"infra io: the library snapshot {s.commit}: " ++
              FvdepCore.Doc.escapeControls (toString e)))

/-- K2: the library modules `roots` reach in `tree` (kept for the view's build). -/
def closure (st : IO.Ref State) (tree : String) (roots : List String) : IO Response := do
  tryCatch
      (do
        match ← FvdepIO.Cache.discover tree roots with
        | .ok srcs =>
          st.modify fun x => { x with discovered := some (tree, roots, srcs) }
          return .closure
              (.ok
                (srcs.toList.map fun s =>
                  { module := s.module
                    bytes := s.bytes
                    imports := s.header.imports.map (·.module) }))
        | .error f =>
          return .closure (.error f.detail))
      fun e => return .closure (.error (FvdepCore.Doc.escapeControls (toString e)))

/-- The command's run directory (created once, on the cache's filesystem). -/
def runDir (st : IO.Ref State) (root : System.FilePath) : IO System.FilePath := do
  match (← st.get).run with
  | some r =>
    return r
  | none =>
    let r ← FvdepIO.Phase.runDir root
    st.modify fun x => { x with run := some r }
    return r

/-- O1 + K: T1's tools (bwrap, fvdep's toolchain, the helper, the fingerprint), the closure of
`roots` built from the kept discovery (a fresh one when none matches), one view; its handle = its
path. -/
def view (st : IO.Ref State) (tree : String) (roots : List String) : IO Response := do
  let some root ← FvdepIO.Tools.cacheRoot | return .view (.error ⟨.io, noCache⟩)
  let bwrap ←
    match ← FvdepIO.Tools.preflightBwrap with
    | .ok b =>
      pure b
    | .error e =>
      return .view (.error ⟨.toolMissing, e⟩)
  let run ← runDir st root
  match ← FvdepIO.Tools.tools root run with
  | .error e =>
    return .view (.error ⟨.toolMissing, e⟩)
  | .ok (sys, fp) =>
    let env ← FvdepIO.Tools.env root run {} bwrap sys (run / "step") fp
    st.modify fun x => { x with env := some env }
    let built ←
      match (← st.get).discovered with
      | some (t, rs, srcs) =>
        if t == tree && rs == roots then
          FvdepIO.Cache.buildFrom env srcs roots
        else
          FvdepIO.Cache.build env tree roots
      | none =>
        FvdepIO.Cache.build env tree roots
    match built with
    | .error f =>
      return .view (.error ⟨f.code, f.detail⟩)
    | .ok es =>
      let dir := run / "view"
      match ← FvdepIO.Cache.view env dir (es.map fun x => (x.key, x.manifest)) with
      | .ok () =>
        return .view (.ok dir.toString)
      | .error f =>
        return .view (.error ⟨f.code, f.detail⟩)

/-- One step over the view (R's layout: `src` at `/fvdep/src`, the view at `/fvdep/lib`, an empty
`/fvdep/prior`; `consumer/1`'s environment) judged by P5 against the artifact family `fam` → the
framed file `file`'s bytes, or the cause (`what` names the step). -/
def step (env : FvdepIO.Cache.Env) (run src : System.FilePath) (view : String) (lim : Limits)
    (pre cmd : List String) (extra : List (String × String)) (fam : List String) (file : String)
    (what : String) : IO (Except Cause ByteArray) := do
  let prior := run / "prior"
  IO.FS.createDirAll prior
  let setup : FvdepIO.Phase.Setup :=
    { cache := env
      recipe := FvdepCore.Build.consumer FvdepIO.Toolchain.release env.recipe.fingerprint
      limits := lim
      library := "" }
  match ← FvdepIO.Phase.stepRun setup src view prior pre cmd extra lim none with
  | .error why =>
    return .error ⟨.sandboxSetup, why⟩
  | .ok obs =>
    let res := FvdepIO.Cache.result fam obs
    let over :=
      match obs.frame with
      | .ok o => o.files.any fun f => f.1 == file && lim.exportCap < f.2.size
      | _ => false
    match stepVerdict .exportStep { res with exhausted := res.exhausted || over } with
    | .pass =>
      match obs.frame with
      | .ok o =>
        match o.files.find? (·.1 == file) with
        | some f =>
          return .ok f.2
        | none =>
          return .error ⟨.io, s!"{what} framed no {file}"⟩
      | _ =>
        return .error ⟨.io, s!"{what}: the step helper failed"⟩
    | .failed _ =>
      let inner :=
        match obs.firstErr <|> obs.firstOut with
        | some { file := some f, line := some n, message } =>
          s!"{FvdepCore.Bundle.mapPath f}:{n}: {FvdepCore.Bundle.firstLine message}"
        | some d => FvdepCore.Bundle.firstLine d.message
        | none => s!"{cmd.headD ""} exited with code {FvdepIO.Phase.exitCode obs}"
      return .error ⟨.io, s!"{what} failed: {inner}"⟩
    | .infra code d =>
      let d :=
        match res.outcome, res.frame with
        | .timedOut, _ => s!"{what} passed its deadline of {lim.deadline} seconds"
        | _, .ok (.signaled 25) _ => s!"signal 25 (per-file limit {lim.fileCap} bytes)"
        | _, .ok (.signaled k) _ => s!"signal {k}"
        | _, _ => d
      return .error ⟨code, d⟩

/-- E3–E4 + U5 P4: `leanexport imports -- roots` over the view (U5's export cap). -/
def leanexport (st : IO.Ref State) (view : String) (imports roots : List String) : IO Response := do
  let s ← st.get
  let (some env, some run) :=
    (s.env, s.run) | return .leanexport (.error ⟨.io, "no view was built"⟩)
  let empty := run / "empty"
  IO.FS.createDirAll empty
  let lim : Limits := {}
  let (pre, cmd, extra, fam, _) :=
    FvdepIO.Phase.stepCommand
      (FvdepCore.Build.consumer FvdepIO.Toolchain.release env.recipe.fingerprint) .exportStep
      imports roots false
  return .leanexport (← step env run empty view lim pre cmd extra fam "export.ndjson" "the export")

/-- V1: stdin to its end in chunks, at most `cap` bytes (one more = `tooLarge`). -/
def stdin (cap : Nat) : IO Response := do
  tryCatch
      (do
        let h ← IO.getStdin
        let mut acc := ByteArray.empty
        repeat
          let chunk ← h.read 65536
          if chunk.isEmpty then
            break
          acc := acc ++ chunk
          if cap < acc.size then
            return .stdin .tooLarge
        return .stdin (.bytes acc))
      fun e => return .stdin (.failed (FvdepCore.Doc.escapeControls (toString e)))

/-- V3: `lean --run Driver.lean` over the view (`requests.txt` beside it, both read-only;
`out/replies.txt` alone framed; deadline `seconds`) — or the dev seam's substitute bytes. -/
def evaluate (st : IO.Ref State) (view driver : String) (requests : ByteArray) (seconds : Nat) :
    IO Response := do
  let s ← st.get
  if let some b := s.replies then
    return .evaluate (.ok b)
  let (some env, some run) := (s.env, s.run) | return .evaluate (.error ⟨.io, "no view was built"⟩)
  let src := run / "evaluate"
  IO.FS.createDirAll src
  IO.FS.writeFile (src / "Driver.lean") driver
  IO.FS.writeBinFile (src / "requests.txt") requests
  let lim : Limits := { deadline := seconds }
  return .evaluate
      (←
        step env run src view lim ["--mkdir", "out"] ["lean", "--run", "Driver.lean"] []
            ["replies.txt"] "replies.txt" "the evaluation")

/-- The end of the command: the cache's pins released, the run directory removed. -/
def cleanup (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if let some env := s.env then
    try
      FvdepIO.Cache.unpinAll env
    catch _ =>
      pure ()
  if let some run := s.run then
    try
      IO.FS.removeDirAll run
    catch _ =>
      pure ()

end FvdepIO.Oracle
