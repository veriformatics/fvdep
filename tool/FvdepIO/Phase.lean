import FvdepCore.Bundle
import FvdepCore.Phase
import FvdepIO.Cache

/-! A check's two phases (contract `docs/contracts/U5-sandbox.md` P1–P8 + B1; residues `bwrap`,
`sandbox-spawn`, `step-helper`, `lean-toolchain`, `cache-fs`): the project's frozen sources (S)
graphed (K2: headers, import classes, plan), the library closure filled + viewed (K), then the
steps — phase 1's library roots check, then the deadline window `steps` (each compile, the roots
check, the export) — run by P8's `drive`, each judged by P5's `stepVerdict`, each phase observed by
`observe1`/`observe2`. The supervisor reads built files as bytes alone (I2). -/

namespace FvdepIO.Phase

open FvdepCore.Build FvdepCore.Sandbox FvdepCore.Phase FvdepCore.Evidence

/-- A check's request: S's frozen sources (module, bytes), P4's spec + ABI roots, each phase's
export roots. -/
structure Request where
  impl : List (String × ByteArray)
  proof : List (String × ByteArray)
  specModule : String
  spec : String
  abi : Option (String × String)
  roots1 : List String
  roots2 : List String

/-- A check's setting: the cache (library fills + views; its `run` = the command's supervisor-only
run directory), the consumer recipe (T2), the step limits (`deadline` = each phase's window, P1),
the library directory. -/
structure Setup where
  cache : FvdepIO.Cache.Env
  recipe : Recipe
  limits : Limits
  library : System.FilePath

/-- What a phase froze (P3, P6): its artifacts (paths under `phase<n>/`) + its export. -/
structure Frozen where
  artifacts : List FileRec
  exported : FileRec

/-- A failing step as its bundle records it (B2): its kind + module, the roots check's or the
export's request, a graph refusal's presence facts, the directories it read by role, its streams. -/
structure Capture where
  phase : Nat
  step : String
  module : String := ""
  imports : List String := []
  roots : List String := []
  presence : List (String × String) := []
  inputs : List (String × System.FilePath) := []
  stdout : ByteArray := .empty
  stderr : ByteArray := .empty

/-- One phase as the supervisor saw it: its observation (P5), what it froze, a failure's capture,
the library modules its closure started from. -/
structure PhaseRun where
  obs : Obs
  frozen : Option Frozen := none
  capture : Option Capture := none
  libRoots : List String := []

/-- A check's report (D1's lines; U8's evidence). -/
structure Report where
  implSources : String
  proofSources : String
  runs : List PhaseRun

def label (n : Nat) : String := if n == 1 then "implementation" else "proof"

def infraOf : String → Infra
  | "sandbox_setup" => .sandboxSetup
  | "tool_missing" => .toolMissing
  | _ => .io

def stepName : Step → String
  | .compile m => s!"compile {m}"
  | .consumerRoots => "roots"
  | .libraryRoots => "library roots"
  | .exportStep => "export"

/-- B2's name of a step's kind (`bundle.json` + D4). -/
def stepKind : Step → String
  | .compile _ => "compile"
  | .consumerRoots => "roots"
  | .libraryRoots => "library-roots"
  | .exportStep => "export"

def className : ImportClass → String
  | .listed => "listed"
  | .built => "built"
  | .toolchain => "toolchain"
  | .library => "library"
  | .absent => "absent"

/-- K2's plan refusal inside a consumer phase (its own refusal: the phase's `failed`). -/
def graphText : FvdepCore.Build.Refusal → String
  | .duplicate m => s!"{m} is listed twice"
  | .missing (some a) t => s!"{stem a}.lean imports {t}, which has no source"
  | .missing none t => s!"{t} has no source"
  | .stuck ms => s!"{", ".intercalate ms} import each other"

/-- `files` (relative path, bytes) written under `dir` → their records, in order. -/
def freeze (dir : System.FilePath) (files : List (String × ByteArray)) : IO (List FileRec) := do
  let mut out := #[]
  for (path, bytes) in files do
    let f := dir / path
    if let some p := f.parent then
      IO.FS.createDirAll p
    IO.FS.writeBinFile f bytes
    out := out.push { path, size := bytes.size, sha256 := FvdepIO.Hash.sha256Hex bytes }
  return out.toList

/-- One step in R's layout: `src` at `/fvdep/src`, `view` at `/fvdep/lib`, the check's consumer
modules built so far at `/fvdep/prior` (`run/consumer`: phase 1's frozen artifacts + this phase's
earlier ones, T2); `pre` = the helper's options before its `--file-bytes`, `cmd` = the command,
`env` = extra variables. -/
def stepRun (s : Setup) (src view prior : System.FilePath) (pre cmd : List String)
    (env : List (String × String)) (lim : Limits) (untilMs : Option Nat) :
    IO (Except String FvdepIO.Sandbox.Observation) := do
  let spec : Spec :=
    { ro :=
        [(s.cache.sysroot.toString, .sysroot), (s.cache.helper.toString, .step),
          (src.toString, .src), (view.toString, .lib), (prior.toString, .prior)]
      env := s.recipe.env ++ [("LEAN_PATH", ":".intercalate s.recipe.leanPath)] ++ env
      workBytes := lim.workBytes
      tmpBytes := lim.tmpBytes
      argv := pre ++ ["--file-bytes", toString lim.fileCap, "--"] ++ cmd }
  FvdepIO.Sandbox.run s.cache.bwrap spec lim untilMs

/-- The child's exit code as the frame records it (bwrap's when no frame). -/
def exitCode (obs : FvdepIO.Sandbox.Observation) : Nat :=
  match obs.frame with
  | .ok o => o.status.child.helperExit
  | _ =>
    match obs.outcome with
    | .exited c => c
    | _ => 0

/-- The directories a step read, by B2's roles. -/
def inputsOf (run src view : System.FilePath) : List (String × System.FilePath) :=
  [("src", src), ("lib", view), ("prior", run / "consumer")]

/-- An infrastructure detail naming the phase, the step + the limit its observation hit (text
alone: P5 classified already). -/
def detailOf (n : Nat) (step : Step) (lim : Limits) (exportOver : Bool)
    (obs : FvdepIO.Sandbox.Observation) (d : String) : String :=
  let cap :=
    match obs.frame with
    | .overflow => s!" (the frame passed --frame-bytes {lim.frameBytes})"
    | _ => if exportOver then s!" (the export passed --export-bytes {lim.exportCap})" else ""
  s!"phase {n}, {stepName step}: {d}{cap}"

/-- A step's command (P1, P4; T2's recipe): the helper's options before `--file-bytes`, the argv,
extra environment, the artifact family its frame must hold, the tool B1 names. `imports` + `roots`
= the roots check's or the export's request; `isModule` = a compiled module's header flag (P2). -/
def stepCommand (recipe : Recipe) (step : Step) (imports roots : List String) (isModule : Bool) :
    List String × List String × List (String × String) × List String × String :=
  match step with
  | .compile m =>
    (["--mkdir", FvdepIO.Cache.outDir m], compileArgv recipe m, [], family isModule m, "lean")
  | .libraryRoots | .consumerRoots =>
    (["--mkdir", "out"], recipe.argv ++ compileFlags recipe ++ ["./FvdepRoots.lean"], [], [],
      "lean")
  | .exportStep =>
    (["--mkdir", "out", "--stdout", "out/export.ndjson"],
      ["leanexport"] ++ imports ++ ["--"] ++ roots, [("LEAN_ABORT_ON_PANIC", "1")],
      ["export.ndjson"], "leanexport")

/-- One step run + judged (P5) over its materialized inputs: its `StepResult` (B1's reason or the
absent root as `diagnostic`, the export cap as a size cap), the observation, whether the export
passed its cap, the root a roots check names — or bwrap's setup failure. -/
def judge (s : Setup) (n : Nat) (step : Step) (src view prior : System.FilePath)
    (imports roots : List String) (isModule : Bool) (lim : Limits) (untilMs : Option Nat) :
    IO (Except String (StepResult × FvdepIO.Sandbox.Observation × Bool × String)) := do
  let (pre, cmd, env, fam, tool) := stepCommand s.recipe step imports roots isModule
  match ← stepRun s src view prior pre cmd env lim untilMs with
  | .error why =>
    return .error why
  | .ok obs =>
    let over :=
      match obs.frame with
      | .ok o => step == .exportStep && o.files.any fun f => lim.exportCap < f.2.size
      | _ => false
    let first := obs.firstOut <|> obs.firstErr
    let missing :=
      match step with
      | .libraryRoots | .consumerRoots =>
        match (first.bind (·.line)).bind (rootAt imports roots) with
        | some root => root
        | none => s!"one of {", ".intercalate roots}"
      | _ => ""
    let reason :=
      match step with
      | .libraryRoots | .consumerRoots =>
        FvdepCore.Doc.escapeControls s!"{label n} build failed ({missing} is not defined)"
      | _ => FvdepCore.Bundle.reason (label n) first tool (exitCode obs)
    let res := FvdepIO.Cache.result fam obs
    return .ok
        ({ res with
            exhausted := res.exhausted || over, diagnostic := reason },
          obs, over, missing)

/-- K2 + P5's graph of a phase: each module's import order, the library modules it reads, each
module's `module` flag. -/
structure Graph where
  order : List String
  library : List String
  isModule : List (String × Bool)

/-- K2 + P5 over phase `n`'s frozen sources: each header observed (a parse error = the phase's
refusal), each import classed (`importClass`; the library's presence read per import), K2's plan
→ the graph, or the failed reason + the presence facts read so far (B2: a rerun repeats the decision
from them). -/
def graph (n : Nat) (mods : List (String × ByteArray)) (built : List String)
    (present : String → IO Bool) : IO (Except (String × List (String × String)) Graph) := do
  let listed := mods.map (·.1)
  let mut heads : Array (String × FvdepIO.Header.Observed) := #[]
  for (m, bytes) in mods do
    match ← FvdepIO.Header.observe (stem m ++ ".lean") bytes with
    | .error why =>
      return .error (s!"{label n} build failed ({why})", [])
    | .ok h =>
      heads := heads.push (m, h)
  let mut presence : Array (String × String) := #[]
  let mut library : Array String := #[]
  let mut nodes : Array Node := #[]
  for (m, h) in heads do
    let mut edges : Array String := #[]
    for i in h.imports do
      let here ← present i.module
      let c := importClass listed built (fun _ => here) i.module
      presence := presence.push (i.module, className c)
      match c with
      | .listed =>
        edges := edges.push i.module
      | .library =>
        unless library.contains i.module do
          library := library.push i.module
      | .absent =>
        return .error
            (FvdepCore.Doc.escapeControls
                (s!"{label n} build failed ({stem m}.lean imports {i.module}, " ++
                  "which is not a listed module or a library module)"),
              presence.toList)
      | _ =>
        pure ()
    nodes := nodes.push { name := m, imports := edges.toList }
  match plan nodes.toList listed with
  | .ok order =>
    return .ok
        { order, library := library.toList,
          isModule := heads.toList.map fun x => (x.1, x.2.isModule) }
  | .error r =>
    return .error
        (FvdepCore.Doc.escapeControls s!"{label n} build failed ({graphText r})", presence.toList)

/-- The state a phase's steps share: the window's deadline (set by its first step), the frozen
artifacts + export, the last step's observation (B2's capture, the detail's limit). -/
structure Shared where
  window : Option Nat := none
  artifacts : Array FileRec := #[]
  exported : Option FileRec := none
  last : Option (Step × FvdepIO.Sandbox.Observation × Bool × System.FilePath × String) := none
  current : Option Step := none

/-- Phase `n` (P3, P6): the graph (a refusal = the phase's `failed`), the library closure from the
spec + ABI modules + the library modules imported (phase 2: ∪ phase 1's) + its view (a failure =
infrastructure), then P8's `drive` over phase 1's library roots check + the window (`steps`). -/
def phaseBody (s : Setup) (r : Request) (n : Nat) (mods : List (String × ByteArray))
    (built libPrev : List String) : IO PhaseRun := do
  let run := s.cache.run
  let lim := s.limits
  let sources := run / s!"sources{n}"
  for (m, bytes) in mods do
    let f := sources / (stem m ++ ".lean")
    if let some p := f.parent then
      IO.FS.createDirAll p
    IO.FS.writeBinFile f bytes
  let failedObs (reason : String) : Obs :=
    if n == 1 then .phase1 (.failed reason) else .phase2 "" (.failed reason)
  let g ←
    match ← graph n mods built fun m => (s.library / (stem m ++ ".lean")).pathExists with
    | .ok g =>
      pure g
    | .error (reason, presence) =>
      return {
          obs := failedObs reason
          capture := some { phase := n, step := "graph", presence, inputs := [("src", sources)] }
          libRoots := libPrev }
  let abiModule := (r.abi.map (·.1)).toList
  let libRoots := (libPrev ++ [r.specModule] ++ abiModule ++ g.library).eraseDups
  let entries ←
    match ← FvdepIO.Cache.build s.cache s.library libRoots with
    | .ok es =>
      pure es
    | .error f =>
      return { obs := .infra (infraOf f.code) s!"phase {n}, the library: {f.detail}", libRoots }
  let view := run / s!"view{n}"
  if let .error f← FvdepIO.Cache.view s.cache view (entries.map fun x => (x.key, x.manifest)) then
    return { obs := .infra (infraOf f.code) s!"phase {n}, the library view: {f.detail}", libRoots }
  let exportImports := (g.order ++ [r.specModule] ++ abiModule).eraseDups
  let roots := if n == 1 then r.roots1 else r.roots2
  let libConsts := [r.spec] ++ (r.abi.map (·.2)).toList
  let empty := run / "empty"
  IO.FS.createDirAll empty
  let st ← IO.mkRef ({} : Shared)
  let exec : Step → IO StepResult := fun step => do
    st.modify fun x => { x with current := some step }
    let untilMs ←
      match step with
      | .libraryRoots =>
        pure none
      | _ =>
        match (← st.get).window with
        | some u =>
          pure (some u)
        | none =>
          let u := (← IO.monoMsNow) + lim.deadline * 1000
          st.modify fun x => { x with window := some u }
          pure (some u)
    if let some u := untilMs then
      if u ≤ (← IO.monoMsNow) then
        return { outcome := .timedOut, frame := .missing, exhausted := false, diagnostic := "" }
    let stepLim :=
      if step == .libraryRoots then { lim with deadline := s.cache.limits.fillBudget } else lim
    let (src, imports, rs, isMod) ←
      match step with
      | .compile m =>
        let src := run / s!"src{n}" / m
        let f := src / (stem m ++ ".lean")
        if let some p := f.parent then
          IO.FS.createDirAll p
        IO.FS.writeBinFile f (((mods.find? (·.1 == m)).map (·.2)).getD .empty)
        pure (src, [], [], (g.isModule.lookup m).getD false)
      | .libraryRoots | .consumerRoots =>
        let (imports, rs) :=
          if step == .libraryRoots then ([r.specModule] ++ abiModule, libConsts)
          else (exportImports, roots)
        let src := run / s!"roots{n}-{if step == .libraryRoots then "library" else "consumer"}"
        IO.FS.createDirAll src
        IO.FS.writeFile (src / "FvdepRoots.lean") (rootsSource imports rs)
        pure (src, imports, rs, false)
      | .exportStep =>
        pure (empty, exportImports, roots, false)
    match ← judge s n step src view (run / "consumer") imports rs isMod stepLim untilMs with
    | .error why =>
      return { outcome := .setupFailed why, frame := .missing, exhausted := false,
               diagnostic := "" }
    | .ok (res, obs, over, missing) =>
      st.modify fun x => { x with last := some (step, obs, over, src, missing) }
      if stepVerdict step res == .pass then
        if let .ok o := obs.frame then
          match step with
          | .compile _ =>
            let recs ← freeze (run / s!"phase{n}") o.files
            discard <| freeze (run / "consumer") o.files
            st.modify fun x => { x with artifacts := x.artifacts ++ recs }
          | .exportStep =>
            let recs ← freeze (run / "exports") (o.files.map fun f => (s!"e{n}.ndjson", f.2))
            st.modify fun x => { x with exported := recs.head? }
          | _ =>
            pure ()
      return res
  let plan := (if n == 1 then [Step.libraryRoots] else []) ++ steps g.order
  let outcome ← drive exec plan
  let sh ← st.get
  let e := (sh.exported.map (·.sha256)).getD ""
  let obs := if n == 1 then observe1 outcome e else observe2 "" outcome e
  let frozen :=
    if outcome.isNone then
      sh.exported.map fun x => { artifacts := sh.artifacts.toList, exported := x }
    else none
  match obs, sh.last with
  | .infra code d, last =>
    -- The step that stopped the phase; a step never spawned (no time left, bwrap not started) has
    -- no observation of its own.
    let d :=
      match last, sh.current with
      | some (step, o, over, _, missing), some f =>
        if step == f then
          -- P4: an absent library root (its child refused the roots file) is named.
          let d :=
            match step, o.frame with
            | .libraryRoots, .ok fr =>
              if fr.status.child.helperExit != 0 then s!"{d}: {missing}" else d
            | _, _ => d
          detailOf n step lim over o d
        else s!"phase {n}, {stepName f}: {d}"
      | none, some f => s!"phase {n}, {stepName f}: {d}"
      | _, none => s!"phase {n}: {d}"
    return { obs := .infra code d, libRoots }
  | .phase1 (.failed _), some (step, o, _, src, _) | .phase2 _ (.failed _),
    some (step, o, _, src, _) =>
    let (imports, rs) :=
      match step with
      | .libraryRoots => ([r.specModule] ++ abiModule, libConsts)
      | .consumerRoots | .exportStep => (exportImports, roots)
      | .compile _ => ([], [])
    let module :=
      match step with
      | .compile m => m
      | _ => ""
    return {
        obs
        capture :=
          some
            { phase := n
              step := stepKind step
              module
              imports
              roots := rs
              inputs := inputsOf run src view
              stdout := o.stdout.kept
              stderr := o.stderr.kept }
        libRoots }
  | _, _ =>
    return { obs, frozen, libRoots }

/-- `phaseBody`, a host I/O failure of the supervisor's own (its run directory, a library file read)
= `infra io` (P5), never an exception the caller reads as a verdict. -/
def phase (s : Setup) (r : Request) (n : Nat) (mods : List (String × ByteArray))
    (built libPrev : List String) : IO PhaseRun :=
  tryCatch (phaseBody s r n mods built libPrev) fun ex =>
    pure { obs := .infra .io s!"phase {n}: a host I/O operation failed: {ex}", libRoots := libPrev }

/-- A command's fresh run directory on the cache's filesystem (`<cache>/runs/<pid>.<ns>`): K4's
views = hard links into the cache, which `link(2)` refuses across filesystems (`EXDEV`). -/
def runDir (cache : System.FilePath) : IO System.FilePath := do
  let dir := cache / "runs" / s!"{← IO.Process.getPID}.{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  return dir

/-- The phase-2 observation bound to the e1 it was built on (U2 E: `phase2 e1 …`). -/
def bindE1 (e1 : Digest) : Obs → Obs
  | .phase2 _ b => .phase2 e1 b
  | o => o

/-- P3 → P6: S2's digests, phase 1, then phase 2 only after `phase1 (ok e1)` (bound to that e1). -/
def check (s : Setup) (r : Request) : IO Report := do
  let run := s.cache.run
  let implSources := FvdepIO.Hash.digest .implSources (sourceFiles r.impl)
  let proofSources := FvdepIO.Hash.digest .proofSources (sourceFiles r.proof)
  try
    for d in ["phase1", "phase2", "exports", "consumer"] do
      IO.FS.createDirAll (run / d)
  catch ex =>
    return {
        implSources
        proofSources
        runs := [{ obs := .infra .io s!"the run directory could not be prepared: {ex}" }] }
  let one ← phase s r 1 r.impl [] []
  match one.obs with
  | .phase1 (.ok e1) =>
    let two ← phase s r 2 r.proof (r.impl.map (·.1)) one.libRoots
    return { implSources, proofSources, runs := [one, { two with obs := bindE1 e1 two.obs }] }
  | _ =>
    return { implSources, proofSources, runs := [one] }

end FvdepIO.Phase
