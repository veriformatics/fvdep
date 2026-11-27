import FvdepDev.Cache
import FvdepDev.Judge
import FvdepDev.ProfileCheck
import FvdepIO.Bundle
import FvdepIO.Snapshot
import FvdepIO.Toml

/-! `fvdep-dev phase check` (contract `docs/contracts/U5-sandbox.md` D1; never shipped): a
manifest entry's two phases over a library working copy — S's snapshot, K's views, P's steps, B2's
bundle on a failure — reported line by line (interface §1's line rule). `--profile` (contract
`docs/contracts/U6-profile.md` D2) = B1's barrier: after S1 + T1 the profile step over the
implementation modules (consumer role, the working copy's library rows), the phases only after
`accepted`. -/

namespace FvdepDev.Phase

open FvdepCore.Build FvdepCore.Sandbox FvdepCore.Evidence FvdepDev.Sandbox FvdepIO.Tools

def usage : String :=
  "usage: fvdep-dev phase check <project dir> <id> --library <library dir> --spec-module <M> " ++
    "--spec <constant> [--abi-module <M> --abi <constant>] [--roots1 <c>…] [--roots2 <c>…] " ++
    "[--deadline <s>] [--work-bytes <n>] [--frame-bytes <n>] [--export-bytes <n>] " ++
    "[--artifacts <dir>] [--profile [--limit <name>=<n>]... [--results <file> | --child <file>]]" ++
    " [--judge [--limit judge.work=<n>] [--limit kernel.<k>.deadline=<s>]...]" ++
    " [--manifest <file>]" ++
    "\n       fvdep-dev phase rerun <bundle dir>\n"

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
  profile : Bool := false
  prof : FvdepDev.ProfileCheck.Options := {}
  profOptions : Bool := false
  judge : Bool := false
  manifest : Option String := none
  judgeWork : Option Nat := none
  kernelDeadlines : List (FvdepCore.Evidence.Kernel × Nat) := []
  simulated : List String := []

/-- The values after a list option, up to the next option. -/
def values (args : List String) : List String × List String :=
  (args.takeWhile fun a => !a.startsWith "--", args.dropWhile fun a => !a.startsWith "--")

/-- `o` with `name` among the overrides its verdict block names (D1: an option changing what is
judged — a limit, the export roots, a given profile result or child — makes it a simulation). -/
def Options.override (o : Options) (name : String) : Options :=
  if o.simulated.contains name then o else { o with simulated := o.simulated ++ [name] }

partial def parse (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--library" :: v :: rest => parse { o with library := v } rest
  | "--spec-module" :: v :: rest => parse { o with specModule := v } rest
  | "--spec" :: v :: rest => parse { o with spec := v } rest
  | "--abi-module" :: v :: rest => parse { o with abiModule := some v } rest
  | "--abi" :: v :: rest => parse { o with abi := some v } rest
  | "--artifacts" :: v :: rest => parse { o with artifacts := some v } rest
  | "--profile" :: rest => parse { o with profile := true } rest
  | "--judge" :: rest => parse { o with judge := true } rest
  | "--manifest" :: v :: rest => parse { o with manifest := some v } rest
  | "--limit" :: v :: rest =>
    match v.splitOn "=", v.splitOn "." with
    | ["judge.work", n], _ =>
      match n.toNat? with
      | some w =>
        if o.judgeWork.isSome then .error "--limit judge.work given twice"
        else
          parse
            { o with
              judgeWork := some w
              simulated := o.simulated ++ ["--limit judge.work"] }
            rest
      | none => .error s!"--limit judge.work takes a number: {v}"
    | [key, n], "kernel" :: _ =>
      match key.splitOn ".", n.toNat? with
      | ["kernel", k, "deadline"], some sec =>
        match FvdepDev.Judge.kernelOf k with
        | some kk =>
          if sec == 0 || o.kernelDeadlines.any (·.1 == kk) then .error s!"--limit {key}: once, ≥ 1"
          else
            parse
              { o with
                kernelDeadlines := o.kernelDeadlines ++ [(kk, sec)]
                simulated := o.simulated ++ [s!"--limit {key}"] }
              rest
        | none => .error s!"unknown kernel {k}"
      | _, _ => .error s!"unknown limit {v}"
    | _, _ =>
      match FvdepDev.ProfileCheck.setLimit o.prof v with
      | .ok p =>
        parse
          ({ o with
                prof := p, profOptions := true }.override
            s!"--limit {(v.splitOn "=").headD v}")
          rest
      | .error e => .error e
  | "--results" :: f :: rest =>
    parse
      ({ o with
            prof := { o.prof with results := some f }, profOptions := true }.override
        "--results")
      rest
  | "--child" :: f :: rest =>
    parse
      ({ o with
            prof := { o.prof with child := some f }, profOptions := true }.override
        "--child")
      rest
  | "--roots1" :: rest =>
    match values rest with
    | ([], _) => .error "--roots1 takes at least one constant"
    | (cs, rest) => parse ({ o with roots1 := some cs }.override "--roots1") rest
  | "--roots2" :: rest =>
    match values rest with
    | ([], _) => .error "--roots2 takes at least one constant"
    | (cs, rest) => parse ({ o with roots2 := some cs }.override "--roots2") rest
  | "--deadline" :: v :: rest =>
    match number "--deadline" v with
    | .ok n =>
      parse ({ o with limits := { o.limits with deadline := n } }.override "--deadline") rest
    | .error e => .error e
  | "--work-bytes" :: v :: rest =>
    match number "--work-bytes" v with
    | .ok n =>
      parse ({ o with limits := { o.limits with workBytes := n } }.override "--work-bytes") rest
    | .error e => .error e
  | "--frame-bytes" :: v :: rest =>
    match number "--frame-bytes" v with
    | .ok n =>
      parse ({ o with limits := { o.limits with frameBytes := n } }.override "--frame-bytes") rest
    | .error e => .error e
  | "--export-bytes" :: v :: rest =>
    match number "--export-bytes" v with
    | .ok n =>
      parse ({ o with limits := { o.limits with exportBytes := some n } }.override "--export-bytes")
        rest
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

/-- D1's U2 refusal for U6's (B3; interface §6's codes): I1's import rule = `import_not_allowed`,
I2's module name = `reserved_module`, every other rule = `profile_construct`; its detail = the
record's module, location + cause (U8 renders interface §4's reason). -/
def refusalOf (f : FvdepCore.Profile.Refusal) : FvdepCore.Evidence.Refusal × String :=
  let code :=
    match f.rule, f.detail with
    | "header", "import" :: _ => FvdepCore.Evidence.Refusal.importNotAllowed
    | "header", "name" :: _ => .reservedModule
    | _, _ => .profileConstruct
  (code, s!"{f.module} {f.line}:{f.column} {" ".intercalate (f.rule :: f.detail)}")

/-- D1: the cause each failed phase recorded (an early stop's `  detail:` lines, J4's cap). -/
def stopCauses (obs : List Obs) : List String :=
  obs.filterMap fun
    | .phase1 (.failed r) | .phase2 _ (.failed r) => some (FvdepCore.Profile.cutDetail r)
    | _ => none

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
  if o.profOptions && !o.profile then
    return ← usageError "--limit, --results and --child go with --profile"
  if o.judge && !o.profile then
    return ← usageError "--judge goes with --profile"
  if (o.judgeWork.isSome || !o.kernelDeadlines.isEmpty) && !o.judge then
    return ← usageError "--limit judge.work and kernel.<k>.deadline go with --judge"
  if o.prof.results.isSome && o.prof.child.isSome then
    return ← usageError "--results and --child exclude each other"
  if let some why := ({ fileBytes := o.prof.fileBytes } : Limits).check then
    return ← usageError why
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
      IO.FS.readBinFile ((o.manifest.map System.FilePath.mk).getD (proj / "fvdep.toml"))
    catch ex =>
      say [s!"infra io: fvdep.toml could not be read: {ex}"]
      return 2
  let mf ←
    match ← FvdepIO.Toml.readManifest text with
    | .ok m =>
      pure m
    | .error e =>
      say [s!"infra {e.code.spelling}: fvdep.toml: {e.detail}"]
      return 2
  let some entry := mf.modules.find? fun e => toString e.decl.module == o.id |
    do
      say [s!"infra io: fvdep.toml has no entry {o.id}"]
      return 2
  let (some impl, some proof) := (entry.decl.impl, entry.decl.proof) |
    do
      say [s!"infra io: the entry {o.id} names no implementation + proof constant"]
      return 2
  let jr : FvdepCore.Judge.Request :=
    { impl := impl.toName
      spec := o.spec.toName
      proof := proof.toName
      abi := o.abi.map String.toName }
  -- J3: each effective export root list (the default or an override) names each root once.
  let roots1 := o.roots1.getD ((FvdepCore.Judge.exportRoots1 jr).map toString)
  let roots2 := o.roots2.getD ((FvdepCore.Judge.exportRoots2 jr).map toString)
  for (n, rs) in [(1, roots1), (2, roots2)] do
    if let some d := firstDuplicate rs then
      return ← usageError s!"phase {n}'s export roots name {d} twice"
  let src ←
    match ← FvdepIO.Snapshot.read proj entry.implModules entry.proofModules with
    | .ok s =>
      pure s
    | .error d =>
      say [s!"infra io: {d}"]
      return 2
  let implD := FvdepIO.Hash.digest .implSources (FvdepCore.Phase.sourceFiles src.impl)
  let proofD := FvdepIO.Hash.digest .proofSources (FvdepCore.Phase.sourceFiles src.proof)
  let jp := FvdepDev.Judge.withJudgeLimits FvdepCore.Judge.v1 o.judgeWork o.kernelDeadlines
  let key : FvdepCore.Evidence.ChallengeKey :=
    { request :=
        { decl := entry.decl
          specClosure := ""
          implSources := some implD
          proofSources := some proofD
          adapter := none }
      library := ⟨List.replicate 40 0, List.length_replicate⟩
      profile := jp.evidence
      statement := "" }
  -- U7 D1's verdict block: U2's result over every observation so far (U6's, U5's, J's), one key.
  let finalize (all : List Obs) (details : List String) : List String × UInt32 :=
    FvdepDev.Judge.verdictBlock s!"{o.id}@{entry.decl.version}" impl o.simulated
      (FvdepCore.Evidence.result key (all.map fun x => ⟨key, x⟩)) details
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
    -- U6 B1 (D2): the profile step before any graph, fill, view or compile.
    let mut head : List String := []
    if o.profile then
      let frozen := src.impl.mergeSort fun a b => Decidable.decide (a.1 ≤ b.1)
      head :=
        [s!"impl_sources {implD}", s!"proof_sources {proofD}"] ++
          FvdepDev.ProfileCheck.moduleLines frozen
      let rows ←
        match ← FvdepIO.Profile.libraryRows lib with
        | .ok rs =>
          pure rs
        | .error why =>
          say (head ++ [s!"infra io: {why}"])
          return 2
      let (digest, verdict) ←
        FvdepDev.ProfileCheck.runProfile o.prof .consumer rows frozen bwrap sys run fp
      let (ls, rc) := FvdepDev.ProfileCheck.report verdict
      head := head ++ s!"request {digest}" :: ls
      unless verdict matches .accepted _ do
        if o.judge then
          let (seen, causes) : Obs × List String :=
            match verdict with
            | .refused _ f => (.implProfile (some (refusalOf f)), [(refusalOf f).2])
            | .infra c d => (.infra c d, [])
            | .accepted _ => (.implProfile none, [])
          let (block, brc) := finalize [seen] (causes.map FvdepCore.Profile.cutDetail)
          say (head ++ block)
          return brc
        say head
        return rc
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
        roots1
        roots2
        trusted :=
          if o.roots1.isSome || o.roots2.isSome then []
          else (FvdepCore.Judge.trustedRoots jr).map toString }
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
    -- U7 D1: J on the frozen exports, then the verdict block; a phase stop's block without J.
    let (judgeLines, judgeRc) ←
      match o.judge, obs with
      | true, [.phase1 (.ok d1), .phase2 _ (.ok d2)] =>
        do
          let jo ←
            FvdepIO.Judge.judge bwrap sys (run / "step") (run / "kernel-src") fp jp jr
                (run / "exports" / "e1.ndjson") (run / "exports" / "e2.ndjson") d1 d2 (cap :=
                o.limits.exportCap)
          let (block, rc) := finalize (.implProfile none :: obs ++ jo.obs) jo.details
          let times :=
            jo.kernels.map fun x => s!"time kernel {FvdepCore.Evidence.kernelName x.kernel} {x.ms}"
          pure
              (jo.obs.map FvdepDev.Judge.judgeLine ++ [s!"judge work {jo.used}"] ++ times ++ block,
                some rc)
      | true, _ =>
        let (block, rc) := finalize (.implProfile none :: obs) (stopCauses obs)
        pure (block, some rc)
      | false, _ =>
        pure ([], none)
    say
        ((if o.profile then head
          else [s!"impl_sources {rep.implSources}", s!"proof_sources {rep.proofSources}"]) ++
          obs.map obsLine ++
          fileLines ++
          bundleLines.toList ++
          judgeLines)
    if let some dir := o.artifacts then
      try
        retain dir run files
      catch ex =>
        say [s!"infra io: the artifacts could not be kept in {dir}: {ex}"]
        return 2
    return judgeRc.getD (exitOf obs)
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
