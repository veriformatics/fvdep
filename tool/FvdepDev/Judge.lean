import FvdepCore.Oracle.Command
import FvdepIO.Judge
import FvdepIO.Phase
import FvdepIO.Tools

/-! `fvdep-dev judge profile|pins|kernels` (contract U7 V2, K4, D3; never shipped): `profile`
prints the verification profile v1's persisted form (`docs/verification-profile.json`'s bytes);
`pins` checks K4 on fvdep's own toolchain (`pins hold`, else `infra tool_missing: …`, exit 2);
`kernels <e2> [--kernel-binary <k>=<path>]… [--limit kernel.<k>.deadline=<s>]…
[--pin <k>=<sha256>]… [--e2-digest <hex>]` runs the kernel phase on `e2` (its frozen digest =
`--e2-digest`, else the file's own; `--pin` = a kernel's expected SHA-256), one line per kernel
`kernel <k> <status>`, after `SIMULATION (overrides: …)` when an option overrides v1; exit 0 every
kernel accepts, 1 a non-acceptance, 2 infrastructure. -/

namespace FvdepDev.Judge

open FvdepCore.Evidence FvdepCore.Judge

def usage : String :=
  "usage: fvdep-dev judge profile\n" ++ "       fvdep-dev judge pins\n" ++
    "       fvdep-dev judge run <e1> <e2> --spec <c> --impl <c> --proof <c> [--abi <c>] " ++
    "[--limit judge.work=<n>] [--limit kernel.<k>.deadline=<s>]… [--kernel-binary <k>=<path>]…\n" ++
    "       fvdep-dev judge kernels <e2> [--kernel-binary <k>=<path>]… " ++
    "[--limit kernel.<k>.deadline=<s>]… [--pin <k>=<sha256>]… [--e2-digest <hex>]\n"

def say (ls : List String) : IO Unit := do
  let out ← IO.getStdout
  for l in ls do
    out.putStrLn (FvdepCore.Doc.escapeControls l)

def kernelOf : String → Option Kernel
  | "lean" => some .lean
  | "con-leche" => some .conLeche
  | "nanoda" => some .nanoda
  | _ => none

def statusText : KResult → String
  | .infra c d => s!"infra {FvdepCore.Oracle.Command.infraWord c} {d}"
  | .status .accept => "accept"
  | .status .reject => "reject"
  | .status .crash => "crash"
  | .status (.timeout s) => s!"timeout {s}"
  | .status (.decline d) => s!"decline {d}"

structure Options where
  e2 : Option String := none
  stubs : List (Kernel × System.FilePath) := []
  deadlines : List (Kernel × Nat) := []
  overrides : List String := []
  digest : Option String := none
  pins : List (Kernel × String) := []

partial def parse (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--kernel-binary" :: v :: rest =>
    match v.splitOn "=", (v.splitOn "=").head?.bind kernelOf with
    | [k, path], some kk =>
      if o.stubs.any (·.1 == kk) then .error s!"--kernel-binary {k} given twice"
      else
        parse
          { o with
            stubs := o.stubs ++ [(kk, System.FilePath.mk path)]
            overrides := o.overrides ++ [s!"--kernel-binary {k}"] }
          rest
    | _, _ => .error s!"--kernel-binary takes <k>=<path>, <k> one of lean, con-leche, nanoda: {v}"
  | "--limit" :: v :: rest =>
    match v.splitOn "=" with
    | [key, n] =>
      match key.splitOn ".", n.toNat? with
      | ["kernel", k, "deadline"], some s =>
        match kernelOf k with
        | some kk =>
          if o.deadlines.any (·.1 == kk) then .error s!"--limit {key} given twice"
          else
            if s == 0 then .error s!"--limit {key} takes at least 1 second"
            else
              parse
                { o with
                  deadlines := o.deadlines ++ [(kk, s)]
                  overrides := o.overrides ++ [s!"--limit {key}"] }
                rest
        | none => .error s!"unknown kernel {k}"
      | _, _ => .error s!"unknown limit {v}"
    | _ => .error s!"--limit takes <key>=<value>: {v}"
  | "--pin" :: v :: rest =>
    match v.splitOn "=", (v.splitOn "=").head?.bind kernelOf with
    | [k, h], some kk =>
      if o.pins.any (·.1 == kk) then .error s!"--pin {k} given twice"
      else
        parse
          { o with
            pins := o.pins ++ [(kk, h)]
            overrides := o.overrides ++ [s!"--pin {k}"] }
          rest
    | _, _ => .error s!"--pin takes <k>=<sha256>, <k> one of lean, con-leche, nanoda: {v}"
  | "--e2-digest" :: h :: rest =>
    if o.digest.isSome then .error "--e2-digest given twice"
    else parse { o with digest := some h } rest
  | x :: rest =>
    if x.startsWith "--" || o.e2.isSome then .error s!"unexpected argument {x}"
    else parse { o with e2 := some x } rest

/-- `p` with kernel `k`'s entry changed by `f`. -/
def setKernel (p : VProfile) (k : Kernel) (f : VKernel → VKernel) : VProfile :=
  match k with
  | .lean => { p with lean := f p.lean }
  | .conLeche => { p with conLeche := f p.conLeche }
  | .nanoda => { p with nanoda := f p.nanoda }

/-- v1 under D3's overrides: deadlines + expected kernel digests. -/
def overridden (o : Options) : VProfile :=
  let p := o.deadlines.foldl (fun p d => setKernel p d.1 fun x => { x with deadline := d.2 }) v1
  o.pins.foldl (fun p d => setKernel p d.1 fun x => { x with sha256 := d.2 }) p

/-- T1's tools in a fresh run directory, then `act` (the directory removed after). -/
def withTools (act : String → System.FilePath → System.FilePath → String → IO UInt32) : IO UInt32 :=
  do
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
    match ← FvdepIO.Tools.tools root run with
    | .ok (sys, fp) =>
      act bwrap sys run fp
    | .error e =>
      say [s!"infra tool_missing: {e}"]
      return 2
  finally
    try
      IO.FS.removeDirAll run
    catch ex =>
      IO.eprintln s!"fvdep-dev: the run directory {run} stayed: {ex}"

def pins : IO UInt32 :=
  withTools fun _ sys _ fp => do
    match ← FvdepIO.Judge.pins sys fp v1 [] with
    | some why =>
      say [s!"infra tool_missing: {why}"]
      return 2
    | none =>
      say ["pins hold"]
      return 0

def kernelsCmd (o : Options) (e2 : String) : IO UInt32 :=
  withTools fun bwrap sys run fp => do
    let digest ←
      match o.digest with
      | some h =>
        pure h
      | none =>
        pure (FvdepCore.Hash.hex (← FvdepIO.Hash.sha256File e2))
    let head :=
      if o.overrides.isEmpty then []
      else [s!"SIMULATION (overrides: {", ".intercalate o.overrides})"]
    let p := overridden o
    match
      ← FvdepIO.Judge.run bwrap sys (run / "step") (run / "kernel-src") fp p e2 digest o.stubs with
    | .error (c, d) =>
      say (head ++ [s!"infra {FvdepCore.Oracle.Command.infraWord c}: {d}"])
      return 2
    | .ok rs =>
      say (head ++ rs.map fun r => s!"kernel {kernelName r.kernel} {statusText r.result}")
      if rs.any fun r => r.result matches .infra .. then
        return 2
      else
        if rs.all fun r => r.result == .status .accept then
          return 0
        else
          return 1

/-- D1: v1 under `--limit judge.work` + `kernel.<k>.deadline` (each an override: SIMULATION). -/
def withJudgeLimits (p : VProfile) (work : Option Nat) (ds : List (Kernel × Nat)) : VProfile :=
  let p := ds.foldl (fun p d => setKernel p d.1 fun x => { x with deadline := d.2 }) p
  match work with
  | some w => { p with work := w }
  | none => p

/-- D1: a reason code's interface §6 spelling. -/
def codeWord : Code → String
  | .profileConstruct => "profile_construct"
  | .importNotAllowed => "import_not_allowed"
  | .reservedModule => "reserved_module"
  | .buildFailed => "build_failed"
  | .statementMismatch => "statement_mismatch"
  | .graphMismatch => "graph_mismatch"
  | .axiom => "axiom"
  | .kernelReject => "kernel_reject"
  | .kernelCrash => "kernel_crash"
  | .kernelTimeout => "kernel_timeout"
  | .kernelDecline => "kernel_decline"
  | .sandboxSetup => "sandbox_setup"
  | .toolMissing => "tool_missing"
  | .adapter => "adapter"
  | .fetchFailed => "fetch_failed"
  | .io => "io"
  | _ => "internal"

/-- D1: J's observation lines. -/
def judgeLine : Obs → String
  | .statement _ _ b => s!"statement {if b then "matched" else "mismatch"}"
  | .graph _ _ b => s!"graph {if b then "matched" else "mismatch"}"
  | .axioms _ ns => "axioms" ++ String.join (ns.map (" " ++ ·))
  | .kernel _ k s => s!"kernel {kernelName k} {statusText (.status s)}"
  | .infra c d => s!"infra {FvdepCore.Oracle.Command.infraWord c}: {d}"
  | _ => "infra io: internal: an observation the judge never makes"

/-- D1 + interface §4: the verdict block — line 1 + one `  detail:` line per listed reason (J4's
causes, in U2's order); under an override line 1 reads `SIMULATION …` (D3). Exit 0 PROVEN, 1 NOT
PROVEN, 2 infrastructure. -/
def verdictBlock (id impl : String) (sim : List String) (r : Result) (details : List String) :
    List String × UInt32 :=
  let tail := if sim.isEmpty then "" else s!" (overrides: {", ".intercalate sim})"
  let head := if sim.isEmpty then "" else "SIMULATION "
  let dl (n : Nat) := (details.take n).map ("  detail: " ++ ·)
  match r with
  | .verdict .proven _ => ([s!"{head}PROVEN {id} {impl}{tail}"], 0)
  | .verdict _ rs =>
    ([s!"{head}NOT PROVEN {id}: {(rs.head?.map (·.detail)).getD ""}{tail}"] ++ dl rs.length, 1)
  | .infra c ns => ([s!"{head}infra {codeWord c.code}: {c.detail}{tail}"] ++ dl ns.length, 2)

/-- D2's request: the names + D3's overrides (`kernels`' options) + `--limit judge.work`. -/
structure RunOptions where
  files : List String := []
  spec : Option String := none
  impl : Option String := none
  proof : Option String := none
  abi : Option String := none
  work : Option Nat := none
  k : Options := {}

partial def parseRun (o : RunOptions) : List String → Except String RunOptions
  | [] => .ok o
  | "--spec" :: v :: rest => parseRun { o with spec := some v } rest
  | "--impl" :: v :: rest => parseRun { o with impl := some v } rest
  | "--proof" :: v :: rest => parseRun { o with proof := some v } rest
  | "--abi" :: v :: rest => parseRun { o with abi := some v } rest
  | "--limit" :: v :: rest =>
    match v.splitOn "=" with
    | ["judge.work", n] =>
      match n.toNat? with
      | some w =>
        if o.work.isSome then .error "--limit judge.work given twice"
        else
          parseRun
            { o with
              work := some w
              k := { o.k with overrides := o.k.overrides ++ ["--limit judge.work"] } }
            rest
      | none => .error s!"--limit judge.work takes a number: {v}"
    | _ =>
      match parse o.k ["--limit", v] with
      | .ok k => parseRun { o with k } rest
      | .error e => .error e
  | "--kernel-binary" :: v :: rest =>
    match parse o.k ["--kernel-binary", v] with
    | .ok k => parseRun { o with k } rest
    | .error e => .error e
  | x :: rest =>
    if x.startsWith "--" then .error s!"unexpected argument {x}"
    else parseRun { o with files := o.files ++ [x] } rest

/-- D2: J on two given exports (their digests = their own bytes'; each at most T's export cap,
checked before any read): the stages, then K, then U2's verdict over the phases' observations as
if both built — always SIMULATION (a given e1 is no phase 1's), the request named `judge`. -/
def runCmd (o : RunOptions) (e1 e2 spec impl proof : String) : IO UInt32 :=
  withTools fun bwrap sys run fp => do
    let some decl :=
      (FvdepCore.Ids.ModuleId.parse "judge.given").bind fun m =>
        (FvdepCore.Ids.EntryVersion.parse "1.0.0").map fun v =>
          ({  module := m, version := v, shape := some (if o.abi.isSome then .abi else .fn)
              kind := .proof, impl := some impl, proof := some proof, adapter := none } : Decl) |
      do
        say ["infra io: internal: no request key"]
        return 2
    let r : Request :=
      { impl := impl.toName
        spec := spec.toName
        proof := proof.toName
        abi := o.abi.map String.toName }
    let p := withJudgeLimits (overridden o.k) o.work []
    let key : ChallengeKey :=
      { request :=
          { decl
            specClosure := ""
            implSources := some ""
            proofSources := some ""
            adapter := none }
        library := ⟨List.replicate 40 0, List.length_replicate⟩
        profile := p.evidence
        statement := "" }
    let block (all : List Obs) (details : List String) : List String × UInt32 :=
      verdictBlock "judge" impl ("given e1 + e2" :: o.k.overrides)
        (result key (all.map fun x => ⟨key, x⟩)) details
    let cap := ({} : FvdepCore.Sandbox.Limits).exportCap
    let intake (f : String) : IO (Except String String) :=
      tryCatch
        (do
          let m ← System.FilePath.metadata f
          if cap < m.byteSize.toNat then
            return .error s!"the export {f} passes the export cap of {cap} bytes"
          return .ok (FvdepCore.Hash.hex (← FvdepIO.Hash.sha256File f)))
        fun ex => pure (.error s!"the export {f} could not be read: {ex}")
    let refuse (why : String) : IO UInt32 := do
      let (ls, rc) := block [.infra .io why] []
      say ls
      return rc
    let d1 ←
      match ← intake e1 with
      | .ok d =>
        pure d
      | .error why =>
        return ← refuse why
    let d2 ←
      match ← intake e2 with
      | .ok d =>
        pure d
      | .error why =>
        return ← refuse why
    let jo ←
      FvdepIO.Judge.judge bwrap sys (run / "step") (run / "kernel-src") fp p r e1 e2 d1 d2 o.k.stubs
    let (ls, rc) :=
      block ([.implProfile none, .phase1 (.ok d1), .phase2 d1 (.ok d2)] ++ jo.obs) jo.details
    say (jo.obs.map judgeLine ++ [s!"judge work {jo.used}"] ++ ls)
    return rc

def run : List String → IO UInt32
  | ["profile"] => do
    (← IO.getStdout).write v1.text
    return 0
  | ["pins"] => pins
  | "run" :: rest =>
    match parseRun {} rest with
    | .ok o =>
      match o.files, o.spec, o.impl, o.proof with
      | [e1, e2], some spec, some impl, some proof => runCmd o e1 e2 spec impl proof
      | _, _, _, _ => do
        IO.eprint s!"fvdep-dev: judge run takes <e1> <e2> --spec --impl --proof\n{usage}"
        return 2
    | .error why => do
      IO.eprint s!"fvdep-dev: {why}\n{usage}"
      return 2
  | "kernels" :: rest =>
    match parse {} rest with
    | .ok o =>
      match o.e2 with
      | some e2 => kernelsCmd o e2
      | none => do
        IO.eprint s!"fvdep-dev: judge kernels takes an e2 file\n{usage}"
        return 2
    | .error why => do
      IO.eprint s!"fvdep-dev: {why}\n{usage}"
      return 2
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Judge
