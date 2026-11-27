import FvdepCore.Judge.Plan
import FvdepIO.Sandbox
import FvdepIO.Sha256

/-! U7 K1 + K4 (contract `docs/contracts/U7-judge.md`): the kernel phase's IO — K4's pins (T1's
fingerprint + the three kernel binaries' SHA-256 against the profile), e2 + NanoDa's config staged
into a fresh source directory (e2's digest checked on staging), then each kernel alone through U5's
runner in U2's order, every one run whatever another reported; K2 judges each observation
(residues `kernels`, `sandbox-spawn`, `toolchain-install`). -/

namespace FvdepIO.Judge

open FvdepCore.Evidence FvdepCore.Judge

/-- K2's view of U5's frame: the child's status, the data files it carried, a full tmpfs. -/
def kframeOf : FvdepIO.Sandbox.Received → KFrame
  | .ok out => .ok out.status.child out.files.length (out.status.workFull || out.status.tmpFull)
  | .overflow => .overflow
  | .invalid => .invalid

/-- K2's input from one observation: both streams as kept, `whole` = no byte dropped. -/
def kernelRunOf (deadline : Nat) (o : FvdepIO.Sandbox.Observation) : KernelRun :=
  { outcome := o.outcome
    frame := kframeOf o.frame
    stdout := o.stdout.kept
    stderr := o.stderr.kept
    whole := o.stdout.dropped == 0 && o.stderr.dropped == 0
    deadline }

/-- K4: kernel `k`'s binary under the toolchain at `sys` — its SHA-256 hex, or why it is missing;
`none` = D3's stub (its own pin skipped). -/
def digest1 (sys : System.FilePath) (stubs : List Kernel) (k : Kernel) :
    IO (Option (Except String String)) := do
  if stubs.contains k then
    return none
  let path := sys / "bin" / kernelBin k
  unless ← path.pathExists do
    return some (.error s!"the kernel binary {path} is missing")
  return some (.ok (FvdepCore.Hash.hex (← FvdepIO.Hash.sha256File path)))

/-- K4 in its order while acquired: T1's fingerprint, then each kernel binary hashed + compared in
turn (`pinCheck`'s texts); `none` = the pins hold. -/
def pins (sys : System.FilePath) (fingerprint : String) (p : VProfile) (stubs : List Kernel) :
    IO (Option String) := do
  if let some why := pinCheck p fingerprint fun _ => none then
    return some why
  for k in kernels do
    if let some h← digest1 sys stubs k then
      match h with
      | .error e =>
        return some e
      | .ok d =>
        if let some why := pinCheck p fingerprint fun j => if j == k then some d else none then
          return some why
  return none

/-- K1: a fresh source directory `dir` = e2's bytes (the copy re-read + hashed = `digest`, the
frozen export's), NanoDa's config (both 0644) + D3's stubs (0755). -/
def stage (dir e2 : System.FilePath) (digest : String) (p : VProfile)
    (stubs : List (Kernel × System.FilePath)) : IO (Except String Unit) := do
  if ← dir.pathExists then
    IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let target := dir / "e2.ndjson"
  IO.FS.writeBinFile target (← IO.FS.readBinFile e2)
  let got := FvdepCore.Hash.hex (← FvdepIO.Hash.sha256File target)
  if got != digest then
    return .error s!"the staged e2 has SHA-256 {got}; the frozen export's is {digest}"
  IO.FS.writeBinFile (dir / "nanoda.json") (nanodaConfig p.allowlist p.nanoda.threads)
  for f in [target, dir / "nanoda.json"] do
    IO.setAccessRights f
        { user := { read := true, write := true }
          group := { read := true }
          other := { read := true } }
  for (k, path) in stubs do
    let t := dir / ("stub-" ++ kernelBin k)
    IO.FS.writeBinFile t (← IO.FS.readBinFile path)
    IO.setAccessRights t
        { user := { read := true, write := true, execution := true }
          group := { read := true, execution := true }
          other := { read := true, execution := true } }
  return .ok ()

/-- U5's runner as K1 calls it: a step's spec + limits → its observation (a test injects
another). -/
abbrev StepRunner :=
  FvdepCore.Sandbox.Spec → FvdepCore.Sandbox.Limits → IO (Except String FvdepIO.Sandbox.Observation)

/-- One kernel's step as K1 ran it: K2's result, J4's line, its wall-clock in ms (Q1's measure). -/
structure KernelOut where
  kernel : Kernel
  result : KResult
  line : String
  ms : Nat

/-- K1: each kernel alone in U2's order — every one run whatever another reported — its binary the
toolchain's, or D3's stub staged in `src`; each with J4's line (the kernel's own message). -/
def kernelPhaseWith (step : StepRunner) (sys stepDir src : System.FilePath) (p : VProfile)
    (stubs : List Kernel) : IO (List KernelOut) := do
  let mut out := []
  for k in kernels do
    let t0 ← IO.monoMsNow
    let bin := if stubs.contains k then stubPath k else kernelPath k
    let spec :=
      kernelSpec sys.toString stepDir.toString src.toString p.step (p.kernel k).threads k bin
    let r ←
      tryCatch
          (do
            match ← step spec (p.limits k) with
            | .ok o =>
              let kr := kernelRunOf (p.kernel k).deadline o
              pure (kernelStatus k kr, kernelLine kr)
            | .error e =>
              pure (.infra .sandboxSetup e, e))
          fun ex => pure (.infra .io s!"the kernel step failed: {ex}", s!"{ex}")
    out := out ++ [⟨k, r.1, r.2, (← IO.monoMsNow) - t0⟩]
  return out

/-- The kernel phase: K4's pins, the staged source directory `src`, then the three steps;
infrastructure before any step = `.error (code, detail)`. -/
def runWith (step : StepRunner) (sys stepDir src : System.FilePath) (fingerprint : String)
    (p : VProfile) (e2 : System.FilePath) (digest : String)
    (stubs : List (Kernel × System.FilePath)) : IO (Except (Infra × String) (List KernelOut)) := do
  let stubKs := stubs.map (·.1)
  if let some why← pins sys fingerprint p stubKs then
    return .error (.toolMissing, why)
  match ← stage src e2 digest p stubs with
  | .error e =>
    return .error (.io, e)
  | .ok () =>
    return .ok (← kernelPhaseWith step sys stepDir src p stubKs)

/-- The kernel phase through U5's runner. -/
def run (bwrap : String) (sys stepDir src : System.FilePath) (fingerprint : String) (p : VProfile)
    (e2 : System.FilePath) (digest : String) (stubs : List (Kernel × System.FilePath)) :
    IO (Except (Infra × String) (List KernelOut)) :=
  runWith (fun spec lim => FvdepIO.Sandbox.run bwrap spec lim) sys stepDir src fingerprint p e2
    digest stubs

/-- J1 + X8: an export's bytes, read once + checked against the digest its phase recorded. -/
def readExport (path : System.FilePath) (digest : String) : IO Read := do
  try
    let b ← IO.FS.readBinFile path
    let h := FvdepIO.Hash.sha256Hex b
    if h != digest then
      return .error s!"{path.fileName.getD ""} has SHA-256 {h}; its phase recorded {digest}"
    return .ok b
  catch e =>
    return .error s!"{e}"

/-- J's result: the observations (U2 E2), J4's causes in U2's reason order, W's units S + G took,
the kernels' steps (empty unless K ran). -/
structure JudgeOut where
  obs : List Obs
  details : List String
  used : Nat
  kernels : List KernelOut

/-- J: the judge over one request's frozen exports (`e1`, `e2` + the digests their phases
recorded): the stages, then — reached — the kernel phase on e2; J4's causes = S's or G's cause, A's
failing names, then each non-accepting kernel's own line. -/
def judge (bwrap : String) (sys step src : System.FilePath) (fingerprint : String) (p : VProfile)
    (r : Request) (e1 e2 : System.FilePath) (d1 d2 : String)
    (stubs : List (Kernel × System.FilePath) := []) : IO JudgeOut := do
  let b1 ← readExport e1 d1
  let b2 ← readExport e2 d2
  let pre := stages p Lean.githash Lean.versionString r d1 d2 b1 b2
  if !pre.kernels then
    return ⟨pre.obs, pre.details, pre.used, []⟩
  match ← run bwrap sys step src fingerprint p e2 d2 stubs with
  | .error (c, d) =>
    return ⟨pre.obs ++ [.infra c d], pre.details, pre.used, []⟩
  | .ok ks =>
    let lines :=
      ks.filterMap fun x =>
        match x.result with
        | .status .accept | .infra .. => none
        | _ => some x.line
    return ⟨judgeObs pre d2 (ks.map fun x => (x.kernel, x.result)), pre.details ++ lines, pre.used,
        ks⟩

end FvdepIO.Judge
