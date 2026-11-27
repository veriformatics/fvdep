import FvdepCore.Judge.Profile
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

/-- K4: each kernel binary's SHA-256 hex under the toolchain at `sys` (`none` = D3's stub). -/
def digests (sys : System.FilePath) (stubs : List Kernel) :
    IO (Except String (List (Kernel × Option String))) := do
  let mut out := []
  for k in kernels do
    if stubs.contains k then
      out := out ++ [(k, none)]
    else
      let path := sys / "bin" / kernelBin k
      unless ← path.pathExists do
        return .error s!"the kernel binary {path} is missing"
      out := out ++ [(k, some (FvdepCore.Hash.hex (← FvdepIO.Hash.sha256File path)))]
  return .ok out

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

/-- K1: each kernel alone in U2's order — every one run whatever another reported — its binary the
toolchain's, or D3's stub staged in `src`. -/
def kernelPhase (bwrap : String) (sys step src : System.FilePath) (p : VProfile)
    (stubs : List Kernel) : IO (List (Kernel × KResult)) := do
  let mut out := []
  for k in kernels do
    let bin := if stubs.contains k then stubPath k else kernelPath k
    let spec := kernelSpec sys.toString step.toString src.toString p.step (p.kernel k).threads k bin
    let r ←
      match ← FvdepIO.Sandbox.run bwrap spec (p.limits k) with
      | .ok o =>
        pure (kernelStatus k (kernelRunOf (p.kernel k).deadline o))
      | .error e =>
        pure (.infra .sandboxSetup e)
    out := out ++ [(k, r)]
  return out

/-- The kernel phase: K4's pins, the staged source directory `src`, then the three steps;
infrastructure before any step = `.error (code, detail)`. -/
def run (bwrap : String) (sys step src : System.FilePath) (fingerprint : String) (p : VProfile)
    (e2 : System.FilePath) (digest : String) (stubs : List (Kernel × System.FilePath)) :
    IO (Except (Infra × String) (List (Kernel × KResult))) := do
  let stubKs := stubs.map (·.1)
  match ← digests sys stubKs with
  | .error e =>
    return .error (.toolMissing, e)
  | .ok ds =>
    if let some why := pinCheck p fingerprint fun k => (ds.lookup k).join then
      return .error (.toolMissing, why)
    match ← stage src e2 digest p stubs with
    | .error e =>
      return .error (.io, e)
    | .ok () =>
      return .ok (← kernelPhase bwrap sys step src p stubKs)

end FvdepIO.Judge
