import FvdepCore.Index.Command
import FvdepIO.Cache
import FvdepIO.Toolchain

/-! T1's tools for a command that runs sandbox steps (contract `docs/contracts/U5-sandbox.md` T1;
residues `bwrap`, `lean-toolchain`, `step-helper`): the cache root, bwrap ≥ 0.8.0 on `PATH`, fvdep's
own toolchain (elan resolves the release fvdep was built with), the step helper beside the running
executable, the toolchain's content fingerprint, a command's cache setting. -/

namespace FvdepIO.Tools

open FvdepIO.Cache

/-- `FVDEP_CACHE`, else `$XDG_CACHE_HOME/fvdep`, else `~/.cache/fvdep` (interface §1). -/
def cacheRoot : IO (Option System.FilePath) := do
  let get (k : String) : IO (Option String) := do
    return (← IO.getEnv k).filter (!·.isEmpty)
  if let some c← get "FVDEP_CACHE" then
    return some c
  if let some x← get "XDG_CACHE_HOME" then
    return some (System.FilePath.mk x / "fvdep")
  if let some h← get "HOME" then
    return some (System.FilePath.mk h / ".cache" / "fvdep")
  return none

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

/-- R8: a copy of the step helper beside the running executable, at `<run>/step/fvdep-step` (the
directory bound at `/fvdep/step`). -/
def installHelper (run : System.FilePath) : IO (Except String Unit) := do
  let helper := ((← IO.appPath).parent.getD ".") / "fvdep-step"
  unless ← helper.pathExists do
    return .error s!"fvdep-step is missing beside the running executable ({helper})"
  IO.FS.createDirAll (run / "step")
  IO.FS.writeBinFile (run / "step" / "fvdep-step") (← IO.FS.readBinFile helper)
  IO.setAccessRights (run / "step" / "fvdep-step")
      { user := { read := true, write := true, execution := true }
        group := { read := true, execution := true }
        other := { read := true, execution := true } }
  return .ok ()

/-- T1 + D3's tools: the sysroot (in `run`), the helper copy, the fingerprint. -/
def tools (root run : System.FilePath) : IO (Except String (System.FilePath × String)) := do
  match ← preflightSysroot run with
  | .error e =>
    return .error e
  | .ok sys =>
    if let .error e← installHelper run then
      return .error e
    match ← FvdepIO.Toolchain.fingerprint root sys with
    | .error e =>
      return .error s!"the toolchain fingerprint failed: {e}"
    | .ok fp =>
      return .ok (sys, fp)

/-- A command's cache setting (the tools + recipe filled in once T1 ran). -/
def env (root run : System.FilePath) (limits : FvdepCore.Build.CacheLimits) (bwrap : String := "")
    (sys helper : System.FilePath := "") (fingerprint : String := "") : IO Env := do
  return {
      root
      bwrap
      sysroot := sys
      helper
      recipe := FvdepCore.Build.library FvdepIO.Toolchain.release fingerprint
      limits
      step := { deadline := limits.fillBudget }
      trace := (← IO.getEnv "FVDEP_BUILD_TRACE").map System.FilePath.mk
      run
      handles := ← IO.mkRef #[]
      counter := ← IO.mkRef 0 }

end FvdepIO.Tools
