import FvdepCore.Index.Assemble
import FvdepDev.Sandbox
import FvdepIO.Cache
import FvdepIO.Toolchain

/-! `fvdep-dev cache build|list|evict|fingerprint` (contract `docs/contracts/U5-sandbox.md` D3;
never shipped): K's fills, listing + eviction over `FVDEP_CACHE`; each line through interface §1's
line rule. -/

namespace FvdepDev.Cache

open FvdepIO.Cache FvdepDev.Sandbox

def usage : String :=
  "usage: fvdep-dev cache build <library dir> <module>…\n" ++
    "       fvdep-dev cache list | evict | fingerprint\n"

/-- `FVDEP_CACHE`, else `$XDG_CACHE_HOME/fvdep`, else `~/.cache/fvdep` (interface §1). -/
def root : IO (Option System.FilePath) := do
  let get (k : String) : IO (Option String) := do
    return (← IO.getEnv k).filter (!·.isEmpty)
  if let some c← get "FVDEP_CACHE" then
    return some c
  if let some x← get "XDG_CACHE_HOME" then
    return some (System.FilePath.mk x / "fvdep")
  if let some h← get "HOME" then
    return some (System.FilePath.mk h / ".cache" / "fvdep")
  return none

/-- K5's target: `FVDEP_CACHE_BYTES` (whole bytes, 0 allowed), else 4 GiB. -/
def target : IO (Except String Nat) := do
  match ← IO.getEnv "FVDEP_CACHE_BYTES" with
  | none =>
    return .ok FvdepCore.Build.defaultCacheBytes
  | some s =>
    match s.toNat? with
    | some n =>
      return .ok n
    | none =>
      return .error s!"FVDEP_CACHE_BYTES takes a whole number of bytes, got {s}"

/-- A module argument: a plain dotted name (U3 T3 components) outside the toolchain's. -/
def libraryModule (m : String) : Bool :=
  !m.isEmpty && (m.splitOn ".").all (fun c => FvdepCore.Manifest.isComponent c.toList) &&
    !FvdepCore.Build.toolchainModule m

/-- A command's setting (tools + recipe filled in by `build` alone). -/
def envOf (root run : System.FilePath) (limits : FvdepCore.Build.CacheLimits) (bwrap : String := "")
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

/-- I1: a library pinning another toolchain is refused (interface §1). -/
def toolchainOk (lib : System.FilePath) : IO (Option String) := do
  let f := lib / "lean-toolchain"
  unless ← f.pathExists do
    return none
  let t := FvdepCore.Index.Assemble.trimText (← IO.FS.readFile f)
  if t == FvdepCore.Index.Command.toolchain then
    return none
  else
    return some s!"the library uses {t}; this fvdep checks {FvdepCore.Index.Command.toolchain}"

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

def build (lib : String) (mods : List String) : IO UInt32 := do
  let some r ← root |
    do
      say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
      return 2
  let t ←
    match ← target with
    | .ok t =>
      pure t
    | .error why =>
      IO.eprint s!"fvdep-dev: {why}\n{usage}"
      return 2
  if let some why← toolchainOk lib then
    say [s!"infra toolchain: {why}"]
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
      match ← tools r run with
      | .ok x =>
        pure x
      | .error e =>
        say [s!"infra tool_missing: {e}"]
        return 2
    let e ← envOf r run { cacheBytes := t } bwrap sys (run / "step") fp
    let built ← tryFinally (FvdepIO.Cache.build e lib mods) (unpinAll e)
    match built with
    | .error f =>
      say [s!"infra {f.code}: {f.detail}"]
      return 2
    | .ok rows =>
      say (rows.map fun x => s!"{if x.use == .built then "built" else "reused"} {x.key} {x.module}")
    -- K5 at the final unpin.
    if let .error f← evict e t then
      say [s!"infra {f.code}: {f.detail}"]
      return 2
    return 0
  finally
    try
      IO.FS.removeDirAll run
    catch ex =>
      IO.eprintln s!"fvdep-dev: the run directory {run} stayed: {ex}"

def run (args : List String) : IO UInt32 := do
  let fail : IO UInt32 := do
    IO.eprint usage
    return 2
  match args with
  | "build" :: lib :: m :: ms =>
    if (m :: ms).all libraryModule then
      build lib (m :: ms)
    else
      fail
  | ["list"] =>
    let some r ← root |
      do
        say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
        return 2
    let e ← envOf r "" {}
    say ((← list e).map fun x => s!"{x.1} {x.2.1} {x.2.2}")
    return 0
  | ["evict"] =>
    let some r ← root |
      do
        say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
        return 2
    let t ←
      match ← target with
      | .ok t =>
        pure t
      | .error why =>
        IO.eprint s!"fvdep-dev: {why}\n{usage}"
        return 2
    match ← evict (← envOf r "" { cacheBytes := t }) t with
    | .error f =>
      say [s!"infra {f.code}: {f.detail}"]
      return 2
    | .ok (n, left) =>
      say [if n == 0 && t < left then "nothing evictable" else s!"evicted {n}"]
      return 0
  | ["fingerprint"] =>
    let some r ← root |
      do
        say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
        return 2
    let tmp ← IO.FS.createTempDir
    try
      match ← preflightSysroot tmp with
      | .error e =>
        say [s!"infra tool_missing: {e}"]
        return 2
      | .ok sys =>
        match ← FvdepIO.Toolchain.fingerprint r sys with
        | .error e =>
          say [s!"infra io: {e}"]
          return 2
        | .ok fp =>
          say [s!"fingerprint {fp}"]
          return 0
    finally
      IO.FS.removeDirAll tmp
  | _ =>
    fail

end FvdepDev.Cache
