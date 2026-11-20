import FvdepCore.Library
import FvdepDev.Cache
import FvdepIO.Library
import FvdepIO.Project

/-! `fvdep-dev library tree|plan <file>` (contract U5b L4; never shipped): a saved `git ls-tree
-r -t -l -z` output through `FvdepCore.Library.parseTree` → one line per entry (mode, type, object,
size, path), or through `planTree` (default caps) → one line per planned blob + the count;
`library batch <tree> <replies>` → the planned blobs' `cat-file --batch -Z` replies through
`parseBatch` → their count + bytes; a refusal → its reason, exit 1. `library killgroup self|<n>` →
`FvdepIO.Git.killGroup` with signal 0 (`ok` | `refused <errno>`). `library fetch [--project <dir>]
[--limit <name>=<n>]…` (P + L2–L7 through the residue, the source = `FVDEP_LIBRARY_URL`, the cache
root = `FVDEP_CACHE`) → stdout `served <commit>`, a notice on stderr, exit 0; a refusal → stderr,
exit 2 (every line through §1's line rule). -/

namespace FvdepDev.Library

open FvdepCore.Library

def usage : String :=
  "usage: fvdep-dev library (tree|plan) <file> | library batch <tree> <replies>\n" ++
    "       fvdep-dev library fetch [--project <dir>] [--limit <name>=<n>]...\n" ++
    "       fvdep-dev library killgroup self|<n>\n"

def bytesText (bs : List UInt8) : String := String.ofList (bs.map charOf)

def say (lines : List String) : IO Unit := do
  for l in lines do
    IO.eprintln (FvdepCore.Doc.escapeControls l)

/-- `fetch`'s options: `--project <dir>`, `--limit <name>=<n>` (a library limit). -/
def options : List String → Option String → Limits → Option (Option String × Limits)
  | [], p, l => some (p, l)
  | "--project" :: d :: rest, none, l => options rest (some d) l
  | "--limit" :: kv :: rest, p, l =>
    match kv.splitOn "=" with
    | [k, v] => v.toNat?.bind (l.set k) |>.bind (options rest p)
    | _ => none
  | _, _, _ => none

/-- P (project → pin) → L (the snapshot) → L7 (the served tree's toolchain). -/
def fetch (args : List String) : IO UInt32 := do
  let some (explicit, limits) := options args none {}
    |
    do
      IO.eprint usage
      return 2
  let pin ←
    match FvdepCore.Project.selectProject (← FvdepIO.Project.observe explicit) with
    | .none =>
      pure none
    | .refuse r =>
      say [r]
      return 2
    | .project d =>
      match ← FvdepIO.Project.pin d with
      | .ok p =>
        pure (some p)
      | .error r =>
        say [r]
        return 2
  let some cache ← FvdepDev.Cache.root |
    do
      say ["infra io: no cache directory (FVDEP_CACHE, XDG_CACHE_HOME + HOME unset)"]
      return 2
  let source := anchor (← IO.currentDir).toString (sourceOf (← IO.getEnv "FVDEP_LIBRARY_URL"))
  match ← FvdepIO.Library.snapshot (← FvdepIO.Library.Store.of cache source limits) pin with
  | .error r =>
    say [r]
    return 2
  | .ok s =>
    if let some n := s.notice then
      say [n]
    let theirs :=
      FvdepCore.Index.Command.textOfBytes (← IO.FS.readBinFile (s.tree / "lean-toolchain"))
    if let some r := toolchainRefusal s.commit theirs FvdepCore.Index.Command.toolchain then
      say [r]
      return 2
    IO.println s!"served {s.commit}"
    return 0

/-- This process's group id (`/proc/self/stat`'s fifth field). -/
def ownGroup : IO Nat := do
  let stat ← IO.FS.readFile "/proc/self/stat"
  return (((stat.splitOn ") ").getLastD "").splitOn " ").getD 2 "" |>.toNat?.getD 0

def run : List String → IO UInt32
  | "fetch" :: args => fetch args
  | ["killgroup", g] => do
    let n ←
      if g == "self" then
        ownGroup
      else
        pure (g.toNat?.getD 0)
    match ← FvdepIO.Git.killGroup n.toUInt32 0 with
    | .ok () =>
      IO.println "ok"
    | .error e =>
      IO.println s!"refused {e}"
    return 0
  | ["batch", tree, replies] => do
    let some es := parseTree (← IO.FS.readBinFile tree) |
      do
        IO.println "refused: not an ls-tree -z -l listing"
        return 1
    let .ok plan := planTree {} es |
      do
        IO.println "refused: the listing's plan"
        return 1
    match parseBatch plan (← IO.FS.readBinFile replies) with
    | none =>
      IO.println "refused: not the planned batch replies"
      return 1
    | some cs =>
      IO.println s!"blobs {cs.length} bytes {cs.foldl (· + ·.size) 0}"
      return 0
  | [cmd, file] => do
    let b ← IO.FS.readBinFile file
    match parseTree b, cmd with
    | none, _ =>
      IO.println "refused: not an ls-tree -z -l listing"
      return 1
    | some es, "tree" =>
      for e in es do
        let size :=
          match e.size with
          | some n => toString n
          | none => "-"
        IO.println s!"{bytesText e.mode} {repr e.kind} {bytesText e.oid} {size} {e.path}"
      IO.println s!"entries {es.length}"
      return 0
    | some es, "plan" =>
      match planTree {} es with
      | .error why =>
        IO.println s!"refused: the library snapshot {why}"
        return 1
      | .ok bs =>
        for x in bs do
          IO.println s!"{x.path} {bytesText x.oid} {x.size}"
        IO.println s!"blobs {bs.length}"
        return 0
    | _, _ =>
      do
        IO.eprint usage
        return 2
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Library
