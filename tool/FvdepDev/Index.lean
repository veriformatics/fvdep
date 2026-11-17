import FvdepCore.Index.History
import FvdepIO.Index

/-! `fvdep-dev index decode <file>` (contract U4 C9; never shipped): `decodeIndex` over a file —
stdout the canonical encoding of the decoded index, exit 0; else stdout `refused: <reason>`, exit 1;
usage or an unreadable file, exit 2. `fvdep-dev index history [<dir>]` (C7 + C9; the gate driver):
the working tree's `index.json` against HEAD's + its parents' through git plumbing — silent exit 0,
else one stdout line per violation, exit 1; not a work tree, a shallow repository or an unreadable
commit → one stderr line, exit 2 (before any violation). Every message line takes the line rule
(`escapeControls`). -/

namespace FvdepDev.Index

open FvdepCore.Doc FvdepCore.Index
open FvdepIO.Index (chomp)

def usage : String := "usage: fvdep-dev index decode <file> | history [<dir>]\n"

def decodeFile (file : String) : IO UInt32 := do
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .error e =>
    IO.eprintln (escapeControls s!"fvdep-dev index: cannot read {file}: {e}")
    return 2
  | .ok bytes =>
    match decodeIndex bytes with
    | .error e =>
      IO.println (escapeControls s!"refused: {e.render}")
      return 1
    | .ok i =>
      match encodeIndex i with
      | .ok out =>
        (← IO.getStdout).write out
        return 0
      | .error e =>
        IO.eprintln
            (escapeControls s!"fvdep-dev index: an accepted index does not re-encode: {e.render}")
        return 2

/-- `git -C dir args`: (exit code, stdout bytes, stderr text); stdout drains on its own task, so a
full stderr pipe never blocks it. -/
def git (dir : String) (args : List String) : IO (UInt32 × ByteArray × String) := do
  let child ←
    IO.Process.spawn
        { cmd := "git"
          args := #["-C", dir] ++ args.toArray
          stdin := .null
          stdout := .piped
          stderr := .piped }
  let out ← IO.asTask child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  let bytes ← IO.ofExcept (← IO.wait out)
  let code ← child.wait
  return (code, bytes, err)

def text (b : ByteArray) : String := chomp (String.fromUTF8! b)

/-- The committed `index.json` at `rev`: `.error` = git cannot read the commit (its stderr). -/
def indexAt (dir rev : String) : IO (Except String (Option (Except String IndexFile))) := do
  let (c, out, err) ← git dir ["ls-tree", "--name-only", rev, "--", "index.json"]
  if c != 0 then
    return .error (chomp err)
  if out.size == 0 then
    return .ok none
  let (c, out, err) ← git dir ["cat-file", "blob", s!"{rev}:index.json"]
  if c != 0 then
    return .error (chomp err)
  return .ok <|
      some <|
      match decodeIndex out with
      | .ok i => .ok i
      | .error e => .error e.render

def historyRun (dir : String) : IO UInt32 := do
  let fail (msg : String) : IO UInt32 := do
    IO.eprintln (escapeControls msg)
    return 2
  let (c, out, _) ← git dir ["rev-parse", "--is-inside-work-tree"]
  if c != 0 || text out != "true" then
    return ← fail s!"history: not a git work tree: {dir}"
  let (c, out, err) ← git dir ["rev-parse", "--is-shallow-repository"]
  if c != 0 then
    return ← fail s!"history: cannot read HEAD: {chomp err}"
  if text out == "true" then
    return ← fail "history: shallow repository: fetch the full history"
  -- HEAD's own commit object names its parents (`HEAD^@`): an unreadable parent fails at its read.
  let (c, head, _) ← git dir ["rev-parse", "--verify", "-q", "HEAD"]
  let revs ←
    if c != 0 then
      pure []
    else
      do
        let (c, out, err) ← git dir ["rev-parse", "HEAD^@"]
        if c != 0 then
          return ← fail s!"history: cannot read HEAD: {chomp err}"
        pure (text head :: ((text out).splitOn "\n").filter (· != ""))
  let mut baselines : Array FvdepCore.Index.History.Baseline := #[]
  for rev in revs do
    match ← indexAt dir rev with
    | .error reason =>
      return ← fail s!"history: cannot read {rev}: {reason}"
    | .ok index =>
      baselines := baselines.push ⟨rev, index⟩
  let path := System.FilePath.mk dir / "index.json"
  let work ←
    if !(← path.pathExists) then
      pure (.ok none)
    else
      match ← (IO.FS.readBinFile path).toBaseIO with
      | .error e =>
        return ← fail s!"history: cannot read index.json: {e}"
      | .ok bytes =>
        pure <|
            match decodeIndex bytes with
            | .ok i => .ok (some i)
            | .error e => .error e.render
  match baselines.toList with
  | [] =>
    match work with
    | .error reason =>
      IO.println (escapeControls (FvdepCore.Index.History.Line.workingUndecodable reason).render)
      return 1
    | .ok _ =>
      return 0
  | head :: parents =>
    let lines := FvdepCore.Index.History.history work head parents
    for l in lines do
      IO.println (escapeControls l.render)
    return if lines.isEmpty then 0 else 1

def run : List String → IO UInt32
  | ["decode", file] => decodeFile file
  | ["history"] => historyRun "."
  | ["history", dir] => historyRun dir
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Index
