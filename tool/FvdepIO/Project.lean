import FvdepCore.Project
import FvdepIO.Sys
import FvdepIO.Toml

/-! Project selection, the residue (contract `docs/contracts/U5b-oracle.md` P1–P2; ledger residue
`library-store`'s filesystem reads): each candidate's `fvdep.toml` observed with `lstat` (never
followed, never opened), then the chosen manifest read through U3's reader. The decision =
`FvdepCore.Project.selectProject`. -/

namespace FvdepIO.Project

open FvdepCore.Project

/-- P1: what `dir/fvdep.toml` is by `lstat`: a regular file, a link, anything else = special; a
failed `lstat` (absent, an unreachable directory) = absent. -/
def found (dir : System.FilePath) : IO Found :=
  tryCatch
    (do
      match (← (dir / "fvdep.toml").symlinkMetadata).type with
      | .file =>
        return .file
      | .symlink =>
        return .link
      | _ =>
        return .special)
    fun _ => pure .absent

/-- `d` and each of its ancestors, nearest first. -/
partial def ancestors (d : System.FilePath) : List System.FilePath :=
  match d.parent with
  | some p => if p == d then [d] else d :: ancestors p
  | none => [d]

/-- P1's observation: `--project <dir>` (its manifest's kind) or the working directory's
ancestors, nearest first, each with its manifest's kind. -/
def observe (explicit : Option String) : IO Seen := do
  match explicit with
  | some d =>
    return .explicit d (← found d)
  | none =>
    return .ancestors (← (ancestors (← IO.currentDir)).mapM fun d => return (d.toString, ← found d))

/-- A manifest refusal: U3's public code + detail, naming the file. -/
def refusal (file : String) (e : FvdepIO.Toml.ReadError) : String :=
  s!"infra {e.code.spelling}: {file}: {e.detail}"

/-- P2: the chosen project's pin: its `fvdep.toml` read (at most `maxBytes` + 1 bytes: a larger one
is refused like the text stage's `too_large`), then U3's reader (text stage, Lake's parse,
`validate`) → `[library] commit`, or the refusal (exit 2). -/
def pin (dir : String) : IO (Except String String) := do
  let file := s!"{dir}/fvdep.toml"
  match FvdepIO.Sys.Path.ofString? dir, FvdepIO.Sys.Name.ofString? "fvdep.toml" with
  | some p, some n =>
    match ← FvdepIO.Sys.readFile p n (FvdepCore.Manifest.maxBytes + 1) with
    | .ok (some b) =>
      match ← FvdepIO.Toml.readManifest b with
      | .ok m =>
        return .ok (toString m.library)
      | .error e =>
        return .error (refusal file e)
    | .ok none =>
      return .error s!"No fvdep.toml found in {dir}."
    | .error e =>
      if e.cause matches .tooLarge then
        return .error (refusal file (.text .tooLarge))
      return .error s!"infra io: {file} could not be read: {e.reason}"
  | _, _ =>
    return .error s!"infra io: {file}: a path with NUL"

end FvdepIO.Project
