/-! Project selection, the pure part (contract `docs/contracts/U5b-oracle.md` P1–P3; U8 reuses
it): `--project <dir>`, else the nearest ancestor of the working directory holding `fvdep.toml`.
The residue observes each candidate's `fvdep.toml` with `lstat` (never followed); the manifest
read + validation = U3's reader. -/

namespace FvdepCore.Project

/-- P1: what a directory's `fvdep.toml` is (`lstat`: a link is never followed). -/
inductive Found where
  | absent
  | file
  | link
  | special
  deriving DecidableEq, Repr

/-- P1: the observation — `--project <dir>` with its manifest's kind, or the working directory's
ancestors nearest first, each with its manifest's kind. -/
inductive Seen where
  | explicit (dir : String) (found : Found)
  | ancestors (dirs : List (String × Found))
  deriving DecidableEq, Repr

/-- P1 + P3: no project, a project directory, or a refusal (exit 2). -/
inductive Choice where
  | none
  | project (dir : String)
  | refuse (reason : String)
  deriving DecidableEq, Repr

/-- A manifest found where a regular file must be: its refusal. -/
def irregular (dir : String) : Found → String
  | .link => s!"infra io: {dir}/fvdep.toml is a link (never followed)"
  | _ => s!"infra io: {dir}/fvdep.toml is not a regular file (special file)"

/-- P3: `--project` → that directory (its manifest absent, a link or special = refused); else the
first ancestor holding a manifest: a regular file → its directory, anything else → refused; none →
no project. -/
def selectProject : Seen → Choice
  | .explicit d .file => .project d
  | .explicit d .absent => .refuse s!"No fvdep.toml found in {d}."
  | .explicit d f => .refuse (irregular d f)
  | .ancestors ds =>
    match ds.find? (·.2 != .absent) with
    | none => .none
    | some (d, .file) => .project d
    | some (d, f) => .refuse (irregular d f)

end FvdepCore.Project
