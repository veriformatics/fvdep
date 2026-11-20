import FvdepCore.Export
import FvdepIO.Toolchain

/-! `fvdep-dev export read <file> [<constant>]` (contract U5b X; never shipped): one `leanexport`
output through `FvdepCore.Export.read` against fvdep's own Lean (version + githash) → the
declaration count, + the named declaration's kind, value presence + type; a refusal → its line,
class + reason, exit 1. -/

namespace FvdepDev.Export

def usage : String := "usage: fvdep-dev export read <file> [<constant>]\n"

def run : List String → IO UInt32
  | "read" :: file :: rest => do
    let b ← IO.FS.readBinFile file
    match FvdepCore.Export.read Lean.githash Lean.versionString b with
    | .error r =>
      IO.println s!"refused line {r.line} {repr r.cls}: {r.reason}"
      return 1
    | .ok ds =>
      IO.println s!"decls {ds.length}"
      if let [c] := rest then
        match ds.find? (·.name == c.toName) with
        | some d =>
          IO.println s!"{d.name} {repr d.kind} value={d.value.isSome} type {d.type}"
        | none =>
          IO.println s!"{c} absent"
      return 0
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Export
