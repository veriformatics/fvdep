import FvdepCore.Hash.Frame
import FvdepCore.Json.Decode
import FvdepCore.Phase

/-! The step helper's output frame (contract `docs/contracts/U5-sandbox.md` R8): the helper frames
its child's status + every regular file under `/fvdep/work/out`; the supervisor reads it back here
before P5 classifies the step. Pure. -/

namespace FvdepCore.Step

open FvdepCore.Hash FvdepCore.Json FvdepCore.Phase

/-- R8's status record: the child's status + whether `/fvdep/work` / `/tmp` had no free block when
the helper sampled them after the child. -/
structure Status where
  child : Child
  workFull : Bool
  tmpFull : Bool
  deriving DecidableEq, Repr

/-- The status as a JSON object, its keys ascending (J's canonical order). -/
def Status.toJson (s : Status) : Value :=
  match s.child with
  | .exited c =>
    .obj
      [("code", .int c), ("kind", .str "exited"), ("tmpFull", .bool s.tmpFull),
        ("workFull", .bool s.workFull)]
  | .signaled n =>
    .obj
      [("kind", .str "signaled"), ("signal", .int n), ("tmpFull", .bool s.tmpFull),
        ("workFull", .bool s.workFull)]
  | .notStarted r =>
    .obj
      [("kind", .str "notStarted"), ("reason", .str r), ("tmpFull", .bool s.tmpFull),
        ("workFull", .bool s.workFull)]

/-- The status a JSON value of exactly `Status.toJson`'s form denotes, else `none`. -/
def Status.ofJson : Value → Option Status
  | .obj [("code", .int c), ("kind", .str "exited"), ("tmpFull", .bool t), ("workFull", .bool w)] =>
    if 0 ≤ c then some ⟨.exited c.toNat, w, t⟩ else none
  |
  .obj
      [("kind", .str "signaled"), ("signal", .int n), ("tmpFull", .bool t),
        ("workFull", .bool w)] =>
    if 0 ≤ n then some ⟨.signaled n.toNat, w, t⟩ else none
  |
  .obj
      [("kind", .str "notStarted"), ("reason", .str r), ("tmpFull", .bool t),
        ("workFull", .bool w)] =>
    some ⟨.notStarted r, w, t⟩
  | _ => none

/-- A path relative to a directory: nonempty, `/`-separated components, each nonempty and never `.`
or `..`; no NUL. -/
def safePath (p : String) : Bool :=
  p != "" && !p.contains '\x00' && (p.splitOn "/").all fun c => c != "" && c != "." && c != ".."

/-- What the supervisor reads from a step's frame. -/
structure Output where
  status : Status
  files : List (String × ByteArray)

/-- R8: the helper's frame of `s` + `files` (paths relative to `/fvdep/work/out`): tag
`fvdep/step/1`, the status at the empty path (H3's non-file entry: it sorts first), then the files
in path order. -/
def frameOf (s : Status) (files : List (String × ByteArray)) : ByteArray :=
  frame Tag.step.spelling (("", print s.toJson) :: sortByPath files)

/-- R8: the status + files of a frame `frameOf` makes, else `none`: the tag, a status entry whose
bytes are its status's canonical JSON (another text of the same value is refused), safe file
paths. -/
def read (b : ByteArray) : Option Output := do
  let (tag, entries) ← unframe b
  match entries with
  | ("", sb) :: files =>
    let v ← (decode sb).toOption
    let s ← Status.ofJson v
    if tag == Tag.step.spelling && sb.data == (print s.toJson).data && files.all (safePath ·.1) then
      some ⟨s, files⟩
    else
      none
  | _ =>
    none

end FvdepCore.Step
