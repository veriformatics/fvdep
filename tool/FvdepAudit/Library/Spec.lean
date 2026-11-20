import FvdepAudit.Doc.Spec
import FvdepAudit.Hash.Spec
import FvdepCore.Library
import FvdepCore.Project

/-! Specs for project selection + library snapshots (contract `docs/contracts/U5b-oracle.md`
P3, L1, L4–L7), written from the contract apart from `FvdepCore.Project` + `FvdepCore.Library`:
git's two machine layouts (L4), the tree policy (L4), the head record (L5), the selection tables
(P3, L6). -/

namespace FvdepAudit.Library.Spec

open FvdepCore.Json FvdepCore.Library FvdepCore.Project FvdepAudit.Hash.Spec

/-- ASCII text as bytes. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- A canonical decimal (no leading zero) as bytes. -/
def decimalBytes (n : Nat) : List UInt8 := ascii (String.ofList (FvdepCore.Ids.decimal n))

/-! ## L4 git's machine layouts -/

def kindName : ObjKind → List UInt8
  | .blob => ascii "blob"
  | .tree => ascii "tree"
  | .commit => ascii "commit"

/-- `ls-tree -l`'s size column: printf `%7s` of a blob's size, `-` for other types. -/
def sizeColumn (size : Option Nat) : List UInt8 :=
  let t :=
    match size with
    | some n => decimalBytes n
    | none => ascii "-"
  List.replicate (7 - t.length) 32 ++ t

/-- L4: one `ls-tree -z -l` record: `mode SP type SP object SP size TAB path`. -/
def recordLayout (e : TreeEntry) : List UInt8 :=
  e.mode ++ [32] ++ kindName e.kind ++ [32] ++ e.oid ++ [32] ++ sizeColumn e.size ++ [9] ++
    utf8 e.path

/-- L4: a whole listing: each record NUL-terminated. -/
def listing (es : List TreeEntry) : List UInt8 := (es.map fun e => recordLayout e ++ [0]).flatten

/-- L4: a record git prints: a 6-digit octal mode, a 40-digit lowercase hex object name, a size
exactly for a blob, a nonempty path without NUL. -/
def EntryWF (e : TreeEntry) : Prop :=
  e.mode.length = 6 ∧
    (∀ b ∈ e.mode, 48 ≤ b ∧ b ≤ 55) ∧
    e.oid.length = 40 ∧
    (∀ b ∈ e.oid, 48 ≤ b ∧ b ≤ 57 ∨ 97 ≤ b ∧ b ≤ 102) ∧
    (e.kind = .blob ↔ e.size.isSome) ∧ utf8 e.path ≠ [] ∧ 0 ∉ utf8 e.path

/-- L4: `cat-file --batch -Z`'s reply to one blob: `object SP blob SP size NUL`, the content,
NUL. -/
def replyLayout (x : Blob) (c : ByteArray) : List UInt8 :=
  x.oid ++ ascii " blob " ++ decimalBytes x.size ++ [0] ++ c.data.toList ++ [0]

/-- L4: the replies to the planned blobs, in order. -/
def batchLayout (plan : List Blob) (cs : List ByteArray) : List UInt8 :=
  ((plan.zip cs).map fun p => replyLayout p.1 p.2).flatten

/-! ## L4 the tree policy -/

def components (p : String) : List String := p.splitOn "/"

/-- L4: a plain path: nonempty, no NUL, every component nonempty + not starting with `.`, within
the path caps. -/
def PathOk (caps : Caps) (p : String) : Prop :=
  p ≠ "" ∧
    '\x00' ∉ p.toList ∧
    (∀ c ∈ components p, c ≠ "" ∧ c.toList.head? ≠ some '.') ∧
    p.utf8ByteSize ≤ caps.pathBytes ∧ (components p).length ≤ caps.depth

/-- L4: a directory = `040000 tree`; a file = `100644`/`100755 blob`. -/
def IsDir (e : TreeEntry) : Prop := e.kind = .tree ∧ e.mode = ascii "040000"

def IsFile (e : TreeEntry) : Prop :=
  e.kind = .blob ∧ (e.mode = ascii "100644" ∨ e.mode = ascii "100755")

/-- L4: the library's roots + the files a library must hold. -/
def rootDirsSpec : List String := ["Fvdep", "FvdepPreview", "FvdepProofs"]

def rootFilesSpec : List String :=
  ["lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "FvdepPreview.lean",
    "FvdepProofs.lean"]

def requiredSpec : List String :=
  ["lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "Fvdep/Registry.lean"]

/-- L4: an entry where the policy allows it: a root directory or root file of its kind, or a
directory or file inside a root directory. -/
def Placed (e : TreeEntry) : Prop :=
  match components e.path with
  | [r] => r ∈ rootDirsSpec ∧ IsDir e ∨ r ∈ rootFilesSpec ∧ IsFile e
  | r :: _ :: _ => r ∈ rootDirsSpec ∧ (IsDir e ∨ IsFile e)
  | [] => False

/-- A blob's listed size (0 for other entries). -/
def blobSize (e : TreeEntry) : Nat := if e.kind = .blob then e.size.getD 0 else 0

/-- L4: the whole listing allowed: every entry plain + placed + within the per-file cap; the
entry count, the path bytes + the blob bytes within their caps; every required file a blob. -/
def Policy (caps : Caps) (es : List TreeEntry) : Prop :=
  (∀ e ∈ es, PathOk caps e.path ∧ Placed e ∧ blobSize e ≤ caps.fileBytes) ∧
    es.length ≤ caps.entries ∧
    (es.map fun e => e.path.utf8ByteSize).sum ≤ caps.pathTotal ∧
    (es.map blobSize).sum ≤ caps.totalBytes ∧
    ∀ p ∈ requiredSpec, ∃ e ∈ es, e.kind = .blob ∧ e.path = p

/-- L4: the plan = the blobs (path, object, size), in listing order. -/
def blobsOf (es : List TreeEntry) : List Blob :=
  es.filterMap fun e => if e.kind = .blob then some ⟨e.path, e.oid, e.size.getD 0⟩ else none

/-! ## L5 the head record -/

/-- L5: `head.json`'s value: exactly `commit`, `fetched`, `schema` 1, `source`, in key order. -/
def headLayout (h : Head) : Value :=
  .obj
    [("commit", .str h.commit), ("fetched", .str h.fetched), ("schema", .int 1),
      ("source", .str h.source)]

def headBytes (h : Head) : ByteArray := (print (headLayout h)).push 0x0A

/-- L5: a commit (40 lowercase hex), a UTC time, a source key (64 lowercase hex). -/
def HeadWF (h : Head) : Prop :=
  (∃ c : FvdepCore.Ids.Commit, h.commit = toString c) ∧
    FvdepAudit.Doc.Spec.UtcText h.fetched ∧ FvdepAudit.Doc.Spec.DigestText h.source

/-! ## P3 + L6 the tables (refusal + notice texts = tested presentation, outside the claims) -/

/-- P3's outcome with the refusal text erased. -/
inductive Pick where
  | none
  | project (dir : String)
  | refuse
  deriving DecidableEq, Repr

def pick : Choice → Pick
  | .none => .none
  | .project d => .project d
  | .refuse _ => .refuse

/-- P3: `--project` decides alone (its manifest a regular file, else refused); else the nearest
candidate holding a manifest decides (a regular file → its directory, a link or special file →
refused); no candidate holding one → no project. -/
inductive ProjectSpec : Seen → Pick → Prop
  | explicit (d : String) : ProjectSpec (.explicit d .file) (.project d)
  | explicitNot (d : String) (f : Found) : f ≠ .file → ProjectSpec (.explicit d f) .refuse
  |
  nearest (pre : List (String × Found)) (d : String) (rest : List (String × Found)) :
    (∀ x ∈ pre, x.2 = .absent) → ProjectSpec (.ancestors (pre ++ (d, .file) :: rest)) (.project d)
  |
  nearestIrregular (pre : List (String × Found)) (d : String) (f : Found)
    (rest : List (String × Found)) :
    (∀ x ∈ pre, x.2 = .absent) →
      f = .link ∨ f = .special → ProjectSpec (.ancestors (pre ++ (d, f) :: rest)) .refuse
  |
  none (ds : List (String × Found)) : (∀ x ∈ ds, x.2 = .absent) → ProjectSpec (.ancestors ds) .none

/-- L6 before a fetch: a project's pin whose tree is published → served; a pin without → its
fetch; no project → the head's fetch. -/
inductive StartSpec : Option String → Bool → Start → Prop
  | published (pin : String) : StartSpec (some pin) true (.serve pin)
  | pin (pin : String) : StartSpec (some pin) false (.fetchPin pin)
  | head (published : Bool) : StartSpec none published .fetchHead

/-- L6's outcome with the texts erased: the served commit + whether a notice goes to stderr, or a
refusal. -/
inductive Verdict where
  | serve (commit : String) (notice : Bool)
  | refuse
  deriving DecidableEq, Repr

def verdict : Selected → Verdict
  | .serve c n => .serve c n.isSome
  | .refuse _ => .refuse

/-- L6 after a pin fetch: its tree; any failure refuses (a pin never falls back). -/
inductive PinSpec (pin : String) : Fetch → Verdict → Prop
  | ok (c : String) : PinSpec pin (.ok c) (.serve pin false)
  | failed (f : Fetch) : (∀ c, f ≠ .ok c) → PinSpec pin f .refuse

/-- L6 after a head fetch: its tree; a transport failure → the last fetched head + a notice (no
record → refused; a damaged record = a store fault, refused); every other failure refuses, no
fallback. -/
inductive HeadSpec : HeadState → Fetch → Verdict → Prop
  | ok (s : HeadState) (c : String) : HeadSpec s (.ok c) (.serve c false)
  | fallback (h : Head) (r : String) : HeadSpec (.valid h) (.transport r) (.serve h.commit true)
  | never (r : String) : HeadSpec .absent (.transport r) .refuse
  | damaged (why r : String) : HeadSpec (.damaged why) (.transport r) .refuse
  |
  other (s : HeadState) (f : Fetch) :
    (∀ c, f ≠ .ok c) → (∀ r, f ≠ .transport r) → HeadSpec s f .refuse

end FvdepAudit.Library.Spec
