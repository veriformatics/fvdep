import FvdepCore.Hash.Frame
import FvdepCore.Index.Statuses

/-! `index.json`'s value (contract `docs/contracts/U4-library.md` C6) from a validated registry: the
registry strings, each entry's statuses + digest (C4: `h` over the H3 `fvdep/entry/1` frame of its
closure files; IO = SHA-256 hex), operations in C6's (id, version) order, notices + removed records
in registry order, the trimmed `lean-toolchain` text; C9's warnings beside it in `modules` order.
C8 `AssembleExact` states it against the layout written apart (`FvdepAudit.Index.Assemble`). -/

namespace FvdepCore.Index.Assemble

open Lean FvdepCore.Json FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses

/-- C4: the bytes an entry's digest hashes (H3 `fvdep/entry/1` over its closure's files). -/
def entryFrame (F : Facts) (M : Name) : ByteArray :=
  FvdepCore.Hash.frame FvdepCore.Hash.Tag.entry.spelling (closureFiles F M)

/-- C6: an obligation's `name` = its constant's last component (V4: `S.<name>`). -/
def lastName : Name → String
  | .str _ s => s
  | n => toString n

def namesValue (xs : List String) : Value := .arr (xs.map .str)

def obligationValue (x : Name × FvdepCore.Index.Status × List String) : Value :=
  .obj [("axioms", namesValue x.2.2), ("name", .str (lastName x.1)), ("status", .str x.2.1.text)]

def compatValue : Option (String × FvdepCore.Index.Status × List String) → Value
  | some x =>
    .obj [("axioms", namesValue x.2.2), ("status", .str x.2.1.text), ("version", .str x.1)]
  | none => .null

def operationValue (h : ByteArray → String) (F : Facts) (x : Entry × EntryStatus) : Value :=
  .obj
    [("compat", compatValue x.2.compat), ("digest", .str (h (entryFrame F x.1.module))),
      ("id", .str x.1.id), ("obligations", .arr (x.2.obligations.map obligationValue)),
      ("version", .str x.1.version)]

def noticeValue (n : Registry.Notice) : Value :=
  .obj
    [("id", .str n.id), ("reason", .str n.reason),
      ("replacement",
        match n.replacement with
        | some r => .str r
        | none => .null),
      ("version", .str n.version)]

def kindText : Registry.Kind → String
  | .operation => "operation"
  | .profile => "profile"

def removedValue (r : Registry.Removed) : Value :=
  .obj
    [("digest", .str r.digest), ("id", .str r.id), ("kind", .str (kindText r.kind)),
      ("last_commit", .str r.lastCommit), ("toolchain", .str r.toolchain),
      ("version", .str r.version)]

/-- C6: the `lean-toolchain` text without its leading + trailing whitespace
(`Char.isWhitespace`). -/
def trimText (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- An entry's place in C6's order: its id, then its version (an unparseable version keys as
`0.0.0`; `validate` excludes it). -/
def opKey (e : Entry) : String × EntryVersion :=
  (e.id, (EntryVersion.parse e.version).getD ⟨0, 0, 0⟩)

/-- The keys' order: the id's string order (code point = UTF-8 byte order), then the version
numerically — total on every input, so the sort's order laws hold everywhere. -/
def keyLe (a b : String × EntryVersion) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && a.2.cmp b.2 != .gt)

/-- The entries in C6's operation order. -/
def sortOps (rs : List (Entry × EntryStatus)) : List (Entry × EntryStatus) :=
  rs.mergeSort fun a b => keyLe (opKey a.1) (opKey b.1)

/-- C6's value: notices, operations (sorted), removed records, schema 1, the toolchain. -/
def indexValue (toolchain : String) (h : ByteArray → String) (F : Facts) (l : Lists)
    (rs : List (Entry × EntryStatus)) : Value :=
  .obj
    [("notices", .arr (l.notices.map noticeValue)),
      ("operations", .arr ((sortOps rs).map (operationValue h F))),
      ("removed", .arr (l.removed.map removedValue)), ("schema", .int 1),
      ("toolchain", .str (trimText toolchain))]

/-- The index value + C9's warnings in `modules` order, from the raw `lean-toolchain` text; a
theorem without an observed axiom list refuses as load (`statuses`). -/
def assemble (F : Facts) (ax : List (Name × List Name)) (l : Lists) (toolchain : String)
    (h : ByteArray → String) : Except Found (Value × List Warning) :=
  (statuses F ax l).map fun rs => (indexValue toolchain h F l rs, rs.flatMap (·.2.warnings))

end FvdepCore.Index.Assemble
