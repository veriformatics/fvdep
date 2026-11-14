import FvdepCore.Doc

/-! `index.json` schema 1 (contract `docs/contracts/U4-library.md` C6): the index record, its
canonical JSON, the D5 schema data `indexTy`, the relational clauses (C3 V8 + V9 over the document),
`encodeIndex` (refuses an out-of-domain value, never clips) + `decodeIndex`. -/

namespace FvdepCore.Index

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc

/-- C5: an obligation's or a compat edge's status. -/
inductive Status where
  | proven
  | «open»
  | trusts
  deriving DecidableEq, Repr

def Status.text : Status → String
  | .proven => "proven"
  | .«open» => "open"
  | .trusts => "trusts"

/-- An obligation: its constant's last component, status + the axioms beyond the standard three
(full names, byte order). -/
structure Obligation where
  name : String
  status : Status
  axioms : List String
  deriving DecidableEq, Repr

/-- A compat edge: the older version this spec equals + the status of its proof. -/
structure Compat where
  version : EntryVersion
  status : Status
  axioms : List String
  deriving DecidableEq, Repr

structure Operation where
  id : ModuleId
  version : EntryVersion
  digest : String
  obligations : List Obligation
  compat : Option Compat
  deriving DecidableEq, Repr

structure Notice where
  id : ModuleId
  version : EntryVersion
  reason : String
  replacement : Option EntryVersion
  deriving DecidableEq, Repr

/-- A removed-entry record (kind `operation`: schema 1 has no profiles). -/
structure Removed where
  id : ModuleId
  version : EntryVersion
  digest : String
  lastCommit : Commit
  toolchain : String
  deriving DecidableEq

structure IndexFile where
  toolchain : String
  operations : List Operation
  notices : List Notice
  removed : List Removed
  deriving DecidableEq

/-! ## Schema data (D5) -/

def labelTy : Ty := .scalar [.str] .label

/-- An obligation's axioms under each status (C6 status consistency). -/
def axiomsTy : Ty :=
  .byTag
    [("open", .arr [.arr] labelTy labelTy (.ascendingHas "sorryAx")),
      ("proven", .arr [.arr] labelTy labelTy .empty),
      ("trusts", .arr [.arr] labelTy labelTy (.ascendingWithout "sorryAx"))]

def obligationTy : Ty :=
  .obj (some (.str "status" ["open", "proven", "trusts"])) [("axioms", axiomsTy), ("name", labelTy)]

def operationTy : Ty :=
  .obj none
    [("compat", .scalar [.null, .obj] .compat), ("digest", .scalar [.str] .digest),
      ("id", .scalar [.str] .moduleId),
      ("obligations", .arr [.arr] obligationTy obligationTy (.unique ["name"])),
      ("version", .scalar [.str] .version)]

def noticeTy : Ty :=
  .obj none
    [("id", .scalar [.str] .moduleId), ("reason", .scalar [.str] .reason),
      ("replacement", .scalar [.null, .str] .versionOrNull), ("version", .scalar [.str] .version)]

def removedTy : Ty :=
  .obj none
    [("digest", .scalar [.str] .digest), ("id", .scalar [.str] .moduleId),
      ("kind", .scalar [.str] (.oneOf ["operation"])), ("last_commit", .scalar [.str] .commit),
      ("toolchain", labelTy), ("version", .scalar [.str] .version)]

/-- C6: the index root; `schema` = 1 is its discriminator. -/
def indexTy : Ty :=
  .obj (some (.int "schema" 1))
    [("notices", .arr [.arr] noticeTy noticeTy .any),
      ("operations", .arr [.arr] operationTy operationTy .idVersion),
      ("removed", .arr [.arr] removedTy removedTy .any), ("toolchain", labelTy)]

/-! ## Encoding (C6 layout; members in key order) -/

def strsJson (xs : List String) : Value := .arr (xs.map .str)

def Obligation.toJson (o : Obligation) : Value :=
  .obj [("axioms", strsJson o.axioms), ("name", .str o.name), ("status", .str o.status.text)]

def Compat.toJson (c : Compat) : Value :=
  .obj
    [("axioms", strsJson c.axioms), ("status", .str c.status.text),
      ("version", .str (toString c.version))]

def Operation.toJson (o : Operation) : Value :=
  .obj
    [("compat",
        match o.compat with
        | some c => c.toJson
        | none => .null),
      ("digest", .str o.digest), ("id", .str (toString o.id)),
      ("obligations", .arr (o.obligations.map Obligation.toJson)),
      ("version", .str (toString o.version))]

def Notice.toJson (n : Notice) : Value :=
  .obj
    [("id", .str (toString n.id)), ("reason", .str n.reason),
      ("replacement",
        match n.replacement with
        | some v => .str (toString v)
        | none => .null),
      ("version", .str (toString n.version))]

def Removed.toJson (r : Removed) : Value :=
  .obj
    [("digest", .str r.digest), ("id", .str (toString r.id)), ("kind", .str "operation"),
      ("last_commit", .str (toString r.lastCommit)), ("toolchain", .str r.toolchain),
      ("version", .str (toString r.version))]

def IndexFile.toJson (i : IndexFile) : Value :=
  .obj
    [("notices", .arr (i.notices.map Notice.toJson)),
      ("operations", .arr (i.operations.map Operation.toJson)),
      ("removed", .arr (i.removed.map Removed.toJson)), ("schema", .int 1),
      ("toolchain", .str i.toolchain)]

/-! ## Extraction (total: a value the walk accepts never reaches a fallback) -/

def statusOf (s : String) : Status :=
  if s = "proven" then .proven else if s = "trusts" then .trusts else .«open»

def strsAt (o : Option Value) : List String :=
  match o with
  | some (.arr xs) => (strsOf xs).getD []
  | _ => []

def versionAt (o : Option Value) : EntryVersion := (EntryVersion.parse (textOf o)).getD ⟨0, 0, 0⟩

def moduleAt (o : Option Value) : ModuleId := (ModuleId.parse (textOf o)).getD defaultModule

def obligationOfValue (v : Value) : Obligation :=
  let ms := membersOf (some v)
  ⟨textOf (member? ms "name"), statusOf (textOf (member? ms "status")),
    strsAt (member? ms "axioms")⟩

def compatOfValue : Option Value → Option Compat
  | some (.obj ms) =>
    some
      ⟨versionAt (member? ms "version"), statusOf (textOf (member? ms "status")),
        strsAt (member? ms "axioms")⟩
  | _ => none

def operationOfValue (v : Value) : Operation :=
  let ms := membersOf (some v)
  { id := moduleAt (member? ms "id")
    version := versionAt (member? ms "version")
    digest := textOf (member? ms "digest")
    obligations :=
      match member? ms "obligations" with
      | some (.arr xs) => xs.map obligationOfValue
      | _ => []
    compat := compatOfValue (member? ms "compat") }

def noticeOfValue (v : Value) : Notice :=
  let ms := membersOf (some v)
  { id := moduleAt (member? ms "id")
    version := versionAt (member? ms "version")
    reason := textOf (member? ms "reason")
    replacement := (textOpt (member? ms "replacement")).bind EntryVersion.parse }

def removedOfValue (v : Value) : Removed :=
  let ms := membersOf (some v)
  { id := moduleAt (member? ms "id")
    version := versionAt (member? ms "version")
    digest := textOf (member? ms "digest")
    lastCommit := (Commit.parse (textOf (member? ms "last_commit"))).getD defaultCommit
    toolchain := textOf (member? ms "toolchain") }

def arrAt (o : Option Value) :
    List Value := match o with
  | some (.arr xs) => xs
  | _ => []

def indexOfValue (v : Value) : IndexFile :=
  let ms := membersOf (some v)
  { toolchain := textOf (member? ms "toolchain")
    operations := (arrAt (member? ms "operations")).map operationOfValue
    notices := (arrAt (member? ms "notices")).map noticeOfValue
    removed := (arrAt (member? ms "removed")).map removedOfValue }

/-! ## Relational clauses (C3 V8 + V9 over the document) -/

/-- The (id, version) pairs the index lists as operations or removed records. -/
def known (i : IndexFile) : List (ModuleId × EntryVersion) :=
  i.operations.map (fun o => (o.id, o.version)) ++ i.removed.map fun r => (r.id, r.version)

/-- V8: a notice names a listed or removed entry; its replacement, another version of that id. -/
def noticeOk (i : IndexFile) (n : Notice) : Bool :=
  (known i).contains (n.id, n.version) &&
    match n.replacement with
    | some v => v != n.version && (known i).contains (n.id, v)
    | none => true

/-- V9: a removed record is not listed, not recorded earlier, and some notice names it. -/
def removedOk (i : IndexFile) (earlier : List Removed) (r : Removed) : Bool :=
  !(i.operations.any fun o => o.id == r.id && o.version == r.version) &&
    !(earlier.any fun e => e.id == r.id && e.version == r.version) &&
    i.notices.any fun n => n.id == r.id && n.version == r.version

def firstNotice (i : IndexFile) : Nat → List Notice → Option DocError
  | _, [] => none
  | k, n :: ns =>
    if noticeOk i n then firstNotice i (k + 1) ns
    else some ⟨[.key "notices", .index k], .badValue, some n.toJson⟩

def firstRemoved (i : IndexFile) : Nat → List Removed → List Removed → Option DocError
  | _, _, [] => none
  | k, earlier, r :: rs =>
    if removedOk i earlier r then firstRemoved i (k + 1) (earlier ++ [r]) rs
    else some ⟨[.key "removed", .index k], .badValue, some r.toJson⟩

/-- The first relational violation: notices in order, then removed records in order. -/
def relational (i : IndexFile) : Option DocError :=
  (firstNotice i 0 i.notices).orElse fun _ => firstRemoved i 0 [] i.removed

/-! ## Decoding + encoding -/

/-- C6: the index a value denotes, else the walk's first violation, else the first relational one.
-/
def IndexFile.ofJson (v : Value) : Except DocError IndexFile :=
  match walk "" indexTy [] v with
  | some e => .error e
  | none =>
    match relational (indexOfValue v) with
    | some e => .error e
    | none => .ok (indexOfValue v)

/-- C6 `IndexWellFormed` as a check. -/
def IndexFile.wellFormed (i : IndexFile) : Bool :=
  (walk "" indexTy [] i.toJson).isNone && (relational i).isNone

/-- Why `index.json`'s bytes are refused: the text (J3) or the document. -/
inductive IndexError where
  | text (e : DecodeError)
  | doc (e : DocError)
  deriving Repr, BEq

def IndexError.render : IndexError → String
  | .text .malformed => "malformed"
  | .text .tooLarge => "too_large"
  | .text (.duplicateKey (p, k)) => "duplicate_key " ++ pointer (p ++ [.key k])
  | .doc e => e.render

/-- C6: the canonical bytes (J4 text + LF) of a well-formed index; anything else is refused with its
first violation (the walk's, else the first relational one), never clipped. -/
def encodeIndex (i : IndexFile) : Except DocError ByteArray :=
  match walk "" indexTy [] i.toJson with
  | some e => .error e
  | none =>
    match relational i with
    | some e => .error e
    | none => .ok ((print i.toJson).push 0x0A)

/-- The bytes without one final LF (C6's text = canonical JSON + LF): one byte read + one copy
(`ByteArray.data` boxes every byte). -/
def dropFinalLF (b : ByteArray) : ByteArray :=
  if h : 0 < b.size then if b[b.size - 1] = 0x0A then b.extract 0 (b.size - 1) else b else b

/-- C6: the index the bytes denote (one final LF dropped, the rest J's text), else the first
refusal. -/
def decodeIndex (b : ByteArray) : Except IndexError IndexFile :=
  match decode (dropFinalLF b) with
  | .error j => .error (.text j)
  | .ok v =>
    match IndexFile.ofJson v with
    | .ok i => .ok i
    | .error d => .error (.doc d)

end FvdepCore.Index
