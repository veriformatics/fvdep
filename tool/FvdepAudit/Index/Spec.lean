import FvdepAudit.Doc.Spec
import FvdepCore.Index.Doc

/-! `index.json` schema 1 written apart from the shipped schema data (contract
`docs/contracts/U4-library.md` C6 + C8): an index record's layout, its well-formedness (each node's
syntax + the relational clauses C3 V8 + V9), the order of relational refusals, and every field's
general JSON type. -/

namespace FvdepAudit.Index.Spec

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepCore.Index FvdepAudit.Doc.Spec

/-! ## Layout (C6: members in key order) -/

def statusText : Status → String
  | .proven => "proven"
  | .«open» => "open"
  | .trusts => "trusts"

def namesLayout (xs : List String) : Value := .arr (xs.map .str)

def obligationLayout (o : Obligation) : Value :=
  .obj
    [("axioms", namesLayout o.axioms), ("name", .str o.name),
      ("status", .str (statusText o.status))]

def compatLayout : Option Compat → Value
  | some c =>
    .obj
      [("axioms", namesLayout c.axioms), ("status", .str (statusText c.status)),
        ("version", .str (toString c.version))]
  | none => .null

def operationLayout (o : Operation) : Value :=
  .obj
    [("compat", compatLayout o.compat), ("digest", .str o.digest), ("id", .str (toString o.id)),
      ("obligations", .arr (o.obligations.map obligationLayout)),
      ("version", .str (toString o.version))]

def replacementLayout : Option EntryVersion → Value
  | some v => .str (toString v)
  | none => .null

def noticeLayout (n : Notice) : Value :=
  .obj
    [("id", .str (toString n.id)), ("reason", .str n.reason),
      ("replacement", replacementLayout n.replacement), ("version", .str (toString n.version))]

def removedLayout (r : Removed) : Value :=
  .obj
    [("digest", .str r.digest), ("id", .str (toString r.id)), ("kind", .str "operation"),
      ("last_commit", .str (toString r.lastCommit)), ("toolchain", .str r.toolchain),
      ("version", .str (toString r.version))]

def indexLayout (i : IndexFile) : Value :=
  .obj
    [("notices", .arr (i.notices.map noticeLayout)),
      ("operations", .arr (i.operations.map operationLayout)),
      ("removed", .arr (i.removed.map removedLayout)), ("schema", .int 1),
      ("toolchain", .str i.toolchain)]

/-! ## Each node (what the D5 walk judges) -/

/-- A status + its axioms: names of 1–1,024 bytes without a control character, strictly ascending,
consistent with the status. -/
def AxiomsWF (s : Status) (axs : List String) : Prop :=
  (∀ a ∈ axs, TextFits 1024 a) ∧ Ascends axs ∧ StatusAxioms (statusText s) axs

def ObligationWF (o : Obligation) : Prop := TextFits 1024 o.name ∧ AxiomsWF o.status o.axioms

def CompatWF (c : Compat) : Prop := AxiomsWF c.status c.axioms ∧ SpellingFits (toString c.version)

def OperationWF (o : Operation) : Prop :=
  SpellingFits (toString o.id) ∧
    SpellingFits (toString o.version) ∧
    DigestText o.digest ∧
    (∀ b ∈ o.obligations, ObligationWF b) ∧
    (o.obligations.map (·.name)).Nodup ∧ ∀ c, o.compat = some c → CompatWF c

/-- Operations strictly ascending by (id, version): each before the next. -/
def OpsAscend : List Operation → Prop
  | a :: b :: rest =>
    IdVersionBefore (toString a.id) (toString a.version) (toString b.id) (toString b.version) ∧
      OpsAscend (b :: rest)
  | _ => True

def NoticeNodeWF (n : Notice) : Prop :=
  SpellingFits (toString n.id) ∧
    SpellingFits (toString n.version) ∧
    TextFits 65536 n.reason ∧ ∀ v, n.replacement = some v → SpellingFits (toString v)

def RemovedNodeWF (r : Removed) : Prop :=
  SpellingFits (toString r.id) ∧
    SpellingFits (toString r.version) ∧ DigestText r.digest ∧ TextFits 1024 r.toolchain

def IndexNodeWF (i : IndexFile) : Prop :=
  TextFits 1024 i.toolchain ∧
    (∀ o ∈ i.operations, OperationWF o) ∧
    OpsAscend i.operations ∧ (∀ n ∈ i.notices, NoticeNodeWF n) ∧ ∀ r ∈ i.removed, RemovedNodeWF r

/-! ## Relational clauses (C3 V8 + V9 over the document) -/

/-- An (id, version) the index lists as an operation or a removed record. -/
def Listed (i : IndexFile) (m : ModuleId) (v : EntryVersion) : Prop :=
  (∃ o ∈ i.operations, o.id = m ∧ o.version = v) ∨ ∃ r ∈ i.removed, r.id = m ∧ r.version = v

/-- V8: the notice names a listed or removed entry; a replacement = another listed or removed
version of the same id. -/
def NoticeRel (i : IndexFile) (n : Notice) : Prop :=
  Listed i n.id n.version ∧ ∀ v, n.replacement = some v → v ≠ n.version ∧ Listed i n.id v

/-- V9: a removed record is no operation, appears before no equal record, and a notice names it. -/
def RemovedRel (i : IndexFile) (earlier : List Removed) (r : Removed) : Prop :=
  (¬∃ o ∈ i.operations, o.id = r.id ∧ o.version = r.version) ∧
    (¬∃ e ∈ earlier, e.id = r.id ∧ e.version = r.version) ∧
    ∃ n ∈ i.notices, n.id = r.id ∧ n.version = r.version

/-- C6 `IndexWellFormed`: every node + every relational clause. -/
def IndexWF (i : IndexFile) : Prop :=
  IndexNodeWF i ∧
    (∀ n ∈ i.notices, NoticeRel i n) ∧
    ((i.removed.map fun r => (r.id, r.version)).Nodup ∧
      ∀ r ∈ i.removed,
        (¬∃ o ∈ i.operations, o.id = r.id ∧ o.version = r.version) ∧
          ∃ n ∈ i.notices, n.id = r.id ∧ n.version = r.version)

open Classical in
/-- Every failing notice in order (its position + layout). -/
noncomputable def noticeViolations (i : IndexFile) : Nat → List Notice → List DocError
  | _, [] => []
  | k, n :: ns =>
    (if NoticeRel i n then []
      else [⟨[.key "notices", .index k], .badValue, some (noticeLayout n)⟩]) ++
      noticeViolations i (k + 1) ns

open Classical in
/-- Every failing removed record in order, judged against the records before it. -/
noncomputable def removedViolations (i : IndexFile) :
    Nat → List Removed → List Removed → List DocError
  | _, _, [] => []
  | k, earlier, r :: rs =>
    (if RemovedRel i earlier r then []
      else [⟨[.key "removed", .index k], .badValue, some (removedLayout r)⟩]) ++
      removedViolations i (k + 1) (earlier ++ [r]) rs

/-- The relational refusals in document order: notices, then removed records. -/
noncomputable def relationViolations (i : IndexFile) : List DocError :=
  noticeViolations i 0 i.notices ++ removedViolations i 0 [] i.removed

/-! ## General types (C6 + interface §6): the kinds each field's `wrong_type` is judged against -/

def namesKinds (p : List String) : List (List String × List JKind) :=
  [(p, [.arr]), (p ++ ["0"], [.str]), (p ++ ["*"], [.str])]

def obligationKinds (p : List String) : List (List String × List JKind) :=
  (p, [.obj]) ::
    (p ++ ["status"], [.str]) ::
    ["open", "proven", "trusts"].flatMap fun v =>
      namesKinds (p ++ ["@" ++ v, "axioms"]) ++ [(p ++ ["@" ++ v, "name"], [.str])]

def operationKinds (p : List String) : List (List String × List JKind) :=
  [(p, [.obj]), (p ++ ["compat"], [.null, .obj]), (p ++ ["digest"], [.str]), (p ++ ["id"], [.str]),
      (p ++ ["obligations"], [.arr])] ++
    obligationKinds (p ++ ["obligations", "0"]) ++
    obligationKinds (p ++ ["obligations", "*"]) ++
    [(p ++ ["version"], [.str])]

def noticeKinds (p : List String) : List (List String × List JKind) :=
  [(p, [.obj]), (p ++ ["id"], [.str]), (p ++ ["reason"], [.str]),
    (p ++ ["replacement"], [.null, .str]), (p ++ ["version"], [.str])]

def removedKinds (p : List String) : List (List String × List JKind) :=
  [(p, [.obj]), (p ++ ["digest"], [.str]), (p ++ ["id"], [.str]), (p ++ ["kind"], [.str]),
    (p ++ ["last_commit"], [.str]), (p ++ ["toolchain"], [.str]), (p ++ ["version"], [.str])]

/-- C6: the index root, its discriminator `schema` (an integer), then its members in key order. -/
def indexKinds : List (List String × List JKind) :=
  [([], [.obj]), (["schema"], [.int]), (["notices"], [.arr])] ++ noticeKinds ["notices", "0"] ++
    noticeKinds ["notices", "*"] ++
    [(["operations"], [.arr])] ++
    operationKinds ["operations", "0"] ++
    operationKinds ["operations", "*"] ++
    [(["removed"], [.arr])] ++
    removedKinds ["removed", "0"] ++
    removedKinds ["removed", "*"] ++
    [(["toolchain"], [.str])]

/-! ## Bytes (C6: canonical JSON + LF) -/

/-- The bytes with one final LF removed, read as a byte list. -/
def withoutFinalLF (b : ByteArray) : ByteArray :=
  if b.data.toList.getLast? = some 0x0A then ⟨b.data.toList.dropLast.toArray⟩ else b

end FvdepAudit.Index.Spec
