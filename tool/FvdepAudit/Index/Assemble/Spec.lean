import FvdepAudit.Index.Spec
import FvdepAudit.Index.Statuses.Spec
import FvdepCore.Index.Assemble

/-! `index.json`'s value written apart (contract `docs/contracts/U4-library.md` C4, C6, C9): each
obligation by V4's shape `S.<name>`, each operation from its registry strings + statuses + the
digest of its closure's H3 frame, the operations an arrangement of the entries strictly ascending in
C6's (id, version) order (`IdVersionBefore`, the order the schema walk enforces), notices + removed
records in registry order, the toolchain = the `lean-toolchain` text without surrounding
whitespace, C9's warnings in `modules` order. Reused: `StatusesSpec` (C-rules-b's spec); shared
with the shipped code: `closureFiles` (C4), `FvdepCore.Hash.frame` (U3 H). -/

namespace FvdepAudit.Index.Assemble.Spec

open Lean FvdepCore.Json FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses FvdepAudit.Doc.Spec FvdepAudit.Index.Spec
open FvdepAudit.Index.Statuses.Spec

/-- C6: `t` = `raw` without its leading + trailing whitespace (`Char.isWhitespace`). -/
def Trimmed (raw t : String) : Prop :=
  ∃ pre post,
    raw.toList = pre ++ t.toList ++ post ∧
      (∀ c ∈ pre, c.isWhitespace = true) ∧
      (∀ c ∈ post, c.isWhitespace = true) ∧
      ∀ c, (t.toList.head? = some c ∨ t.toList.getLast? = some c) → c.isWhitespace = false

def NamesV (xs : List String) : Value := .arr (xs.map .str)

/-- C6: an obligation of an entry whose spec module is `S`: `S.<name>` (V4) with its status + the
axioms beyond the standard three. -/
def ObligationV (S : Name) (x : Name × FvdepCore.Index.Status × List String) (v : Value) : Prop :=
  ∃ name,
    x.1 = .str S name ∧
      v = .obj [("axioms", NamesV x.2.2), ("name", .str name), ("status", .str (statusText x.2.1))]

/-- C6: a compat edge (version, status, axioms), or `null`. -/
def CompatV : Option (String × FvdepCore.Index.Status × List String) → Value
  | some x =>
    .obj [("axioms", NamesV x.2.2), ("status", .str (statusText x.2.1)), ("version", .str x.1)]
  | none => .null

/-- C4 + C6: an operation from its registry strings + statuses; `digest` = `h` of the H3
`fvdep/entry/1` frame over its closure's files. -/
def OperationV (h : ByteArray → String) (F : Facts) (x : Entry × EntryStatus) (v : Value) : Prop :=
  ∃ obs : List Value,
    obs.length = x.2.obligations.length ∧
      (∀ p ∈ x.2.obligations.zip obs, ObligationV (specModule x.1) p.1 p.2) ∧
      v =
        .obj
          [("compat", CompatV x.2.compat),
            ("digest", .str (h (FvdepCore.Hash.frame "fvdep/entry/1" (closureFiles F x.1.module)))),
            ("id", .str x.1.id), ("obligations", .arr obs), ("version", .str x.1.version)]

/-- C6: a notice from its registry strings. -/
def NoticeV (n : FvdepCore.Index.Registry.Notice) : Value :=
  .obj
    [("id", .str n.id), ("reason", .str n.reason),
      ("replacement",
        match n.replacement with
        | some r => .str r
        | none => .null),
      ("version", .str n.version)]

/-- C6: a removed record from its registry strings (`kind` spelled from the registry's). -/
def RemovedV (r : FvdepCore.Index.Registry.Removed) : Value :=
  .obj
    [("digest", .str r.digest), ("id", .str r.id),
      ("kind",
        .str
          (match r.kind with
          | .operation => "operation"
          | .profile => "profile")),
      ("last_commit", .str r.lastCommit), ("toolchain", .str r.toolchain),
      ("version", .str r.version)]

/-- C4 + C6 + C9: the index value + warnings of a registry: its entries' statuses (`StatusesSpec`),
the operations = those entries arranged strictly ascending in C6's (id, version) order, the
toolchain trimmed, the warnings in `modules` order. -/
def AssembleSpec (F : Facts) (ax : List (Name × List Name)) (l : Lists) (raw : String)
    (h : ByteArray → String) (v : Value) (ws : List Warning) : Prop :=
  ∃ (rs ps : List (Entry × EntryStatus)) (ops : List Value) (tc : String),
    StatusesSpec F ax l rs ∧
      ps.Perm rs ∧
      ps.Pairwise (fun a b => IdVersionBefore a.1.id a.1.version b.1.id b.1.version) ∧
      ops.length = ps.length ∧
      (∀ p ∈ ps.zip ops, OperationV h F p.1 p.2) ∧
      Trimmed raw tc ∧
      v =
        .obj
          [("notices", .arr (l.notices.map NoticeV)), ("operations", .arr ops),
            ("removed", .arr (l.removed.map RemovedV)), ("schema", .int 1),
            ("toolchain", .str tc)] ∧
      ws = rs.flatMap fun x => x.2.warnings

end FvdepAudit.Index.Assemble.Spec
