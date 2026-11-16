import FvdepCore.Index.History

/-! `index.json`'s history gate written apart (contract `docs/contracts/U4-library.md` C7 + C9
`history`), in C9's procedure: the parents' divergence first, then HEAD's lines, then each parent's;
per baseline its operations in index order (≤ 1 line each: changed digest → vanished → removed
without a toolchain change → the first removal's witness), then its removed records' + notices'
extension. Conditions are stated as propositions (first match, membership, list prefix); the witness
rule over every baseline: HEAD lists the operation → judged under HEAD; a parent already holds a
record of it → none; else any parent listing it is a witness, none → one line under the first.
Shared with the shipped code: `Baseline`, `Line` (C9's vocabulary), `emptyIndex`. -/

namespace FvdepAudit.Index.History.Spec

open FvdepCore.Ids FvdepCore.Index FvdepCore.Index.History

/-- `x` = the first element of `xs` satisfying `P`. -/
def FirstIn {α : Type} (xs : List α) (P : α → Prop) (x : α) : Prop :=
  ∃ pre post, xs = pre ++ x :: post ∧ P x ∧ ∀ y ∈ pre, ¬P y

/-- Baseline `b`'s committed index lists `(id, v)` as an operation. -/
def ListsOp (b : Baseline) (id : ModuleId) (v : EntryVersion) : Prop :=
  ∃ i, b.index = some (.ok i) ∧ ∃ x ∈ i.operations, x.id = id ∧ x.version = v

/-- Baseline `b`'s committed index holds a removed record of `(id, v)`. -/
def HoldsRemoved (b : Baseline) (id : ModuleId) (v : EntryVersion) : Prop :=
  ∃ i, b.index = some (.ok i) ∧ ∃ r ∈ i.removed, r.id = id ∧ r.version = v

open Classical in
/-- C7's first removal of `o` (record `r`) judged under baseline `b` (index `ib`). -/
noncomputable def WitnessSpec (head : Baseline) (parents : List Baseline) (b : Baseline)
    (ib : IndexFile) (o : Operation) (r : Removed) : Option Line :=
  let holding := parents.filter fun p => decide (ListsOp p o.id o.version)
  let toolchainLine (t : String) : Option Line :=
    if r.toolchain = t then none else some (.recordToolchain b.commit o.id o.version r.toolchain t)
  if ListsOp head o.id o.version then
    if b.commit = head.commit then
      if toString r.lastCommit = head.commit then toolchainLine ib.toolchain
      else some (.lastCommit b.commit o.id o.version (toString r.lastCommit) head.commit)
    else none
  else
    if ∃ p ∈ parents, HoldsRemoved p o.id o.version then none
    else
      if ∃ p, FirstIn holding (fun p => p.commit = toString r.lastCommit) p then
        if
            ∃ p,
              FirstIn holding (fun p => p.commit = toString r.lastCommit) p ∧
                p.commit = b.commit then
          toolchainLine ib.toolchain
        else none
      else
        if ∃ p, holding.head? = some p ∧ p.commit = b.commit then
          some (.lastCommit b.commit o.id o.version (toString r.lastCommit) b.commit)
        else none

open Classical in
/-- One baseline operation's line (C9's check order). -/
noncomputable def OpLineSpec (w : IndexFile) (head : Baseline) (parents : List Baseline)
    (b : Baseline) (ib : IndexFile) (o : Operation) : Option Line :=
  if ∃ x, FirstIn w.operations (fun x => x.id = o.id ∧ x.version = o.version) x then
    if
        ∃ x,
          FirstIn w.operations (fun x => x.id = o.id ∧ x.version = o.version) x ∧
            x.digest = o.digest then
      none
    else some (.changedDigest b.commit o.id o.version)
  else
    if ∃ r, FirstIn w.removed (fun r => r.id = o.id ∧ r.version = o.version) r then
      if
          ∃ r,
            FirstIn w.removed (fun r => r.id = o.id ∧ r.version = o.version) r ∧
              r.digest ≠ o.digest then
        some (.changedDigest b.commit o.id o.version)
      else
        if w.toolchain = ib.toolchain then some (.sameToolchain b.commit o.id o.version)
        else
          if h : ∃ r, FirstIn w.removed (fun r => r.id = o.id ∧ r.version = o.version) r then
            WitnessSpec head parents b ib o (Classical.choose h)
          else none
    else some (.vanished b.commit o.id o.version)

open Classical in
/-- One baseline's lines. -/
noncomputable def BaselineSpec (w : IndexFile) (head : Baseline) (parents : List Baseline)
    (b : Baseline) : List Line :=
  match b.index with
  | none => []
  | some (.error reason) => [.undecodable b.commit reason]
  | some (.ok ib) =>
    ib.operations.filterMap (OpLineSpec w head parents b ib) ++
      (if ib.removed <+: w.removed then [] else [.removedNotExtended b.commit]) ++
      if ib.notices <+: w.notices then [] else [.noticesNotExtended b.commit]

/-- Two logs among `xs` where neither extends the other. -/
def Diverge {α : Type} (xs : List (List α)) : Prop := ∃ a ∈ xs, ∃ b ∈ xs, ¬(a <+: b ∨ b <+: a)

open Classical in
/-- C7 + C9: the violations in C9's order. -/
noncomputable def HistorySpec (work : Except String (Option IndexFile)) (head : Baseline)
    (parents : List Baseline) : List Line :=
  match work with
  | .error reason => [.workingUndecodable reason]
  | .ok wo =>
    let w := wo.getD emptyIndex
    let logs :=
      parents.filterMap fun p =>
        match p.index with
        | some (.ok i) => some i
        | _ => none
    (if Diverge (logs.map (·.notices)) then [Line.noticesDiverge head.commit] else []) ++
      (if Diverge (logs.map (·.removed)) then [Line.removedDiverge head.commit] else []) ++
      (head :: parents).flatMap (BaselineSpec w head parents)

end FvdepAudit.Index.History.Spec
