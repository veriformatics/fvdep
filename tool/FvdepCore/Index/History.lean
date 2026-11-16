import FvdepCore.Index.Doc

/-! `index.json`'s history gate (contract `docs/contracts/U4-library.md` C7 + C9 `history`): the
working tree's index against HEAD's + each of HEAD's parents' committed ones, pure over the decoded
baselines (the driver `fvdep-dev index history` reads them through git; U7's `admit --base` reuses
the check). C8 `HistoryExact` states it against the checks written apart. -/

namespace FvdepCore.Index.History

open FvdepCore.Ids FvdepCore.Index

/-- A baseline: a commit's full SHA + its committed `index.json` (`none` = absent: nothing to check;
an error = it does not decode, with the reason). -/
structure Baseline where
  commit : String
  index : Option (Except String IndexFile)

/-- C9's `history` violations: one stdout line each. -/
inductive Line where
  | noticesDiverge (head : String)
  | removedDiverge (head : String)
  | changedDigest (c : String) (id : ModuleId) (v : EntryVersion)
  | vanished (c : String) (id : ModuleId) (v : EntryVersion)
  | sameToolchain (c : String) (id : ModuleId) (v : EntryVersion)
  | lastCommit (c : String) (id : ModuleId) (v : EntryVersion) (got expected : String)
  | recordToolchain (c : String) (id : ModuleId) (v : EntryVersion) (got expected : String)
  | removedNotExtended (c : String)
  | noticesNotExtended (c : String)
  | undecodable (c : String) (reason : String)
  | workingUndecodable (reason : String)
  deriving DecidableEq, Repr

def subject (id : ModuleId) (v : EntryVersion) : String := s!"{id}@{v}"

def Line.render : Line → String
  | .noticesDiverge h => s!"history: {h}: the parents' notices diverge: rebase to linearize"
  | .removedDiverge h => s!"history: {h}: the parents' removed records diverge: rebase to linearize"
  | .changedDigest c i v => s!"history: {c}: {subject i v} changed its digest"
  | .vanished c i v => s!"history: {c}: {subject i v} vanished"
  | .sameToolchain c i v => s!"history: {c}: {subject i v} was removed without a toolchain change"
  | .lastCommit c i v g e =>
    s!"history: {c}: {subject i v}: the removal names lastCommit {g}, expected {e}"
  | .recordToolchain c i v g e =>
    s!"history: {c}: {subject i v}: the removal names toolchain {g}, expected {e}"
  | .removedNotExtended c => s!"history: {c}: the removed records do not extend this commit's"
  | .noticesNotExtended c => s!"history: {c}: the notices do not extend this commit's"
  | .undecodable c r => s!"history: {c}: index.json does not decode: {r}"
  | .workingUndecodable r => s!"history: working tree: index.json does not decode: {r}"

/-- The working tree's index when `index.json` is absent. -/
def emptyIndex : IndexFile := ⟨"", [], [], []⟩

/-- A baseline's decoded index. -/
def Baseline.decoded (b : Baseline) : Option IndexFile :=
  match b.index with
  | some (.ok i) => some i
  | _ => none

/-- `i` lists `(id, v)` as an operation. -/
def listsOp (i : IndexFile) (id : ModuleId) (v : EntryVersion) : Bool :=
  i.operations.any fun x => x.id == id && x.version == v

/-- `i` holds a removed record of `(id, v)`. -/
def holdsRemoved (i : IndexFile) (id : ModuleId) (v : EntryVersion) : Bool :=
  i.removed.any fun r => r.id == id && r.version == v

/-- C7's first removal of `o` with record `r`, judged under baseline `b` (index `ib`): HEAD lists it
→ under HEAD, the witness = HEAD; else a parent already holds a record of it → none (the prefix rule
owns it); else the parents listing it: any one is a witness, none → one line under the first. -/
def witnessLine (head : Baseline) (parents : List Baseline) (b : Baseline) (ib : IndexFile)
    (o : Operation) (r : Removed) : Option Line :=
  let holding :=
    parents.filter fun p => (p.decoded.map fun i => listsOp i o.id o.version) == some true
  let toolchainLine (t : String) : Option Line :=
    if r.toolchain = t then none else some (.recordToolchain b.commit o.id o.version r.toolchain t)
  if (head.decoded.map fun i => listsOp i o.id o.version) == some true then
    if b.commit = head.commit then
      if toString r.lastCommit = head.commit then toolchainLine ib.toolchain
      else some (.lastCommit b.commit o.id o.version (toString r.lastCommit) head.commit)
    else none
  else
    if parents.any fun p => (p.decoded.map fun i => holdsRemoved i o.id o.version) == some true then
      none
    else
      match holding.find? fun p => p.commit == (toString r.lastCommit) with
      | some p => if p.commit = b.commit then toolchainLine ib.toolchain else none
      | none =>
        match holding.head? with
        | some p =>
          if p.commit = b.commit then
            some (.lastCommit b.commit o.id o.version (toString r.lastCommit) p.commit)
          else none
        | none => none

/-- One baseline operation's line (≤ 1, C9's order): changed digest → vanished → removed without a
toolchain change → the first removal's witness. -/
def opLine (w : IndexFile) (head : Baseline) (parents : List Baseline) (b : Baseline)
    (ib : IndexFile) (o : Operation) : Option Line :=
  match w.operations.find? (fun x => x.id == o.id && x.version == o.version),
    w.removed.find? fun x => x.id == o.id && x.version == o.version with
  | some x, _ => if x.digest = o.digest then none else some (.changedDigest b.commit o.id o.version)
  | none, some r =>
    if r.digest ≠ o.digest then some (.changedDigest b.commit o.id o.version)
    else
      if w.toolchain = ib.toolchain then some (.sameToolchain b.commit o.id o.version)
      else witnessLine head parents b ib o r
  | none, none => some (.vanished b.commit o.id o.version)

/-- One baseline's lines: undecodable → that line alone; absent → none; else its operations (index
order), then its removed records' + notices' extension. -/
def baselineLines (w : IndexFile) (head : Baseline) (parents : List Baseline) (b : Baseline) :
    List Line :=
  match b.index with
  | none => []
  | some (.error reason) => [.undecodable b.commit reason]
  | some (.ok ib) =>
    ib.operations.filterMap (opLine w head parents b ib) ++
      (if ib.removed.isPrefixOf w.removed then [] else [.removedNotExtended b.commit]) ++
      if ib.notices.isPrefixOf w.notices then [] else [.noticesNotExtended b.commit]

/-- Two logs where neither extends the other. -/
def diverge {α : Type} [BEq α] (xs : List (List α)) : Bool :=
  xs.any fun a => xs.any fun b => !(a.isPrefixOf b || b.isPrefixOf a)

/-- C7 + C9: the violations, in C9's order: the parents' divergence, then HEAD's lines, then each
parent's (`work` = the working tree's index: `none` absent ⇒ empty, an error = undecodable). -/
def history (work : Except String (Option IndexFile)) (head : Baseline) (parents : List Baseline) :
    List Line :=
  match work with
  | .error reason => [.workingUndecodable reason]
  | .ok wo =>
    let w := wo.getD emptyIndex
    let logs := parents.filterMap Baseline.decoded
    (if diverge (logs.map (·.notices)) then [Line.noticesDiverge head.commit] else []) ++
      (if diverge (logs.map (·.removed)) then [Line.removedDiverge head.commit] else []) ++
      (head :: parents).flatMap (baselineLines w head parents)

end FvdepCore.Index.History
