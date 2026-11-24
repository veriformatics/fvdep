import FvdepCore.Profile.Check
import FvdepCore.Profile.Record

/-! The child's batch (contract `docs/contracts/U6-profile.md` C1, P3, P5, P5b): every module's
header item in batch order (the header stage), then — the header stage clean — every module's
grammar (P3) + its body; the first event in C1's order ends the batch; `accepted` only when every
header was observed + every body met its input's end clean. The child observes in this order +
stops at the first event, read from the same functions (`headEvent`, `step`); `conclude` judges what
it observed. Pure. -/

namespace FvdepCore.Profile

/-- The profile this child implements (P5b's `profile`; Q2's version id). -/
def profileId : String := "fvdep/profile/1"

/-- I1's names of a header tree's imports in source order, fail closed: `none` when the header or
one of its imports is outside Lean 4.35's layout (`headerParts`, `importParts`). -/
def importsExact (h : Tree) : Option (List String) :=
  match headerParts h with
  | some (_, _, imps) => imps.mapM fun t => (importParts t).map fun x => dotted x.2.1
  | none => none

/-- A header the stage accepted: its imports' names (`importsExact` holds for it). -/
def importsOf (h : Tree) : List String := (importsExact h).getD []

/-- One batch module as the child observed it: its header item (`none` = never observed: the
batch's first event came earlier), the body stage's state after its items (`State.init` = none
fed) + whether the parser met the input's actual end after them (P5's pass). -/
structure Observed where
  module : String
  head : Option Item
  state : State
  ended : Bool

/-- A stage's end: its first event + the module it occurred in, clean, or short (an observation
stopped before its end with no event: no outcome). -/
inductive Stage where
  | event (module : String) (e : Event)
  | clean
  | short

/-- I1 + I2 over a module's header item: its stop event, else its header's first finding. -/
def headEvent (role : Role) (lib batch : List String) (m : String) : Item → Option Event
  | .stop e => some e
  | .tree h _ => (header role lib batch m h).map .finding

/-- C1's header stage over every module in batch order. -/
def headStage (role : Role) (lib batch : List String) : List Observed → Stage
  | [] => .clean
  | o :: os =>
    match o.head with
    | none => .short
    | some i =>
      match headEvent role lib batch o.module i with
      | some e => .event o.module e
      | none => headStage role lib batch os

/-- A module's own name's first component (I2's library rule). -/
def rootOf (m : String) : String := (m.splitOn ".").headD ""

/-- C1's body stage over every module in batch order: a module's event, else it must have ended
clean. -/
def bodyStage : List Observed → Stage
  | [] => .clean
  | o :: os =>
    match o.state.event with
    | some e => .event o.module e
    | none => if o.ended then bodyStage os else .short

/-- P3's grammar of every batch module (batch order): a batch module's imports = its header's, a
library module's = its request row's; the fuel covers every import edge twice + every module (a
module is visited once, each visit pops one frame). -/
def grammars (req : Request) (obs : List Observed) : List (List String) :=
  let heads :=
    obs.map fun o =>
      (o.module,
        match o.head with
        | some (.tree h _) => importsOf h
        | _ => [])
  let imports := fun (x : String) =>
    match heads.lookup x with
    | some is => is
    | none => ((req.library.find? (·.module == x)).map (·.imports)).getD []
  let edges := (heads.map (·.2.length)).sum + (req.library.map (·.imports.length)).sum
  let fuel := 2 * edges + heads.length + req.library.length + 2
  obs.map fun o => grammar imports fuel o.module

/-- P5b's outcome of an event in module `m`. -/
def outcomeOf (m : String) : Event → Outcome
  | .finding f => .refused ⟨m, f.pos.line, f.pos.col, f.rule, f.detail⟩
  | .over => .over

/-- The batch's outcome + each module's grammar (C1, P3, P5b): the header stage over every module,
then — clean — the body stage; grammars once the header stage is clean, `[]` otherwise. `none` =
the observations do not cover the batch: another module list than the request's, or a stage that
stopped short with no event. -/
def conclude (req : Request) (obs : List Observed) : Option (Outcome × List (List String)) :=
  if obs.map (·.module) = req.modules.map (·.module) then
    match headStage req.role (req.library.map (·.module)) (req.modules.map (·.module)) obs with
    | .short => none
    | .event m e => some (outcomeOf m e, obs.map fun _ => [])
    | .clean =>
      match bodyStage obs with
      | .short => none
      | .event m e => some (outcomeOf m e, grammars req obs)
      | .clean => some (.accepted, grammars req obs)
  else none

/-- P5b's record of a decided batch: the request's modules in batch order with the digests of the
bytes read + their grammars, the outcome, this profile's id, the request's recipe + the digest of
the request bytes read. -/
def assemble (req : Request) (digest : String) (shas : List String) (o : Outcome)
    (gs : List (List String)) : Record :=
  { modules := (req.modules.zip (shas.zip gs)).map fun x => ⟨x.1.module, x.2.1, x.2.2⟩
    outcome := o
    profile := profileId
    recipe := req.recipe
    request := digest }

end FvdepCore.Profile
