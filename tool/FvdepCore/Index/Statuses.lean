import FvdepCore.Index.Doc
import FvdepCore.Index.Rules

/-! Obligation + compat status (contract `docs/contracts/U4-library.md` C5) with C9's warnings, and
the entry digest's input files (C4). Pure over `Facts` (C8 boundary), after `validate` accepted the
lists + the kernel replayed the library; C8 `StatusExact` states it against the chain written apart
(`FvdepAudit.Index.Statuses`). -/

namespace FvdepCore.Index.Statuses

open Lean FvdepCore.Ids FvdepCore.Index.Registry FvdepCore.Index.Rules

/-- `n` with its first component replaced by `FvdepProofs`. -/
def reroot : Name → Name
  | .str .anonymous _ => .str .anonymous "FvdepProofs"
  | .str p s => .str (reroot p) s
  | .num p k => .num (reroot p) k
  | .anonymous => .anonymous

/-- The proof registry constant of entry module `Fvdep.Registry.<Dep>.<Op>.V…`
(`FvdepProofs.Registry.<Dep>.<Op>.V….proofs`: `docs/library.md` Registry). -/
def proofsName (M : Name) : Name := .str (reroot M) "proofs"

/-- C9's `<why>`: the reason a statement counts as open with no axioms. -/
inductive Why where
  | noRegistry
  | unreadable
  | unmapped
  | mappedTwice
  | notTheorem (t : Name)
  | outside (t : Name)
  | otherStatement (t : Name)
  deriving DecidableEq, Repr

def Why.text : Why → String
  | .noRegistry => "no proof registry"
  | .unreadable => "its proof registry cannot be read"
  | .unmapped => "no theorem is mapped"
  | .mappedTwice => "two theorems are mapped"
  | .notTheorem t => s!"{t} is not a theorem"
  | .outside t => s!"{t} is outside FvdepProofs"
  | .otherStatement t => s!"{t} proves another statement"

/-- C9's warnings (subject = `<id>@<version>`). -/
inductive Warning where
  | obligation (subject : String) (o : Name) (why : Why)
  | compat (subject : String) (why : Why)
  | ignored (subject : String) (t : Name)
  deriving DecidableEq, Repr

def Warning.render : Warning → String
  | .obligation s o w => s!"Warning: {s}: obligation {o} counts as open: {w.text}."
  | .compat s w => s!"Warning: {s}: compat counts as open: {w.text}."
  | .ignored s t => s!"Warning: {s}: the compat theorem {t} is ignored: no compat is declared."

/-- An entry's proof registry: its constant absent → `noRegistry`; present but outside C2's forms →
`unreadable`. -/
def proofRegistry (F : Facts) (e : Entry) : Except Why Proofs :=
  let c := proofsName e.module
  match F.decls.find? (·.name == c) with
  | none => .error .noRegistry
  | some _ =>
    match readProofs F c with
    | .ok p => .ok p
    | .error _ => .error .unreadable

/-- A mapped theorem `t` against the statement check `ok`: the first failing C5 condition (a name
the facts lack lies outside both libraries ⇒ outside `FvdepProofs`). -/
def judge (F : Facts) (t : Name) (ok : Expr → Bool) : Option Why :=
  match F.decls.find? (·.name == t) with
  | none => some (.outside t)
  | some d =>
    match d.kind == .thm, d.module.getRoot == `FvdepProofs, ok d.type with
    | false, _, _ => some (.notTheorem t)
    | true, false, _ => some (.outside t)
    | true, true, false => some (.otherStatement t)
    | true, true, true => none

/-- The standard axioms (Decisions Obligation status). -/
def std : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `x` placed into a strictly ascending list, once. -/
def insertAsc (x : String) : List String → List String
  | [] => [x]
  | y :: ys =>
    match decide (x < y), decide (x = y) with
    | true, _ => x :: y :: ys
    | false, true => y :: ys
    | false, false => y :: insertAsc x ys

/-- Strictly ascending (code point order = UTF-8 byte order), each once (axiom lists are short:
insertion). -/
def ascending (xs : List String) : List String := xs.foldr insertAsc []

/-- The axioms `t` rests on beyond the standard three, printed, ascending (`none` = not
observed). -/
def extraAxioms (ax : List (Name × List Name)) (t : Name) : Option (List String) :=
  (ax.find? (·.1 == t)).map fun x => ascending ((x.2.filter (· ∉ std)).map (·.toString))

/-- C5: `sorryAx` among them → open; none → proven; else trusts. -/
def axiomStatus (axioms : List String) : Status :=
  match axioms.contains "sorryAx", axioms.isEmpty with
  | true, _ => .«open»
  | false, true => .proven
  | false, false => .trusts

/-- One statement's outcome: (status, axioms, the warning cause); `.error t` = no axiom list
observed for `t` (a load refusal: absence fails closed). -/
abbrev Outcome := Except Name (Status × List String × Option Why)

def opened (w : Why) : Outcome := .ok (.«open», [], some w)

def outcome (F : Facts) (ax : List (Name × List Name)) (t : Name) (ok : Expr → Bool) : Outcome :=
  match judge F t ok with
  | some w => opened w
  | none =>
    match extraAxioms ax t with
    | some a => .ok (axiomStatus a, a, none)
    | none => .error t

/-- An obligation `o`: the theorem its entry's proof registry maps it to, of type exactly `o`. -/
def obligationOutcome (F : Facts) (ax : List (Name × List Name)) (pr : Except Why Proofs)
    (o : Name) : Outcome :=
  match pr with
  | .error w => opened w
  | .ok p =>
    match p.obligations.filter (·.1 == o) with
    | [] => opened .unmapped
    | [x] => outcome F ax x.2 fun ty => alphaEq ty (.const o [])
    | _ => opened .mappedTwice

/-- The obligations' outcomes, in entry order (the first missing axiom list refuses). -/
def outcomes (F : Facts) (ax : List (Name × List Name)) (pr : Except Why Proofs) :
    List Name → Except Name (List (Status × List String × Option Why))
  | [] => .ok []
  | o :: os =>
    match obligationOutcome F ax pr o, outcomes F ax pr os with
    | .ok r, .ok rs => .ok (r :: rs)
    | .error t, _ => .error t
    | _, .error t => .error t

/-- `@Eq.{u} T a b`. -/
def eqE (u : Level) (T a b : Expr) : Expr := .app (.app (.app (.const ``Eq [u]) T) a) b

/-- The universe level of an `Eq` application (after `erase`). -/
def eqLevel? : Expr → Option Level
  | .app (.app (.app (.const ``Eq [u]) _) _) _ => some u
  | _ => none

/-- C5's compat statement `@Eq T new old` (T = the new spec's type; `Eq`'s level = the theorem's
own: the replay accepted it, so it is T's). -/
def compatStatement (T : Expr) (new old : Name) (ty : Expr) : Bool :=
  match eqLevel? (erase ty) with
  | some u => alphaEq ty (eqE u T (.const new []) (.const old []))
  | none => false

/-- The compat theorem's outcome against `@Eq T new old`. -/
def compatOutcome (F : Facts) (ax : List (Name × List Name)) (T : Expr) (new old : Name)
    (pr : Except Why Proofs) : Outcome :=
  match pr with
  | .error w => opened w
  | .ok p =>
    match p.compat with
    | none => opened .unmapped
    | some t => outcome F ax t (compatStatement T new old)

/-- An entry's compat edge (version, outcome): T = its spec's declared type, `old` = the listed
spec of the compat version (validated: both exist). -/
def compatEdge (F : Facts) (ax : List (Name × List Name)) (l : Lists) (e : Entry)
    (pr : Except Why Proofs) : Except Name (Option (String × Status × List String × Option Why)) :=
  match e.compat with
  | none => .ok none
  | some c =>
    let T := ((libDecl? F e.spec).map (·.type)).getD (.sort .zero)
    let old := ((listedAt? l e.id c).map (·.spec)).getD .anonymous
    (compatOutcome F ax T e.spec old pr).map fun r => some (c, r)

/-- An entry's statuses: per obligation (entry order) its name, status + axioms; its compat edge
(version, status, axioms); C9's warnings in order (obligations, compat, an ignored compat
theorem). -/
structure EntryStatus where
  obligations : List (Name × Status × List String)
  compat : Option (String × Status × List String)
  warnings : List Warning
  deriving DecidableEq, Repr

/-- C9: a mapped compat theorem of an entry that declares no compat. -/
def ignoredWarnings (e : Entry) (pr : Except Why Proofs) : List Warning :=
  match e.compat, pr with
  | none, .ok p => (p.compat.map (Warning.ignored (subject e.id e.version))).toList
  | _, _ => []

/-- C9's warnings of an entry: its obligations' (entry order), its compat edge's, then a mapped
compat theorem it declares no compat for. -/
def warningsOf (e : Entry) (pr : Except Why Proofs) (rs : List (Status × List String × Option Why))
    (edge : Option (String × Status × List String × Option Why)) : List Warning :=
  (e.obligations.zip rs).filterMap
      (fun x => x.2.2.2.map (Warning.obligation (subject e.id e.version) x.1)) ++
    (edge.bind fun x => x.2.2.2.map (Warning.compat (subject e.id e.version))).toList ++
    ignoredWarnings e pr

def entryStatus (F : Facts) (ax : List (Name × List Name)) (l : Lists) (e : Entry) :
    Except Name EntryStatus :=
  let pr := proofRegistry F e
  match outcomes F ax pr e.obligations, compatEdge F ax l e pr with
  | .ok rs, .ok edge =>
    .ok {
        obligations := (e.obligations.zip rs).map fun x => (x.1, x.2.1, x.2.2.1)
        compat := edge.map fun x => (x.1, x.2.1, x.2.2.1)
        warnings := warningsOf e pr rs edge }
  | .error t, _ => .error t
  | _, .error t => .error t

/-- Every entry's statuses in `modules` order; a theorem without an observed axiom list refuses as
load (C9: `Could not load the built library: no axiom list of <t> observed for <id>@<version>.`). -/
def statuses (F : Facts) (ax : List (Name × List Name)) (l : Lists) :
    Except Found (List (Entry × EntryStatus)) := go l.entries
where go : List Entry → Except Found (List (Entry × EntryStatus))
    | [] => .ok []
    | e :: es =>
      match entryStatus F ax l e, go es with
      | .ok s, .ok rest => .ok ((e, s) :: rest)
      | .error t, _ => .error (subject e.id e.version, .unobserved s!"axiom list of {t}")
      | _, .error f => .error f

/-! ## C4: the entry digest's framed input -/

/-- The closure modules' (canonical path, observed bytes): the files an entry's digest frames (H3
`fvdep/entry/1`). -/
def closureFiles (F : Facts) (M : Name) : List (String × ByteArray) :=
  (closure F M).filterMap fun m => (modFacts? F m).bind fun x => x.file.map (modulePath m, ·)

end FvdepCore.Index.Statuses
