import FvdepCore.Profile.Check
import FvdepDev.Parse
import FvdepIO.Parse

/-! Never shipped. `fvdep-dev profile targets` + `profile witness <file>…` (contract U6 Q1 + Q2, the
witness corpus): the table's targets — every rule, every (kind, atom) pair outside the payload
shapes, the scope shapes' two rows, every anchor's slot (an optional one absent + present), every
deriving class — + the targets a module covers, read by the walk's own computation (the shipped
converter's trees, the owner + pending path as `walk` threads them). A module counts only when the
checker accepts it + it compiles on the same bytes (the runner's `phase check --profile`). -/

namespace FvdepDev.Witness

open FvdepCore.Profile Lean

/-- Shapes whose atoms are payloads (K2, K6): no atom target. -/
def payload : Shape → Bool
  | .doc _ => true
  | .literal => true
  | _ => false

/-- The two rows of a scope shape (C1's scope stack reads both). -/
def rows (r : Rule) : List String :=
  match r.shape with
  | .sectionCmd => [s!"shape\t{dotted r.kind}\tbare", s!"shape\t{dotted r.kind}\tnamed"]
  | .endCmd => [s!"shape\t{dotted r.kind}\tbare", s!"shape\t{dotted r.kind}\tnamed"]
  | _ => []

/-- Every target of the table, one line each. -/
def targets : List String :=
  (table.flatMap fun r =>
      s!"rule\t{dotted r.kind}" ::
        ((if payload r.shape then [] else r.atoms.map fun a => s!"atom\t{dotted r.kind}\t{a}") ++
          rows r)) ++
    (anchors.flatMap fun a =>
      if a.2.2.2 then [s!"anchor\t{dotted a.1}\tpresent"]
      else [s!"anchor\t{dotted a.1}\tabsent", s!"anchor\t{dotted a.1}\tpresent"]) ++
    derivingClasses.map fun c => s!"deriving\t{c}"

/-- The anchor path reaches an identifier from `kids`. -/
partial def reaches : Path → List Tree → Bool
  | [], _ => false
  | [some i], kids =>
    match (kids[i]? : Option Tree) with
    | some (.ident _ _) => true
    | _ => false
  | [none], kids => kids.any fun t => (t matches .ident _ _)
  | some i :: p :: rest, kids =>
    match (kids[i]? : Option Tree) with
    | some (.node _ ks) => reaches (p :: rest) ks
    | _ => false
  | none :: p :: rest, kids =>
    kids.any fun t =>
      match t with
      | .node _ ks => reaches (p :: rest) ks
      | _ => false

/-- The scope row a node's layout takes (`section` + `end`: an empty optional node = bare). -/
def shapeRow (r : Rule) (kids : List Tree) : List String :=
  let at? := fun (i : Nat) =>
    match (kids[i]? : Option Tree) with
    | some (.node _ []) => [s!"shape\t{dotted r.kind}\tbare"]
    | some (.node _ (_ :: _)) => [s!"shape\t{dotted r.kind}\tnamed"]
    | _ => []
  match r.shape with
  | .sectionCmd => at? 2
  | .endCmd => at? 1
  | _ => []

/-- An anchor kind's slot: present or absent. -/
def anchorRow (k : List String) (kids : List Tree) : List String :=
  match anchors.find? (·.1 == k) with
  | some (_, p, _, _) => [s!"anchor\t{dotted k}\t{if reaches p kids then "present" else "absent"}"]
  | none => []

mutual
/-- The targets an occurrence covers (the walk's traversal: wrappers pass the owner + the pending
path through, a listed kind owns its atoms). -/
partial def covered (owner : Option Rule) (pend : Option (Path × IdRole)) : Tree → List String
  | .node k kids =>
    if transparent k then coveredKids owner k pend 0 kids
    else
      match lookupRule k with
      | some r =>
        s!"rule\t{dotted k}" ::
          (shapeRow r kids ++ anchorRow k kids ++ coveredKids (some r) k pend 0 kids)
      | none => []
  | .atom a _ =>
    match owner with
    | some r => if payload r.shape then [] else [s!"atom\t{dotted r.kind}\t{a}"]
    | none => []
  | .ident n _ =>
    match pend with
    | some ([], .derivName) => [s!"deriving\t{dotted n}"]
    | _ => []
  | .missing => []
partial def coveredKids (owner : Option Rule) (k : List String) (pend : Option (Path × IdRole))
    (i : Nat) : List Tree → List String
  | [] => []
  | c :: cs => covered owner (childPending k pend i) c ++ coveredKids owner k pend (i + 1) cs
end

/-- One module's body targets: its commands parsed under the consumer grammar `env` + converted by
the shipped converter (P6's defaults), the header skipped (I1's, not K's). -/
def witnessFile (env : Environment) (path : String) : IO (Except String (List String)) := do
  let input := Parser.mkInputContext (← IO.FS.readFile path) path
  let (item, pst?, c0) ← FvdepIO.Parse.headItem {} ⟨0, 0⟩ input
  let (.tree _ _, some pst0) := (item, pst?) | return .error s!"{path}: the header stops"
  let mut pst := pst0
  let mut c := c0
  let mut out := #[]
  repeat
    let q := input.fileMap.toPosition pst.pos
    let (cmd, pst', log) := Parser.parseCommand input { env, options := {} } pst {}
    if log.hasErrors then
      return .error s!"{path}: a parse error at {q.line}:{q.column}"
    if cmd.isOfKind ``Parser.Command.eoi then
      break
    match FvdepIO.Parse.convert input.fileMap {} ⟨q.line, q.column⟩ c cmd with
    | (.ok t, c') =>
      out := out ++ (covered none none t).toArray
      c := c'
    | (.error _, _) =>
      return .error s!"{path}: a cap at {q.line}:{q.column}"
    pst := pst'
  return .ok out.toList

/-- `fvdep-dev profile targets`, `fvdep-dev profile witness <file>…`: one target per line, each
witness line once per module (sorted). -/
def run : List String → IO UInt32
  | ["targets"] => do
    for t in targets do
      IO.println t
    return 0
  | "witness" :: files@(_ :: _) => do
    let env ← FvdepDev.Parse.grammar [`Init, `Std]
    for f in files do
      match ← witnessFile env f with
      | .ok ts =>
        for t in (ts.mergeSort fun a b => Decidable.decide (a ≤ b)).eraseDups do
          IO.println s!"{f}\t{t}"
      | .error why =>
        IO.eprintln why
        return 1
    return 0
  | _ => do
    IO.eprintln "usage: fvdep-dev profile targets | profile witness <file>…"
    return 2

end FvdepDev.Witness
