import FvdepCore.Profile.Check

/-! U6 C1 + C2's spec of the walk (contract `docs/contracts/U6-profile.md` C1, K0, K0', P4, I2, I3,
K4), written apart from `FvdepCore.Profile.walk`: every occurrence of a command's tree in pre-order
with its ancestor chain (innermost first, each with the child index the path took); the context
each rule reads — owner, identifier role, location — computed from the chain alone; the findings
at one occurrence in C1's rule order. The command's first finding = the head of their
concatenation (`walkFirst`); a clean command = every list empty (`walkAccepts`). The table, the
anchors, S + the generated names stay data (`lookupRule`, `anchors`, `scopedNamespaces`,
`derivingClasses`, `generated`): rules are stated over them, never over their contents. Shared
with the implementation + read as spec text: `shapeOk` (K0' + K2 + K4 + K6: one pattern per layout
the contract lists, every other layout a miss), `dotted` + `cutDetail` (T's cap). -/

namespace FvdepAudit.Profile.Walk.Spec

open FvdepCore.Profile

/-- An occurrence: its tree + its ancestors, innermost first, each with the index of the child the
path took. -/
abbrev Occ := Tree × List (Tree × Nat)

mutual
/-- C1's pre-order: an occurrence, then its children's left to right (a `choice`'s arms = its
children, in order). -/
def occsOf (anc : List (Tree × Nat)) : Tree → List Occ
  | t@(.node _ kids) => (t, anc) :: occsKids t anc 0 kids
  | t => [(t, anc)]
def occsKids (p : Tree) (anc : List (Tree × Nat)) (i : Nat) : List Tree → List Occ
  | [] => []
  | c :: cs => occsOf ((p, i) :: anc) c ++ occsKids p anc (i + 1) cs
end

/-- K1: the wrappers the walk reads through. -/
def wrapper (k : List String) : Prop := k = ["null"] ∨ k = ["group"] ∨ k = ["choice"]

instance (k : List String) : Decidable (wrapper k) := by
  unfold wrapper; exact inferInstance

/-- K0: an atom's owner = the rule of its nearest ancestor that is no wrapper. -/
def ownerOf : List (Tree × Nat) → Option Rule
  | [] => none
  | (.node k _, _) :: rest => if wrapper k then ownerOf rest else lookupRule k
  | _ :: rest => ownerOf rest

/-- A path (outer → inner child indexes) matches an anchor path (`none` = any child). -/
def pathMatches : Path → List Nat → Bool
  | [], [] => true
  | some j :: p, i :: is => j == i && pathMatches p is
  | none :: p, _ :: is => pathMatches p is
  | _, _ => false

/-- I3 (b) + P4 + K4: an identifier's role = the nearest anchor-kind ancestor's, when the child
indexes from it down to the identifier match its path; else a use. -/
def roleOf (anc : List (Tree × Nat)) : IdRole := go [] anc
where go (below : List Nat) : List (Tree × Nat) → IdRole
    | [] => .use
    | (.node k _, i) :: rest =>
      match anchors.find? (·.1 == k) with
      | some (_, p, r, _) => if pathMatches p (i :: below) then r else .use
      | none => go (i :: below) rest
    | (_, i) :: rest => go (i :: below) rest

/-- C1: a tree's first positioned leaf in pre-order (an atom or an identifier carrying one). -/
def leafPos (t : Tree) : Option Pos :=
  (occsOf [] t).findSome? fun o =>
    match o.1 with
    | .atom _ q => q
    | .ident _ q => q
    | _ => none

/-- C1's location: the occurrence's first positioned leaf, else its nearest ancestor's, else the
command's start. -/
def locOf (start : Pos) (t : Tree) (anc : List (Tree × Nat)) : Pos :=
  ((t :: anc.map (·.1)).findSome? leafPos).getD start

mutual
/-- The occurrences strictly inside `t`, each with its child-index path from `t` (outer → inner). -/
def inside : Tree → List (Tree × List Nat)
  | .node _ kids => insideKids 0 kids
  | _ => []
/-- Children `cs` from index `i`, each followed by the occurrences inside it. -/
def insideKids (i : Nat) : List Tree → List (Tree × List Nat)
  | [] => []
  | c :: cs => ((c, [i]) :: (inside c).map fun o => (o.1, i :: o.2)) ++ insideKids (i + 1) cs
end

/-- K0' + I3 (b) + P4 + K4: an anchor kind's declaring slots, fail closed — every occurrence inside
its children on a proper prefix of its path is a node, every occurrence at its full length an
identifier; a required slot reaches at least one. -/
def slotsHold (k : List String) (kids : List Tree) : Bool :=
  match anchors.find? (·.1 == k) with
  | some (_, p, _, req) =>
    (insideKids 0 kids).all
        (fun o =>
          if o.2.length < p.length && pathMatches (p.take o.2.length) o.2 then
            (o.1 matches .node _ _)
          else if pathMatches p o.2 then (o.1 matches .ident _ _) else true) &&
      (!req || (insideKids 0 kids).any fun o => pathMatches p o.2)
  | none => true

/-- T: a finding's details under the detail cap. -/
def mk (p : Pos) (rule : String) (detail : List String) : Finding := ⟨p, rule, detail.map cutDetail⟩

/-- I2: a full name breaks the module's ownership — consumer: a first component `Init`, `Std`,
`Lean`, `Lake` or one starting with `Fvdep`; library: a first component other than its own. -/
def ownBroken (s : Subject) : List String → Bool
  | [] => false
  | c :: _ =>
    match s.role with
    | .consumer => ["Init", "Std", "Lean", "Lake"].contains c || c.startsWith "Fvdep"
    | .library => c != s.root

/-- P4: the first accumulated namespace in S (the enclosing namespaces ++ each prefix of `n`,
shortest first), else `n` itself when it holds a `_root_` component. -/
def nsScoped (ns n : List String) : Option (List String) :=
  (((List.range n.length).map fun i => ns ++ n.take (i + 1)).find? fun a =>
      scopedNamespaces.contains a) <|>
    if n.contains "_root_" then some n else none

/-- I3 (a) + (b): an identifier's first reserved component, left to right — `_`-led anywhere, one
of Lean's generated names at a declaring slot. -/
def firstReserved (declaring : Bool) (n : List String) : Option String :=
  n.find? fun c => c.startsWith "_" || (declaring && generated c)

/-- C1's node rules after `kind` + `shape`: `scope` then `ownership` at a `namespace` (its name =
child 1), `ownership` at a `declId` (its name = child 0), `ownership instance` at an anonymous
instance (child 3 empty) outside every namespace (library). -/
def roleRules (s : Subject) (ns k : List String) (kids : List Tree) (p : Pos) : List Finding :=
  if k == kindNamespace then
    match (kids[1]? : Option Tree) with
    | some (.ident n _) =>
      match nsScoped ns n with
      | some a => [mk p "scope" ["namespace", dotted a]]
      | none => if ownBroken s (ns ++ n) then [mk p "ownership" [dotted (ns ++ n)]] else []
    | _ => []
  else
    if k == kindDeclId then
      match (kids[0]? : Option Tree) with
      | some (.ident n _) =>
        if ownBroken s (ns ++ n) then [mk p "ownership" [dotted (ns ++ n)]] else []
      | _ => []
    else
      if
          k == kindInstance && s.role == .library && ns.isEmpty &&
            (match (kids[3]? : Option Tree) with
            | some (.node _ (_ :: _)) => false
            | _ => true) then
        [mk p "ownership" ["instance"]]
      else []

/-- K0 + K0' + C1: the findings at a node occurrence, in rule order. -/
def nodeRules (s : Subject) (ns : List String) (start : Pos) (o : Occ) : List Finding :=
  match o.1 with
  | .node k kids =>
    if wrapper k then []
    else
      match lookupRule k with
      | none => [mk (locOf start o.1 o.2) "kind" [dotted k]]
      | some r =>
        if shapeOk r.shape kids && slotsHold k kids then roleRules s ns k kids (locOf start o.1 o.2)
        else [mk (locOf start o.1 o.2) "shape" [dotted k]]
  | _ => []

/-- K0: an atom outside its owner's set (doc + literal payloads belong to their shape). -/
def atomRules (start : Pos) (o : Occ) : List Finding :=
  match o.1, ownerOf o.2 with
  | .atom a _, some r =>
    match r.shape with
    | .doc _ | .literal => []
    | _ => if r.atoms.contains a then [] else [mk (locOf start o.1 o.2) "atom" [dotted r.kind, a]]
  | _, _ => []

/-- C1's identifier rules in order, for an identifier `n` of role `role` at `p`: `scope` (an `open`
name in S by suffix, or holding `_root_`), `reserved`, `reserved main`, `name deriving`. -/
def identRulesAt (ns : List String) (role : IdRole) (n : List String) (p : Pos) : List Finding :=
  (if
        role == .openName &&
          (n.contains "_root_" || scopedNamespaces.any fun x => n.isSuffixOf x) then
      [mk p "scope" ["open", dotted n]]
    else []) ++
    (match firstReserved (role == .slot || role == .declName) n with
    | some c => [mk p "reserved" [c]]
    | none => []) ++
    (if role == .declName && ns ++ n == ["main"] then [mk p "reserved" ["main"]] else []) ++
    (if role == .derivName && !(derivingClasses.any fun c => n == [c]) then
      [mk p "name" ["deriving", dotted n]]
    else [])

/-- C1: the identifier rules at an identifier occurrence (its role from the chain). -/
def identRules (ns : List String) (start : Pos) (o : Occ) : List Finding :=
  match o.1 with
  | .ident n _ => identRulesAt ns (roleOf o.2) n (locOf start o.1 o.2)
  | _ => []

/-- C1: every finding at one occurrence, in rule order. -/
def findingsAt (s : Subject) (ns : List String) (start : Pos) (o : Occ) : List Finding :=
  nodeRules s ns start o ++ atomRules start o ++ identRules ns start o

/-- C1: a command's findings in C1's total order (pre-order, then rule order). -/
def findings (s : Subject) (ns : List String) (start : Pos) (t : Tree) : List Finding :=
  (occsOf [] t).flatMap (findingsAt s ns start)

end FvdepAudit.Profile.Walk.Spec
