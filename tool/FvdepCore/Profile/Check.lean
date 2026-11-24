import FvdepCore.Profile.Table

/-! The implementation profile's checks (contract `docs/contracts/U6-profile.md` C1, K0, P3, P4,
I1–I3): one module's header stage, its body walk over the command trees in source order (the first
finding in C1's order), the scope stack between commands + each module's grammar. Pure; mutual
structural recursion with match-based first-wins (U6-D states the claims against a spec over
trees). -/

namespace FvdepCore.Profile

/-- A finding: its location (C1) + its typed cause (T: `rule` + `detail`). -/
structure Finding where
  pos : Pos
  rule : String
  detail : List String
  deriving DecidableEq, Repr

/-- The module a check reads: its role + its own name's first component (I2's library rule). -/
structure Subject where
  role : Role
  root : String
  deriving DecidableEq, Repr

def dotted (xs : List String) : String := ".".intercalate xs

/-- The longest prefix of `cs` within `n` UTF-8 bytes (it stops at the first character that does
not fit: a prefix ends on a character boundary). -/
def takeBytes : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs => if c.utf8Size ≤ n then c :: takeBytes (n - c.utf8Size) cs else []

/-- T's detail cap: a string over 1,024 UTF-8 bytes → its longest prefix of ≤ 1,021 bytes ending on
a character boundary + `...`. -/
def cutDetail (s : String) : String :=
  if s.utf8ByteSize ≤ detailMax then s
  else String.ofList (takeBytes (detailMax - 3) s.toList) ++ "..."

def found (p : Pos) (rule : String) (detail : List String) : Option Finding :=
  some ⟨p, rule, detail.map cutDetail⟩

/-! ## Trees -/

/-- K1: the wrappers the walk reads through (`choice` = every arm walked, in order). -/
def transparent (k : List String) : Bool := k == ["null"] || k == ["group"] || k == ["choice"]

mutual
/-- C1: an occurrence's first positioned leaf in pre-order (Lean 4.35's `Syntax.getPos?`). -/
def Tree.firstPos : Tree → Option Pos
  | .node _ kids => firstPosList kids
  | .atom _ p => p
  | .ident _ p => p
  | .missing => none
def firstPosList : List Tree → Option Pos
  | [] => none
  | t :: ts =>
    match t.firstPos with
    | some p => some p
    | none => firstPosList ts
end

/-- C1: the location of `t` under ancestors `anc` (innermost first): its first positioned leaf,
else the nearest enclosing occurrence's, else the command's start. -/
def locate (start : Pos) (t : Tree) (anc : List Tree) : Pos :=
  match (t :: anc).findSome? Tree.firstPos with
  | some p => p
  | none => start

/-- The identifier a `.ident` child is at child `i` of `kids` (a name's components). -/
def identAt (kids : List Tree) (i : Nat) : Option (List String) :=
  match (kids[i]? : Option Tree) with
  | some (.ident n _) => some n
  | _ => none

/-- A `null` child at `i` holding anything. -/
def present (kids : List Tree) (i : Nat) : Bool :=
  match (kids[i]? : Option Tree) with
  | some (.node _ (_ :: _)) => true
  | _ => false

/-! ## The table -/

def lookupRule (k : List String) : Option Rule := table.find? (·.kind == k)

def kindNamespace : List String := ["Lean", "Parser", "Command", "namespace"]

def kindSection : List String := ["Lean", "Parser", "Command", "section"]

def kindEnd : List String := ["Lean", "Parser", "Command", "end"]

def kindDeclId : List String := ["Lean", "Parser", "Command", "declId"]

def kindInstance : List String := ["Lean", "Parser", "Command", "instance"]

/-- K0's slot rules. -/
def shapeOk : Shape → List Tree → Bool
  | .free, _ => true
  | .doc o, [.atom a _, .atom _ _] => a == o
  | .doc _, _ => false
  | .literal, [.atom _ _] => true
  | .literal, _ => false
  | .quotedName, [.node ["name"] _] => true
  | .quotedName, _ => false
  | .doubleQuotedName, [.atom "`" _, .atom "`" _, .ident _ _] => true
  | .doubleQuotedName, _ => false
  | .derivingClass, [_, .ident _ _] => true
  | .derivingClass, _ => false

/-! ## Identifiers -/

/-- What an identifier is to the walk (C1's identifier rules, I3's slots, K4's deriving names). -/
inductive IdRole where
  | use
  | openName
  | declName
  | slot
  | derivName
  deriving DecidableEq, Repr

/-- A child-index path (`none` = any child) from an anchor kind to the identifiers it gives a
role. -/
abbrev Path := List (Option Nat)

/-- I3 (b) + P4 + K4: each anchor kind's path to its identifiers (Lean 4.35's parser layouts;
`fvdep-dev profile tree` prints them). -/
def anchors : List (List String × Path × IdRole) :=
  [("Lean.Parser.Command.declId".splitOn ".", [some 0], .declName),
    ("Lean.Parser.Command.ctor".splitOn ".", [some 3], .slot),
    ("Lean.Parser.Command.structCtor".splitOn ".", [some 1], .slot),
    ("Lean.Parser.Command.structSimpleBinder".splitOn ".", [some 1], .slot),
    ("Lean.Parser.Command.structExplicitBinder".splitOn ".", [some 2, none], .slot),
    ("Lean.Parser.Command.structImplicitBinder".splitOn ".", [some 2, none], .slot),
    ("Lean.Parser.Command.structInstBinder".splitOn ".", [some 2, none], .slot),
    ("Lean.Parser.Command.structParent".splitOn ".", [some 0, some 0], .slot),
    ("Lean.Parser.Term.letRecDecl".splitOn ".", [some 2, some 0, some 0, some 0], .slot),
    ("Lean.Parser.Command.derivingClass".splitOn ".", [some 1], .derivName),
    ("Lean.Parser.Command.openSimple".splitOn ".", [some 0, none], .openName)]

/-- The pending path a node hands its `i`-th child: the node's own anchor, else the one it got. -/
def childPending (k : List String) (got : Option (Path × IdRole)) (i : Nat) :
    Option (Path × IdRole) :=
  match (anchors.find? (·.1 == k)).map (·.2) with
  | some p => step p
  | none => step' got
where
  step : Path × IdRole → Option (Path × IdRole)
    | (s :: rest, r) => if s == none || s == some i then some (rest, r) else none
    | ([], _) => none
  step' : Option (Path × IdRole) → Option (Path × IdRole)
    | some p => step p
    | none => none

/-- I3 (b): one of Lean's generated declaration names (`eq_<n>`, `match_<n>`, `proof_<n>` with `n`
decimal included). -/
def generated (c : String) : Bool :=
  generatedNames.contains c ||
    ["eq_", "match_", "proof_"].any fun p =>
      match c.dropPrefix? p with
      | some rest => !rest.isEmpty && rest.all Char.isDigit
      | none => false

/-- I3 (a) + (b): the first reserved component of `n`, left to right. -/
def reservedComponent (decl : Bool) : List String → Option String
  | [] => none
  | c :: cs =>
    if c.startsWith "_" || (decl && generated c) then some c else reservedComponent decl cs

/-- P4: `xs` ends with `ys` (full components). -/
def endsWith (xs ys : List String) : Bool :=
  ys.length ≤ xs.length && xs.drop (xs.length - ys.length) == ys

/-- The identifier rules at one identifier (C1: `scope`, `reserved`, then `name`). -/
def identFinding (ns : List String) (role : IdRole) (n : List String) (p : Pos) : Option Finding :=
  let scope :=
    role == .openName && (n.contains "_root_" || scopedNamespaces.any fun s => endsWith s n)
  if scope then found p "scope" ["open", dotted n]
  else
    match reservedComponent (role == .slot || role == .declName) n with
    | some c => found p "reserved" [c]
    | none =>
      if role == .declName && ns ++ n == ["main"] then found p "reserved" ["main"]
      else
        if role == .derivName && !(derivingClasses.any fun c => n == [c]) then
          found p "name" ["deriving", dotted n]
        else none

/-! ## Ownership + scope (node rules) -/

/-- I2's ownership of the full name `full` in module `s`. -/
def ownershipBroken (s : Subject) (full : List String) : Bool :=
  match s.role, full with
  | .consumer, c :: _ => ["Init", "Std", "Lean", "Lake"].contains c || c.startsWith "Fvdep"
  | .library, c :: _ => c != s.root
  | _, [] => false

/-- P4's namespace check over `ns ++ each prefix of n` (shortest first), then a `_root_`
component. -/
def namespaceScope (ns n : List String) : Option (List String) :=
  match
    ((List.range n.length).map fun i => ns ++ n.take (i + 1)).find? scopedNamespaces.contains with
  | some acc => some acc
  | none => if n.contains "_root_" then some n else none

/-- A node's role rules (C1: after `kind` + `shape`): `scope` then `ownership` at a `namespace`,
`ownership` at a `declId` + at an anonymous `instance` outside every namespace (library role). -/
def nodeFinding (s : Subject) (ns k : List String) (kids : List Tree) (p : Pos) : Option Finding :=
  if k == kindNamespace then
    match identAt kids 1 with
    | some n =>
      match namespaceScope ns n with
      | some acc => found p "scope" ["namespace", dotted acc]
      | none => if ownershipBroken s (ns ++ n) then found p "ownership" [dotted (ns ++ n)] else none
    | none => none
  else
    if k == kindDeclId then
      match identAt kids 0 with
      | some n =>
        if ownershipBroken s (ns ++ n) then found p "ownership" [dotted (ns ++ n)] else none
      | none => none
    else
      if k == kindInstance && s.role == .library && ns.isEmpty && !present kids 3 then
        found p "ownership" ["instance"]
      else none

/-! ## The walk -/

/-- An atom's rule under its owner kind (K0; doc + literal payloads belong to their shape). -/
def atomFinding (owner : Option Rule) (a : String) (p : Pos) : Option Finding :=
  match owner with
  | some r =>
    match r.shape with
    | .doc _ | .literal => none
    | _ => if r.atoms.contains a then none else found p "atom" [dotted r.kind, a]
  | none => none

mutual
/-- The first finding inside occurrence `t` (C1's pre-order; each finding located against `anc`,
the ancestors innermost first, + the command's `start`). -/
def walk (s : Subject) (ns : List String) (start : Pos) (owner : Option Rule)
    (pend : Option (Path × IdRole)) (anc : List Tree) : Tree → Option Finding
  | t@(.node k kids) =>
    if transparent k then walkKids s ns start owner k pend (t :: anc) 0 kids
    else
      match lookupRule k with
      | none => found (locate start t anc) "kind" [dotted k]
      | some r =>
        if !shapeOk r.shape kids then found (locate start t anc) "shape" [dotted k]
        else
          match nodeFinding s ns k kids (locate start t anc) with
          | some f => some f
          | none => walkKids s ns start (some r) k pend (t :: anc) 0 kids
  | t@(.atom a _) => atomFinding owner a (locate start t anc)
  | t@(.ident n _) =>
    let role :=
      match pend with
      | some ([], r) => r
      | _ => .use
    identFinding ns role n (locate start t anc)
  | .missing => none
/-- `kids` (from index `i`) of a node of kind `k`, in order: the first finding. -/
def walkKids (s : Subject) (ns : List String) (start : Pos) (owner : Option Rule) (k : List String)
    (pend : Option (Path × IdRole)) (anc : List Tree) (i : Nat) : List Tree → Option Finding
  | [] => none
  | c :: cs =>
    match walk s ns start owner (childPending k pend i) anc c with
    | some f => some f
    | none => walkKids s ns start owner k pend anc (i + 1) cs
end

/-! ## Scopes between commands (C1) -/

/-- C1's scope stack: each scope's namespace components, outermost first (a section's = `[]`). -/
abbrev Scopes := List (List String)

def Scopes.ns (sc : Scopes) : List String := sc.flatten

/-- The scope stack after the top-level command `t` (applied once its walk is clean): `namespace
A.B` pushes one scope per component, `section` one unnamed scope (`section A.B` one per component),
`end` pops one (`end A.B` one per component, never below empty); `mutual … end` holds its own
`end`. -/
def next (sc : Scopes) : Tree → Scopes
  | .node k kids =>
    if k == kindNamespace then
      match identAt kids 1 with
      | some n => sc ++ n.map fun c => [c]
      | none => sc
    else
      if k == kindSection then
        match (kids[2]? : Option Tree) with
        | some (.node _ [.ident n _]) => sc ++ n.map fun _ => []
        | _ => sc ++ [[]]
      else
        if k == kindEnd then
          match (kids[1]? : Option Tree) with
          | some (.node _ [.ident n _]) => sc.take (sc.length - n.length)
          | _ => sc.take (sc.length - 1)
        else sc
  | _ => sc

/-! ## One module (C1's command order) -/

/-- One item of a module's body stage, in source order (P5): a command's tree + its start, or the
first parse or cap finding the child met there. -/
inductive Item where
  | tree (t : Tree) (start : Pos)
  | stop (f : Finding)

/-- The body stage's state: the scope stack + the first finding so far. -/
structure State where
  scopes : Scopes
  finding : Option Finding

/-- One item into the state: a finding stays; a clean command moves the scope stack. -/
def step (s : Subject) (st : State) : Item → State
  | .tree t start =>
    match st.finding with
    | some _ => st
    | none =>
      match walk s st.scopes.ns start none none [] t with
      | some f => { st with finding := some f }
      | none => { st with scopes := next st.scopes t }
  | .stop f =>
    match st.finding with
    | some _ => st
    | none => { st with finding := some f }

/-- A module's body stage: its first finding in C1's order. -/
def body (s : Subject) (items : List Item) : Option Finding :=
  (items.foldl (step s) ⟨[], none⟩).finding

/-! ## The header stage (I1, I2, I3 (a)) -/

/-- I2: a module's own name under its role. -/
def nameOk (role : Role) (m : String) : Bool :=
  let cs := m.splitOn "."
  !cs.any (·.startsWith "_") &&
    match role, cs with
    | .consumer, c :: _ => !(["Init", "Std", "Lean", "Lake"].contains c || c.startsWith "Fvdep")
    | .library, c :: _ => c == "Fvdep" || c == "FvdepPreview"
    | _, [] => false

/-- I1: an import of module `self` under its role (`lib` = the pinned library's modules, `batch` =
the batch's). -/
def importOk (role : Role) (lib batch : List String) (self m : String) : Bool :=
  let first := fun (x : String) => (x.splitOn ".").headD ""
  m == "Init" || first m == "Std" ||
    match role with
    | .consumer => (lib.contains m && first m == "Fvdep") || batch.contains m
    | .library =>
      batch.contains m &&
        (first m == "Fvdep" || (first self == "FvdepPreview" && first m == "FvdepPreview"))

/-- One import's findings (I1: its modifier, then its name; then I3 (a) on the name). -/
def importFinding (role : Role) (lib batch : List String) (self : String) (start : Pos) (t : Tree) :
    Option Finding :=
  match t with
  | .node _ kids =>
    let here := (t.firstPos).getD start
    let modifier :=
      [0, 1, 3].findSome? fun i =>
        match (kids[i]? : Option Tree) with
        | some (.node _ (.atom a _ :: _)) => some a
        | _ => none
    match modifier with
    | some a => found here "header" ["modifier", a]
    | none =>
      match identAt kids 4 with
      | some n =>
        if !importOk role lib batch self (dotted n) then found here "header" ["import", dotted n]
        else
          match reservedComponent false n with
          | some c =>
            found
              (match (kids[4]? : Option Tree) with
              | some (.ident _ (some q)) => q
              | _ => here)
              "reserved" [c]
          | none => none
      | none => none
  | _ => none

/-- A module's header stage (C1 + I1 + I2): its name (`header name`, at 1:0), then `module`,
`prelude`, then each import in source order. -/
def header (role : Role) (lib batch : List String) (self : String) (h : Tree) : Option Finding :=
  if !nameOk role self then found ⟨1, 0⟩ "header" ["name", self]
  else
    match h with
    | .node _ kids =>
      let posAt := fun (i : Nat) => (kids[i]?.bind Tree.firstPos).getD ⟨1, 0⟩
      if present kids 0 then found (posAt 0) "header" ["module"]
      else
        if present kids 1 then found (posAt 1) "header" ["prelude"]
        else
          match (kids[2]? : Option Tree) with
          | some (.node _ imps) => imps.findSome? (importFinding role lib batch self ⟨1, 0⟩)
          | _ => none
    | _ => none

/-! ## P3: a module's grammar -/

def toolchainModule (m : String) : Bool :=
  ["Init", "Std", "Lean", "Lake"].contains ((m.splitOn ".").headD "")

/-- P3: `Init`, then each toolchain module a non-toolchain module of `m`'s closure imports, in the
order a depth-first walk first meets it (imports in source order, each module visited once), each
listed once; `fuel` ≥ every import edge + module of the closure. -/
def grammar (imports : String → List String) (fuel : Nat) (m : String) : List String :=
  go fuel [imports m] [m] ["Init"]
where go : Nat → List (List String) → List String → List String → List String
    | 0, _, _, acc => acc
    | _, [], _, acc => acc
    | n + 1, [] :: frames, seen, acc => go n frames seen acc
    | n + 1, (i :: is) :: frames, seen, acc =>
      if toolchainModule i then
        go n (is :: frames) seen (if acc.contains i then acc else acc ++ [i])
      else
        if seen.contains i then go n (is :: frames) seen acc
        else go n (imports i :: is :: frames) (i :: seen) acc

end FvdepCore.Profile
