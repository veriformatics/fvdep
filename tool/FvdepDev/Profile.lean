import FvdepDev.Parse

/-! Never shipped. The residue dumps (contract U6 D4: a test reads kinds, atoms + positions from
them, never a verdict): each file parsed in the trusted grammar (`Init` + `Std`; the variable
`FVDEP_DEV_GRAMMAR` overrides). `kinds` = one line per node kind, per atom (with its parent's kind)
+ per identifier under a kind whose names the profile checks; `owned` = the table's view per file:
`kind`, `atom` under its owner kind (`null` + `group` transparent, payloads printed `<payload>`),
`ident`; `positions` = each node at its first positioned leaf + each positioned atom + identifier;
`idents` = every identifier leaf; `stats` = bytes, commands, occurrences + depth per file; `parse` =
the parse time alone; `grammar` + `modules` = the parser kinds per category + the modules a
toolchain import list loads; `scoped` = the namespaces carrying scoped parser entries. -/

namespace FvdepDev.Profile

open FvdepDev.ProfileTree

def usage : String :=
  "usage: fvdep-dev profile (kinds|idents|parse|owned|positions|stats) <file>..." ++
    " | profile scoped | profile (grammar|modules) <module>...\n"

def dotted (xs : List String) : String := ".".intercalate xs

/-- Kinds whose identifier leaves the profile checks by name. -/
def named (k : String) : Bool :=
  ["Attr", "set_option", "namespace", "open", "section", "end", "deriving"].any fun p =>
    (k.splitOn p).length > 1

/-- The dump lines of `t` under the parent kind `parent`. -/
partial def dump (parent : String) : Tree → List String
  | .node k _ kids =>
    let kk := dotted k
    s!"node\t{kk}" :: kids.flatMap (dump kk)
  | .atom t _ => [s!"atom\t{parent}\t{t}"]
  | .ident n _ => if named parent then [s!"ident\t{parent}\t{dotted n}"] else []
  | .missing => [s!"missing\t{parent}"]

/-- The file dumps' grammar: `FVDEP_DEV_GRAMMAR` (comma-separated toolchain modules), else
`Init,Std` (contract U6 P3: a module's own closure sets its grammar). -/
def devGrammar : IO Lean.Environment := do
  let mods := ((← IO.getEnv "FVDEP_DEV_GRAMMAR").getD "Init,Std").splitOn ","
  FvdepDev.Parse.grammar (mods.map String.toName)

/-- Every identifier leaf's components. -/
partial def idents : Tree → List (List String)
  | .node _ _ kids => kids.flatMap idents
  | .ident n _ => [n]
  | _ => []

/-- Wrapper kinds the table reads through: their atoms + identifiers belong to the nearest other
ancestor (contract U6 K). -/
def transparent (k : String) : Bool := k == "null" || k == "group"

/-- Literal kinds: their one atom = the lexer's payload. -/
def literal (k : String) : Bool :=
  ["num", "str", "char", "scientific", "name", "fieldIdx"].contains k

/-- Doc kinds: the opening atom, then the payload. -/
def doc (k : String) : Bool :=
  k == "Lean.Parser.Command.docComment" || k == "Lean.Parser.Command.moduleDoc"

/-- The table's view of `t` under its owner kind `owner`: `kind <k> <owner>` per node (wrappers
included), `atom <owner> <text>` per atom (a payload slot printed `<payload>`), `ident <owner>` per
identifier leaf. -/
partial def owned (owner : String) : Tree → List String
  | .node k _ kids =>
    let kk := dotted k
    let next := if transparent kk then owner else kk
    s!"kind\t{kk}\t{owner}" ::
      (kids.zipIdx.flatMap fun (c, i) =>
        match c with
        | .atom t _ =>
          if literal next || (doc next && i > 0) then [s!"atom\t{next}\t<payload>"]
          else [s!"atom\t{next}\t{t}"]
        | _ => owned next c)
  | .atom t _ => [s!"atom\t{owner}\t{t}"]
  | .ident _ _ => [s!"ident\t{owner}"]
  | .missing => [s!"missing\t{owner}"]

/-- The first positioned leaf of `t` in pre-order: a node's location (contract U6 C1; Lean's
`Syntax.getPos?`). -/
partial def firstPos : Tree → Option Pos
  | .node _ _ kids => kids.findSome? firstPos
  | .atom _ p => p
  | .ident _ p => p
  | .missing => none

/-- Every located occurrence of `t`: `<line>:<column> node <kind>` (at `firstPos`) | `atom <text>` |
`ident <name>`. -/
partial def positions : Tree → List String
  | t@(.node k _ kids) =>
    let rest := kids.flatMap positions
    match firstPos t with
    | some q => s!"{q.line}:{q.col}\tnode\t{dotted k}" :: rest
    | none => rest
  | .atom t (some q) => [s!"{q.line}:{q.col}\tatom\t{t}"]
  | .ident n (some q) => [s!"{q.line}:{q.col}\tident\t{dotted n}"]
  | _ => []

/-- Nodes (every node, atom, identifier + `missing` = one) + depth (a leaf = 1) of `t`. -/
partial def size : Tree → Nat × Nat
  | .node _ _ kids =>
    let (n, d) :=
      kids.foldl
        (fun (n, d) k =>
          let (n', d') := size k;
          (n + n', max d d'))
        (0, 0)
    (n + 1, d + 1)
  | _ => (1, 1)

def run : List String → IO UInt32
  | "kinds" :: files@(_ :: _) => do
    let env ← devGrammar
    let mut rc : UInt32 := 0
    for f in files do
      let text ← IO.FS.readFile f
      match ← FvdepDev.Parse.parseModule env {} f text with
      | .ok ts =>
        for t in ts do
          for l in dump "" t do
            IO.println l
      | .error why =>
        IO.eprintln why
        rc := 1
    return rc
  | "idents" :: files@(_ :: _) => do
    let env ← devGrammar
    for f in files do
      match ← FvdepDev.Parse.parseModule env {} f (← IO.FS.readFile f) with
      | .ok ts =>
        for t in ts do
          for n in idents t do
            IO.println (dotted n)
      | .error why =>
        IO.eprintln why
    return 0
  | ["scoped"] => do
    for mods in [[`Init], [`Init, `Std]] do
      let env ← FvdepDev.Parse.grammar mods
      let st := Lean.Parser.parserExtension.ext.getState env
      let keys := st.scopedEntries.map.toList.map fun e => (e.1, e.2.size)
      IO.println s!"grammar {mods}: {keys.length} namespaces with scoped parser entries"
      for (ns, n) in keys do
        IO.println s!"  {ns} {n}"
    return 0
  | "owned" :: files@(_ :: _) => do
    let env ← devGrammar
    let mut rc : UInt32 := 0
    for f in files do
      IO.println s!"file\t{f}"
      match ← FvdepDev.Parse.parseModule env {} f (← IO.FS.readFile f) with
      | .ok ts =>
        for t in ts do
          for l in owned "" t do
            IO.println l
      | .error why =>
        IO.println s!"refused\t{why}"
        rc := 1
    return rc
  | "positions" :: files@(_ :: _) => do
    let env ← devGrammar
    for f in files do
      IO.println s!"file\t{f}"
      match ← FvdepDev.Parse.parseModule env {} f (← IO.FS.readFile f) with
      | .ok ts =>
        for t in ts do
          for l in positions t do
            IO.println l
      | .error why =>
        IO.println s!"refused\t{why}"
    return 0
  | "stats" :: files@(_ :: _) => do
    let env ← devGrammar
    IO.println "file\tbytes\tcommands\tnodes\tdepth"
    for f in files do
      let text ← IO.FS.readFile f
      match ← FvdepDev.Parse.parseModule env {} f text with
      | .ok ts =>
        let (n, d) :=
          ts.foldl
            (fun (n, d) t =>
              let (n', d') := size t;
              (n + n', max d d'))
            (0, 0)
        IO.println s!"{f}\t{text.utf8ByteSize}\t{ts.length - 1}\t{n}\t{d}"
      | .error why =>
        IO.println s!"{f}\trefused\t{why}"
    return 0
  | "grammar" :: mods@(_ :: _) => do
    let env ← FvdepDev.Parse.grammar (mods.map String.toName)
    let st := Lean.Parser.parserExtension.getState env
    for (c, pc) in st.categories.foldl (fun acc c pc => (c, pc) :: acc) [] do
      for k in pc.kinds.foldl (fun acc k _ => k :: acc) [] do
        IO.println s!"{c}\t{k}"
    return 0
  | "modules" :: mods@(_ :: _) => do
    let env ← FvdepDev.Parse.grammar (mods.map String.toName)
    for m in env.allImportedModuleNames do
      IO.println m
    return 0
  | "parse" :: files@(_ :: _) => do
    let env ← devGrammar
    for f in files do
      let text ← IO.FS.readFile f
      let t0 ← IO.monoMsNow
      let r ← FvdepDev.Parse.parseModule env {} f text
      let t1 ← IO.monoMsNow
      match r with
      | .ok ts =>
        IO.println s!"{f}: {ts.length} trees, {t1 - t0} ms"
      | .error why =>
        IO.println s!"{f}: refused ({why.take 80}), {t1 - t0} ms"
    return 0
  | _ => do
    IO.eprint usage
    return 2

end FvdepDev.Profile
