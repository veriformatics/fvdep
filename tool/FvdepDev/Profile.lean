import FvdepDev.Differential
import FvdepDev.Parse
import FvdepDev.ProfileCheck
import FvdepDev.Walk
import FvdepDev.Witness

/-! Never shipped. The residue dumps (contract U6 D4: a test reads kinds, atoms + positions from
them, never a verdict): each file parsed in the trusted grammar (`Init` + `Std`; the variable
`FVDEP_DEV_GRAMMAR` overrides). `kinds` = one line per node kind, per atom (with its parent's kind)
+ per identifier under a kind whose names the profile checks; `owned` = the table's view per file:
`kind`, `atom` under its owner kind (`null` + `group` transparent, payloads printed `<payload>`),
`ident`; `positions` = each node at its first positioned leaf + each positioned atom + identifier;
`idents` = every identifier leaf; `stats` = bytes, commands, occurrences + depth per file; `parse` =
the parse time alone; `grammar` + `modules` = the parser kinds per category + the modules a
toolchain import list loads; `scoped` = the namespaces carrying scoped parser entries (`--check`:
P4's gate check, the live set over `[Init, Std]` = `FvdepCore.Profile.scopedNamespaces`). -/

namespace FvdepDev.Profile

open FvdepDev.ProfileTree

def usage : String :=
  "usage: fvdep-dev profile (kinds|idents|parse|owned|positions|stats|tree) <file>..." ++
    " | profile scoped [--check] | profile (grammar|modules) <module>...\n" ++
    "  | profile tokens <kind>...\n" ++
    "  | profile walk [--library] [--lib=<M>=<I>,...]... [--limit=<name>=<n>]... <file>...\n" ++
    "  | profile check --role consumer|library [--library <dir>] [--limit <name>=<n>]... " ++
    "[--results <file> | --child <file>] <src dir> <module>...\n"

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

/-- The builtin parsers among K's kinds: compiled into this binary, absent from the trusted
grammar's environment (`mkParserOfConstant` resolves `ParserDescr` notations alone). -/
def builtinParsers : List (Lean.Name × Lean.Parser.Parser) :=
  [(``«Lean».«Parser».«Command».«moduleDoc», «Lean».«Parser».«Command».«moduleDoc»),
    (``«Lean».«Parser».«Command».«docComment», «Lean».«Parser».«Command».«docComment»),
    (``«Lean».«Parser».«Command».«namespace», «Lean».«Parser».«Command».«namespace»),
    (``«Lean».«Parser».«Command».«section», «Lean».«Parser».«Command».«section»),
    (``«Lean».«Parser».«Command».«sectionHeader», «Lean».«Parser».«Command».«sectionHeader»),
    (``«Lean».«Parser».«Command».«end», «Lean».«Parser».«Command».«end»),
    (``«Lean».«Parser».«Command».«open», «Lean».«Parser».«Command».«open»),
    (``«Lean».«Parser».«Command».«openSimple», «Lean».«Parser».«Command».«openSimple»),
    (``«Lean».«Parser».«Command».«openOnly», «Lean».«Parser».«Command».«openOnly»),
    (``«Lean».«Parser».«Command».«variable», «Lean».«Parser».«Command».«variable»),
    (``«Lean».«Parser».«Command».«universe», «Lean».«Parser».«Command».«universe»),
    (``«Lean».«Parser».«Command».«declaration», «Lean».«Parser».«Command».«declaration»),
    (``«Lean».«Parser».«Command».«private», «Lean».«Parser».«Command».«private»),
    (``«Lean».«Parser».«Command».«protected», «Lean».«Parser».«Command».«protected»),
    (``«Lean».«Parser».«Command».«definition», «Lean».«Parser».«Command».«definition»),
    (``«Lean».«Parser».«Command».«abbrev», «Lean».«Parser».«Command».«abbrev»),
    (``«Lean».«Parser».«Command».«instance», «Lean».«Parser».«Command».«instance»),
    (``«Lean».«Parser».«Command».«structure», «Lean».«Parser».«Command».«structure»),
    (``«Lean».«Parser».«Command».«structureTk», «Lean».«Parser».«Command».«structureTk»),
    (``«Lean».«Parser».«Command».«classTk», «Lean».«Parser».«Command».«classTk»),
    (``«Lean».«Parser».«Command».«extends», «Lean».«Parser».«Command».«extends»),
    (``«Lean».«Parser».«Command».«structParent», «Lean».«Parser».«Command».«structParent»),
    (``«Lean».«Parser».«Command».«structCtor», «Lean».«Parser».«Command».«structCtor»),
    (``«Lean».«Parser».«Command».«structFields», «Lean».«Parser».«Command».«structFields»),
    (``«Lean».«Parser».«Command».«structSimpleBinder»,
      «Lean».«Parser».«Command».«structSimpleBinder»),
    (``«Lean».«Parser».«Command».«structExplicitBinder»,
      «Lean».«Parser».«Command».«structExplicitBinder»),
    (``«Lean».«Parser».«Command».«structImplicitBinder»,
      «Lean».«Parser».«Command».«structImplicitBinder»),
    (``«Lean».«Parser».«Command».«structInstBinder», «Lean».«Parser».«Command».«structInstBinder»),
    (``«Lean».«Parser».«Command».«inductive», «Lean».«Parser».«Command».«inductive»),
    (``«Lean».«Parser».«Command».«ctor», «Lean».«Parser».«Command».«ctor»),
    (``«Lean».«Parser».«Command».«mutual», «Lean».«Parser».«Command».«mutual»),
    (``«Lean».«Parser».«Command».«declId», «Lean».«Parser».«Command».«declId»),
    (``«Lean».«Parser».«Command».«declSig», «Lean».«Parser».«Command».«declSig»),
    (``«Lean».«Parser».«Command».«optDeclSig», «Lean».«Parser».«Command».«optDeclSig»),
    (``«Lean».«Parser».«Command».«declValSimple», «Lean».«Parser».«Command».«declValSimple»),
    (``«Lean».«Parser».«Command».«declValEqns», «Lean».«Parser».«Command».«declValEqns»),
    (``«Lean».«Parser».«Command».«whereStructInst», «Lean».«Parser».«Command».«whereStructInst»),
    (``«Lean».«Parser».«Command».«optDeriving», «Lean».«Parser».«Command».«optDeriving»),
    (``«Lean».«Parser».«Command».«derivingClass», «Lean».«Parser».«Command».«derivingClass»),
    (``Lean.Parser.Command.declModifiers, Lean.Parser.Command.declModifiers false),
    (``«Lean».«Parser».«Term».«attrKind», «Lean».«Parser».«Term».«attrKind»),
    (``«Lean».«Parser».«Term».«whereDecls», «Lean».«Parser».«Term».«whereDecls»),
    (``«Lean».«Parser».«Term».«letRecDecl», «Lean».«Parser».«Term».«letRecDecl»),
    (``«Lean».«Parser».«Term».«app», «Lean».«Parser».«Term».«app»),
    (``«Lean».«Parser».«Term».«paren», «Lean».«Parser».«Term».«paren»),
    (``«Lean».«Parser».«Term».«hygienicLParen», «Lean».«Parser».«Term».«hygienicLParen»),
    (``«Lean».«Parser».«Term».«tuple», «Lean».«Parser».«Term».«tuple»),
    (``«Lean».«Parser».«Term».«typeAscription», «Lean».«Parser».«Term».«typeAscription»),
    (``«Lean».«Parser».«Term».«anonymousCtor», «Lean».«Parser».«Term».«anonymousCtor»),
    (``«Lean».«Parser».«Term».«hole», «Lean».«Parser».«Term».«hole»),
    (``«Lean».«Parser».«Term».«cdot», «Lean».«Parser».«Term».«cdot»),
    (``«Lean».«Parser».«Term».«proj», «Lean».«Parser».«Term».«proj»),
    (``«Lean».«Parser».«Term».«dotIdent», «Lean».«Parser».«Term».«dotIdent»),
    (``«Lean».«Parser».«Term».«pipeProj», «Lean».«Parser».«Term».«pipeProj»),
    (``«Lean».«Parser».«Term».«explicit», «Lean».«Parser».«Term».«explicit»),
    (``«Lean».«Parser».«Term».«namedArgument», «Lean».«Parser».«Term».«namedArgument»),
    (``«Lean».«Parser».«Term».«typeSpec», «Lean».«Parser».«Term».«typeSpec»),
    (``«Lean».«Parser».«Term».«explicitBinder», «Lean».«Parser».«Term».«explicitBinder»),
    (``«Lean».«Parser».«Term».«implicitBinder», «Lean».«Parser».«Term».«implicitBinder»),
    (``«Lean».«Parser».«Term».«instBinder», «Lean».«Parser».«Term».«instBinder»),
    (``«Lean».«Parser».«Term».«strictImplicitBinder»,
      «Lean».«Parser».«Term».«strictImplicitBinder»),
    (``«Lean».«Parser».«Term».«binderDefault», «Lean».«Parser».«Term».«binderDefault»),
    (``«Lean».«Parser».«Term».«type», «Lean».«Parser».«Term».«type»),
    (``«Lean».«Parser».«Term».«sort», «Lean».«Parser».«Term».«sort»),
    (``«Lean».«Parser».«Term».«prop», «Lean».«Parser».«Term».«prop»),
    (``«Lean».«Parser».«Term».«fun», «Lean».«Parser».«Term».«fun»),
    (``«Lean».«Parser».«Term».«basicFun», «Lean».«Parser».«Term».«basicFun»),
    (``«Lean».«Parser».«Term».«arrow», «Lean».«Parser».«Term».«arrow»),
    (``«Lean».«Parser».«Term».«depArrow», «Lean».«Parser».«Term».«depArrow»),
    (``«Lean».«Parser».«Term».«forall», «Lean».«Parser».«Term».«forall»),
    (``«Lean».«Parser».«Term».«let», «Lean».«Parser».«Term».«let»),
    (``«Lean».«Parser».«Term».«have», «Lean».«Parser».«Term».«have»),
    (``«Lean».«Parser».«Term».«letConfig», «Lean».«Parser».«Term».«letConfig»),
    (``«Lean».«Parser».«Term».«letDecl», «Lean».«Parser».«Term».«letDecl»),
    (``«Lean».«Parser».«Term».«letIdDecl», «Lean».«Parser».«Term».«letIdDecl»),
    (``«Lean».«Parser».«Term».«letPatDecl», «Lean».«Parser».«Term».«letPatDecl»),
    (``«Lean».«Parser».«Term».«letId», «Lean».«Parser».«Term».«letId»),
    (``«Lean».«Parser».«Term».«match», «Lean».«Parser».«Term».«match»),
    (``«Lean».«Parser».«Term».«matchDiscr», «Lean».«Parser».«Term».«matchDiscr»),
    (``«Lean».«Parser».«Term».«matchAlts», «Lean».«Parser».«Term».«matchAlts»),
    (``«Lean».«Parser».«Term».«matchAlt», «Lean».«Parser».«Term».«matchAlt»),
    (``«Lean».«Parser».«Term».«matchAltsWhereDecls», «Lean».«Parser».«Term».«matchAltsWhereDecls»),
    (``«Lean».«Parser».«Term».«structInst», «Lean».«Parser».«Term».«structInst»),
    (``«Lean».«Parser».«Term».«structInstFields»,
      «Lean».«Parser».«Term».«structInstFields» Lean.Parser.Term.structInstField),
    (``«Lean».«Parser».«Term».«structInstField», «Lean».«Parser».«Term».«structInstField»),
    (``«Lean».«Parser».«Term».«structInstLVal», «Lean».«Parser».«Term».«structInstLVal»),
    (``«Lean».«Parser».«Term».«structInstFieldDef», «Lean».«Parser».«Term».«structInstFieldDef»),
    (``«Lean».«Parser».«Term».«optEllipsis», «Lean».«Parser».«Term».«optEllipsis»),
    (``«Lean».«Parser».«Term».«quotedName», «Lean».«Parser».«Term».«quotedName»),
    (``«Lean».«Parser».«Term».«doubleQuotedName», «Lean».«Parser».«Term».«doubleQuotedName»),
    (``«Lean».«Parser».«Term».«do», «Lean».«Parser».«Term».«do»),
    (``«Lean».«Parser».«Term».«doSeqIndent», «Lean».«Parser».«Term».«doSeqIndent»),
    (``«Lean».«Parser».«Term».«doSeqItem», «Lean».«Parser».«Term».«doSeqItem»),
    (``«Lean».«Parser».«Term».«doExpr», «Lean».«Parser».«Term».«doExpr»),
    (``«Lean».«Parser».«Term».«doNested», «Lean».«Parser».«Term».«doNested»),
    (``«Lean».«Parser».«Term».«doLet», «Lean».«Parser».«Term».«doLet»),
    (``«Lean».«Parser».«Term».«doLetArrow», «Lean».«Parser».«Term».«doLetArrow»),
    (``«Lean».«Parser».«Term».«doIdDecl», «Lean».«Parser».«Term».«doIdDecl»),
    (``«Lean».«Parser».«Term».«doPatDecl», «Lean».«Parser».«Term».«doPatDecl»),
    (``«Lean».«Parser».«Term».«doLetElse», «Lean».«Parser».«Term».«doLetElse»),
    (``«Lean».«Parser».«Term».«doHave», «Lean».«Parser».«Term».«doHave»),
    (``«Lean».«Parser».«Term».«doReassign», «Lean».«Parser».«Term».«doReassign»),
    (``«Lean».«Parser».«Term».«letIdDeclNoBinders», «Lean».«Parser».«Term».«letIdDeclNoBinders»),
    (``«Lean».«Parser».«Term».«doReassignArrow», «Lean».«Parser».«Term».«doReassignArrow»),
    (``«Lean».«Parser».«Term».«doIf», «Lean».«Parser».«Term».«doIf»),
    (``«Lean».«Parser».«Term».«doIfProp», «Lean».«Parser».«Term».«doIfProp»),
    (``«Lean».«Parser».«Term».«doIfLet», «Lean».«Parser».«Term».«doIfLet»),
    (``«Lean».«Parser».«Term».«doIfLetPure», «Lean».«Parser».«Term».«doIfLetPure»),
    (``«Lean».«Parser».«Term».«doMatch», «Lean».«Parser».«Term».«doMatch»),
    (``«Lean».«Parser».«Term».«doFor», «Lean».«Parser».«Term».«doFor»),
    (``«Lean».«Parser».«Term».«doForDecl», «Lean».«Parser».«Term».«doForDecl»),
    (``«Lean».«Parser».«Term».«doUnless», «Lean».«Parser».«Term».«doUnless»),
    (``«Lean».«Parser».«Term».«doBreak», «Lean».«Parser».«Term».«doBreak»),
    (``«Lean».«Parser».«Term».«doContinue», «Lean».«Parser».«Term».«doContinue»),
    (``«Lean».«Parser».«Term».«doReturn», «Lean».«Parser».«Term».«doReturn»),
    (``«Lean».«Parser».«Term».«nestedAction», «Lean».«Parser».«Term».«nestedAction»),
    (``«Lean».«Parser».«Level».«num», «Lean».«Parser».«Level».«num»),
    (``«Lean».«Parser».«Level».«ident», «Lean».«Parser».«Level».«ident»),
    (``«Lean».«Parser».«Level».«addLit», «Lean».«Parser».«Level».«addLit»),
    (``«Lean».«Parser».«Level».«max», «Lean».«Parser».«Level».«max»),
    (``«Lean».«Parser».«Level».«imax», «Lean».«Parser».«Level».«imax»),
    (``«Lean».«Parser».«Level».«paren», «Lean».«Parser».«Level».«paren»),
    (``«Lean».«Parser».«Level».«hole», «Lean».«Parser».«Level».«hole»),
    (``«Lean».«Parser».«Termination».«suffix», «Lean».«Parser».«Termination».«suffix»),
    (``«Lean».«Parser».«Termination».«terminationBy»,
      «Lean».«Parser».«Termination».«terminationBy»),
    (``«Lean».«Parser».«Termination».«decreasingBy», «Lean».«Parser».«Termination».«decreasingBy»),
    (``«Lean».«Parser».«Tactic».«tacticSeq», «Lean».«Parser».«Tactic».«tacticSeq»),
    (``«Lean».«Parser».«Tactic».«tacticSeq1Indented»,
      «Lean».«Parser».«Tactic».«tacticSeq1Indented»)]

/-- A kind's name from its printed spelling (`String.toName` drops `term_+_`). -/
def kindName (k : String) : Lean.Name := (k.splitOn ".").foldl Lean.Name.mkStr .anonymous

def posText : Option Pos → String
  | some q => s!"{q.line}:{q.col}"
  | none => "-"

/-- `t` as lines with each occurrence's child-index path from the command root (U6 I3's declaring
slots + C1's walk read children by position): `<path> node <kind>` | `<path> atom <text> <l:c>` |
`<path> ident <name> <l:c>` | `<path> missing`. -/
partial def treeLines (path : List Nat) : Tree → List String
  | .node k _ kids =>
    let here := ".".intercalate (path.reverse.map toString)
    s!"{here}\tnode\t{dotted k}" :: (kids.zipIdx.flatMap fun (c, i) => treeLines (i :: path) c)
  | .atom t q => [s!"{".".intercalate (path.reverse.map toString)}\tatom\t{t}\t{posText q}"]
  | .ident n q =>
    [s!"{".".intercalate (path.reverse.map toString)}\tident\t{dotted n}\t{posText q}"]
  | .missing => [s!"{".".intercalate (path.reverse.map toString)}\tmissing"]

def run : List String → IO UInt32
  | "check" :: rest => FvdepDev.ProfileCheck.run rest
  | ["targets"] => FvdepDev.Witness.run ["targets"]
  | "differential" :: args@(_ :: _) => FvdepDev.Differential.run args
  | "witness" :: files@(_ :: _) => FvdepDev.Witness.run ("witness" :: files)
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
  | ["scoped", "--check"] => do
    -- P4's gate check (stage `profile-witness`): the live S over `[Init, Std]` (every admitted
    -- import lies in their closure) = the pinned `FvdepCore.Profile.scopedNamespaces`, as sets.
    let env ← FvdepDev.Parse.grammar [`Init, `Std]
    let st := Lean.Parser.parserExtension.ext.getState env
    let order := fun (a b : List String) => decide (dotted a ≤ dotted b)
    let live := (st.scopedEntries.map.toList.map fun e => FvdepDev.Parse.parts e.1).mergeSort order
    let pinned := FvdepCore.Profile.scopedNamespaces.mergeSort order
    if live == pinned then
      IO.println s!"same scoped {live.length} namespaces"
      return 0
    let liveOnly := (live.filter fun n => !pinned.contains n).map dotted
    let pinnedOnly := (pinned.filter fun n => !live.contains n).map dotted
    IO.println s!"differ scoped live-only {liveOnly} pinned-only {pinnedOnly}"
    return 1
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
  | "walk" :: args@(_ :: _) => FvdepDev.Walk.run args
  | "tokens" :: kinds@(_ :: _) => do
    -- K's worklist (contract U6 K0): each kind's parser (builtin `Parser` + `ParserDescr` alike,
    -- as the parser extension compiles them) → its `collectTokens`, sorted; nonreserved symbols
    -- (`max`, `structural`) are no tokens, so the owned-atom dumps stay the table.
    let env ← devGrammar
    let cats := (Lean.Parser.parserExtension.getState env).categories
    let mut rc : UInt32 := 0
    for k in kinds do
      try
        let p ←
          match builtinParsers.lookup (kindName k) with
          | some p =>
            pure p
          | none =>
            pure (← (Lean.Parser.mkParserOfConstant cats (kindName k)).run { env, opts := {} }).2
        let ts := (p.info.collectTokens []).toArray.qsort (· < ·)
        let ks := (p.info.collectKinds {}).toList.map (·.1.toString) |>.toArray.qsort (· < ·)
        IO.println s!"{k}\t{" ".intercalate ts.toList}\t{" ".intercalate ks.toList}"
      catch e =>
        IO.println s!"{k}\t<{e}>"
        rc := 1
    return rc
  | "tree" :: files@(_ :: _) => do
    let env ← devGrammar
    for f in files do
      IO.println s!"file\t{f}"
      match ← FvdepDev.Parse.parseModule env {} f (← IO.FS.readFile f) with
      | .ok ts =>
        for (t, i) in ts.zipIdx do
          IO.println s!"command\t{i}"
          for l in treeLines [] t do
            IO.println l
      | .error why =>
        IO.println s!"refused\t{why}"
    return 0
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
