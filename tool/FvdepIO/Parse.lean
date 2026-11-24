import FvdepCore.Build
import FvdepCore.Json.Print
import FvdepCore.Profile.Batch
import FvdepIO.Sha256
import Lean.Elab.Import
import Lean.Parser.Module

/-! `fvdep-parse` (contract `docs/contracts/U6-profile.md` P1–P6; ledger residue `lean-parser`): the
bounded child of the profile step. It reads the request + the frozen batch at `/fvdep/src`, parses
each module with Lean's own parser in the trusted environment of its own grammar (P3: the
toolchain's modules at `/fvdep/sysroot` alone), converts each command to the profile's tree under
P6's caps + walks it (C), stopping at the batch's first event, then writes the record
(`/fvdep/work/out/results.json`). `ParseMain.main` = `main`. Everything that runs on a parsed,
uncapped `Syntax` is iterative: a left-nested chain (`a ++ a ++ …`, built by the trailing parser
loop without recursion) is as deep as its length. -/

namespace FvdepIO.Parse

open Lean FvdepCore.Profile

/-- A name's components in order (a numeric one printed). -/
def parts : Name → List String
  | .anonymous => []
  | .str p s => parts p ++ [s]
  | .num p n => parts p ++ [toString n]

/-- A dotted module name as a `Name` (each component one string: never `String.toName`'s parse). -/
def nameOf (m : String) : Name := (m.splitOn ".").foldl Name.mkStr .anonymous

/-- Lean's own file for module `n` (its components) under the search root `root`
(`modToFilePath`: the path `importModules` reads). -/
def oleanAt (root : System.FilePath) (n : List String) : System.FilePath :=
  modToFilePath root (n.foldl Name.mkStr .anonymous) "olean"

def posOf (fm : FileMap) (info : SourceInfo) : Option Pos :=
  info.getPos?.map fun p =>
    let q := fm.toPosition p
    ⟨q.line, q.column⟩

/-- C1's location of an occurrence: its first positioned leaf in pre-order (Lean's `getHeadInfo?`
recurses per level). -/
partial def firstPos (fm : FileMap) (stx : Syntax) : Option Pos := go [stx]
where go : List Syntax → Option Pos
    | [] => none
    | .atom info _ :: rest =>
      match posOf fm info with
      | some p => some p
      | none => go rest
    | .ident info .. :: rest =>
      match posOf fm info with
      | some p => some p
      | none => go rest
    | .node _ _ args :: rest => go (args.toList ++ rest)
    | .missing :: rest => go rest

/-- P5: whether a parsed tree holds a `missing` node (a recovered parse). -/
partial def hasMissing (stx : Syntax) : Bool := go [stx]
where go : List Syntax → Bool
    | [] => false
    | .missing :: _ => true
    | .node _ _ args :: rest => go (args.toList ++ rest)
    | _ :: rest => go rest

/-- P6's occurrence counters: this module's (its header included) + the batch's. -/
structure Counts where
  module : Nat
  batch : Nat

/-- A node under conversion: its kind, its children not yet visited, the trees of the visited ones,
the node itself (a cap's fallback location). -/
structure Frame where
  kind : List String
  rest : List Syntax
  done : Array Tree
  stx : Syntax

/-- The conversion's next move. -/
inductive Move where
  | visit (stx : Syntax)
  | attach (t : Tree)
  | advance

/-- A cap's finding at C1's location: the occurrence's first positioned leaf, else the nearest
enclosing occurrence's, else the command's start. -/
def capAt (fm : FileMap) (start : Pos) (stack : Array Frame) (stx : Syntax) (name : String)
    (n : Nat) : Event :=
  let p := (firstPos fm stx).getD ((stack.toList.reverse.findSome? (firstPos fm ·.stx)).getD start)
  .finding ⟨p, "cap", [name, toString n]⟩

/-- P6's conversion loop (one self tail call per move: a loop in the compiled code): each visited
occurrence counted in pre-order at depth = its frames + 1; past a cap: `batchNodes` (→ `over`)
before `depth` before `nodes` (→ `cap <name> <limit>`). -/
partial def loop (fm : FileMap) (lim : Limits) (start : Pos) (c : Counts) (stack : Array Frame) :
    Move → Except Event Tree × Counts
  | .visit stx =>
    let c := { module := c.module + 1, batch := c.batch + 1 }
    if lim.batchNodes < c.batch then (.error .over, c)
    else
      if lim.depth < stack.size + 1 then (.error (capAt fm start stack stx "depth" lim.depth), c)
      else
        if lim.nodes < c.module then (.error (capAt fm start stack stx "nodes" lim.nodes), c)
        else
          match stx with
          | .node _ k args =>
            loop fm lim start c (stack.push ⟨parts k, args.toList, #[], stx⟩) .advance
          | .atom info v => loop fm lim start c stack (.attach (.atom v (posOf fm info)))
          | .ident info _ n _ =>
            loop fm lim start c stack (.attach (.ident (parts n) (posOf fm info)))
          | .missing => loop fm lim start c stack (.attach .missing)
  | .attach t =>
    if stack.isEmpty then (.ok t, c)
    else
      loop fm lim start c (stack.modify (stack.size - 1) fun f => { f with done := f.done.push t })
        .advance
  | .advance =>
    match stack.back? with
    | none => (.error .over, c)
    | some f =>
      match f.rest with
      | s :: rest => loop fm lim start c (stack.set! (stack.size - 1) { f with rest }) (.visit s)
      | [] => loop fm lim start c stack.pop (.attach (.node f.kind f.done.toList))

/-- P6: a command (its root at depth 1) as the profile's tree under the caps, + the counters after
it; or its cap event. -/
def convert (fm : FileMap) (lim : Limits) (start : Pos) (c : Counts) (stx : Syntax) :
    Except Event Tree × Counts := loop fm lim start c #[] (.visit stx)

/-- Lean's first error in `log` (P5): its position + its first line, without the
`file:line:col: error:` prefix. -/
def firstError (log : MessageLog) : IO (Option Finding) := do
  match log.toList.find? (·.severity == .error) with
  | some m =>
    let t ← m.data.toString
    return some ⟨⟨m.pos.line, m.pos.column⟩, "parse", [(t.splitOn "\n").headD t]⟩
  | none =>
    return none

def parseAt (p : Pos) (why : String) : Event := .finding ⟨p, "parse", [why]⟩

/-- P5: a module's header (a command at 1:0) → its item, the parser state after it + the counters;
a parse failure or a cap = its stop. -/
def headItem (lim : Limits) (c : Counts) (input : Parser.InputContext) :
    IO (Item × Option Parser.ModuleParserState × Counts) := do
  let (h, st, log) ← Parser.parseHeader input
  match ← firstError log with
  | some f =>
    return (.stop (.finding f), none, c)
  | none =>
    if hasMissing h.raw then
      return (.stop (parseAt ⟨1, 0⟩ "a node is missing"), none, c)
    match convert input.fileMap lim ⟨1, 0⟩ c h.raw with
    | (.ok t, c') =>
      return (.tree t ⟨1, 0⟩, some st, c')
    | (.error e, c') =>
      return (.stop e, none, c')

/-- P5: a module's body under its grammar, command by command, each converted (P6) + folded into the
body stage's state (`step`) until its first event or the input's actual end (`true`). Structural on
`fuel` (≥ the input's bytes + 1: every command consumes a byte, else it stops as `no progress`), so
the ledger's closure sees the walk on the child's path (a `partial def` = an opaque constant). -/
def bodyLoop (env : Environment) (opts : Options) (input : Parser.InputContext) (s : Subject)
    (lim : Limits) (pst : Parser.ModuleParserState) (c : Counts) (st : State) :
    Nat → IO (State × Bool × Counts)
  | 0 => return (st, false, c)
  | fuel + 1 => do
    let q := input.fileMap.toPosition pst.pos
    let here : Pos := ⟨q.line, q.column⟩
    let (cmd, pst', log) := Parser.parseCommand input { env, options := opts } pst {}
    match ← firstError log with
    | some f =>
      return (step s st (.stop (.finding f)), false, c)
    | none =>
      if cmd.isOfKind ``Parser.Command.eoi then
        if input.atEnd pst'.pos then
          return (st, true, c)
        let e := input.fileMap.toPosition pst'.pos
        return (step s st
              (.stop
                (parseAt ⟨e.line, e.column⟩ "the input continues after the end of the module")),
            false, c)
      if pst'.pos == pst.pos then
        return (step s st (.stop (parseAt here "the parser made no progress")), false, c)
      if hasMissing cmd then
        return (step s st (.stop (parseAt here "a node is missing")), false, c)
      let (r, c') := convert input.fileMap lim here c cmd
      let st' :=
        step s st
          (match r with
          | .ok t => .tree t here
          | .error e => .stop e)
      if st'.event.isSome then
        return (st', false, c')
      bodyLoop env opts input s lim pst' c' st' fuel

/-- P3's parse options = the role's recipe (U5 T2): `consumer/1` = Lean's defaults, `library/1` =
the library's options (none of them changes the parse; P3 holds them anyway). -/
def optionsOf : Role → Options
  | .consumer => {}
  | .library =>
    FvdepCore.Build.libraryOptions.foldl
      (fun o x =>
        match x.2 with
        | "true" => o.setBool (nameOf x.1) true
        | "false" => o.setBool (nameOf x.1) false
        | v => o.insert (nameOf x.1) (.ofString v))
      {}

/-- C1 + P5's ruling: bytes that are not UTF-8 refuse at the module's header (1:0). -/
def notUtf8 : Event := parseAt ⟨1, 0⟩ "the source is not UTF-8"

/-- I1's presence (P5): after the pure header rules, the first import in source order naming a
toolchain module the toolchain does not hold (`holds`) → `header import <name>` at the import's
location (C1, as the pure rules' import findings). Read before any grammar loads: a missing module
is the consumer's own refusal (U5 K2's `absent`), never a failed load (infrastructure). -/
def presence (holds : List String → IO Bool) (h : Tree) : IO (Option Finding) := do
  let some (_, _, imps) := headerParts h | return none
  for t in imps do
    if let some (_, n, _) := importParts t then
      if toolchainModule (dotted n) then
        unless ← holds n do
          return found (locate ⟨1, 0⟩ t [.node ["null"] imps, h]) "header" ["import", dotted n]
  return none

/-- The batch as the child observes it, in C1's order: every module's header (the header stage,
until its first event: the pure rules, then `presence`), then — the stage clean — each module's
body under its grammar (`load` builds a grammar's environment, once per distinct list) until the
batch's first event. A module past that event stays unobserved. -/
def observe (load : List String → IO Environment) (holds : List String → IO Bool) (req : Request)
    (texts : List (ReqModule × ByteArray)) : IO (List Observed) := do
  let lib := req.library.map (·.module)
  let batch := req.modules.map (·.module)
  let lim := req.limits
  let mut total := 0
  let mut stopped := false
  let mut heads :
    Array (Observed × Option (Parser.InputContext × Parser.ModuleParserState) × Nat) := #[]
  for (m, bytes) in texts do
    let blank : Observed := ⟨m.module, none, State.init, false⟩
    if stopped then
      heads := heads.push (blank, none, 0)
    else
      match String.fromUTF8? bytes with
      | none =>
        heads := heads.push ({ blank with head := some (.stop notUtf8) }, none, 0)
        stopped := true
      | some text =>
        let input := Parser.mkInputContext text m.path
        let (item, pst, c) ← headItem lim ⟨0, total⟩ input
        total := c.batch
        let item ←
          match item with
          | .tree h _ =>
            if (headEvent req.role lib batch m.module item).isSome then
              pure item
            else
              match ← presence holds h with
              | some f =>
                pure (.stop (.finding f))
              | none =>
                pure item
          | .stop _ =>
            pure item
        heads := heads.push ({ blank with head := some item }, pst.map (input, ·), c.module)
        if (headEvent req.role lib batch m.module item).isSome then
          stopped := true
  let obs := heads.toList.map (·.1)
  if stopped then
    return obs
  let gs := grammars req obs
  let opts := optionsOf req.role
  let mut envs : List (List String × Environment) := []
  let mut out : Array Observed := #[]
  for ((o, parsed, count), g) in heads.toList.zip gs do
    match stopped, parsed with
    | false, some (input, pst) =>
      let env ←
        match envs.lookup g with
        | some e =>
          pure e
        | none =>
          let e ← load g
          envs := envs ++ [(g, e)]
          pure e
      let (st, ended, c) ←
        bodyLoop env opts input ⟨req.role, rootOf o.module⟩ lim pst ⟨count, total⟩ State.init
            (input.inputString.utf8ByteSize + 2)
      total := c.batch
      out :=
        out.push
          { o with
            state := st, ended }
      if st.event.isSome then
        stopped := true
    | _, _ =>
      out := out.push o
  return out.toList

/-! ## The child process -/

def srcDir : System.FilePath := "/fvdep/src"

def outFile : System.FilePath := "/fvdep/work/out/results.json"

/-- P2: the toolchain's modules at the step's sysroot alone (never `findSysroot`, `LEAN_PATH` or a
project artifact). -/
def sysrootLib : System.FilePath := "/fvdep/sysroot/lib/lean"

/-- `load`'s body: initializers enabled first (`importModules (loadExts := true)` runs the imported
extensions' initial states through the interpreter: Lean's own toolchain code). -/
unsafe def loadImpl (mods : List String) : IO Environment := do
  enableInitializersExecution
  searchPathRef.set [sysrootLib]
  importModules (mods.map fun m => { module := nameOf m }).toArray {} (loadExts := true)

/-- P3: a grammar's environment — the toolchain modules `mods`, their parser extensions loaded. -/
@[implemented_by loadImpl]
opaque load (mods : List String) : IO Environment

/-- The child's argv: none (its inputs + output are the step's layout). -/
def plan (args : List String) : Except String Unit :=
  if args.isEmpty then .ok () else .error "usage: fvdep-parse (no arguments)"

def fail (code : UInt32) (why : String) : IO UInt32 := do
  IO.eprintln s!"fvdep-parse: {why}"
  return code

/-- P5a → P5b: the request read canonical-only (3), each source's digest = the request's (4), the
batch observed + decided (5: the observations do not cover the batch), the record written. -/
def execute : Except String Unit → IO UInt32
  | .error m => fail 2 m
  | .ok () => do
    let reqBytes ← IO.FS.readBinFile (srcDir / "request.json")
    let some req := readRequest reqBytes | fail 3 "the request is not a canonical request"
    let mut texts := #[]
    let mut shas := #[]
    for m in req.modules do
      let bytes ← IO.FS.readBinFile (srcDir / m.path)
      let d := FvdepIO.Hash.sha256Hex bytes
      if d != m.sha256 then
        return ← fail 4 s!"{m.path} differs from its digest in the request"
      texts := texts.push (m, bytes)
      shas := shas.push d
    let obs ← observe load (fun n => (oleanAt sysrootLib n).pathExists) req texts.toList
    let some (o, gs) := conclude req obs | fail 5 "the observations do not cover the batch"
    let r := assemble req (FvdepIO.Hash.sha256Hex reqBytes) shas.toList o gs
    IO.FS.writeBinFile outFile (FvdepCore.Json.print r.toJson)
    return 0

def main (args : List String) : IO UInt32 := execute (plan args)

end FvdepIO.Parse
