import FvdepLedger.Types
import Lean

/-! Ledger checker (gate stage `coverage`; contract `docs/contracts/U2-core.md` L1–L7). Loads the
ledger module's environment from the build, decodes the ledger value from its elaborated term,
checks every row against that environment, replays the owned modules through the toolchain's
`leanchecker`, and renders `docs/verification.md` (`--write`) or compares it (`--check`). -/

open Lean

namespace FvdepLedger.Check

/-! ## Decoding literal ledger values -/

/-- Bound on nested references between ledger values (rows are shallow). -/
def fuel : Nat := 256

/-- A metadata wrapper dropped, a reference to another ledger value replaced by its definition. -/
def unfold (env : Environment) : Expr → Expr
  | .mdata _ e => e
  | e@(.const n _) =>
    match env.find? n with
    | some (.defnInfo d) => d.value
    | _ => e
  | e => e

def str (env : Environment) : Nat → Expr → Except String String
  | 0, _ => .error "ledger values nest too deeply"
  | f + 1, e =>
    match unfold env e with
    | .lit (.strVal s) => .ok s
    | e =>
      match e.getAppFn.constName?, e.getAppArgs with
      | some ``HAppend.hAppend, #[_, _, _, _, a, b] | some ``String.append, #[a, b] => do
        return (← str env f a) ++ (← str env f b)
      | _, _ => .error s!"not a string literal: {e}"

/-- `Lean.Name.mkStr1` … `mkStrN` = the elaborated form of a double-backtick name. -/
def isMkStrN : Name → Bool
  | .str ``Lean.Name s => s.startsWith "mkStr" && s.length > 5
  | _ => false

def name (env : Environment) : Nat → Expr → Except String Name
  | 0, _ => .error "ledger values nest too deeply"
  | f + 1, e =>
    let e := unfold env e
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Name.anonymous, #[] => .ok .anonymous
    | some ``Name.str, #[p, s] | some ``Name.mkStr, #[p, s] => do
      return .str (← name env f p) (← str env f s)
    | some c, args =>
      if isMkStrN c then do
        let parts ← args.toList.mapM (str env f)
        return parts.foldl Name.str .anonymous
      else .error s!"not a name literal: {e}"
    | none, _ => .error s!"not a name literal: {e}"

def list {α : Type} (env : Environment) (item : Expr → Except String α) :
    Nat → Expr → Except String (List α)
  | 0, _ => .error "ledger values nest too deeply"
  | f + 1, e =>
    let e := unfold env e
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``List.nil, #[_] => .ok []
    | some ``List.cons, #[_, h, t] => do
      return (← item h) :: (← list env item f t)
    | _, _ =>
      match e with
      -- A long list literal elaborates in chunks, each bound by a `have`.
      | .letE _ _ v b _ => list env item f (b.instantiate1 v)
      | _ => .error s!"not a list literal: {e}"

/-- The arguments of a structure literal built by `ctor` (`arity` fields, no parameters). -/
def fields (env : Environment) (ctor : Name) (arity : Nat) (e : Expr) :
    Except String (Array Expr) :=
  let e := unfold env e
  if e.getAppFn.constName? == some ctor && e.getAppNumArgs == arity then .ok e.getAppArgs
  else .error s!"not a {ctor} literal: {e}"

def residue (env : Environment) (e : Expr) : Except String Residue := do
  let a ← fields env ``Residue.mk 5 e
  return {
      id := ← str env fuel a[0]!
      what := ← str env fuel a[1]!
      reason := ← str env fuel a[2]!
      ruling := ← str env fuel a[3]!
      boundary := ← list env (name env fuel) fuel a[4]! }

/-- A `(statement, theorem)` pair literal. -/
def pair (env : Environment) (e : Expr) : Except String (Name × Name) :=
  let e := unfold env e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Prod.mk, #[_, _, a, b] => do
    return (← name env fuel a, ← name env fuel b)
  | _, _ => .error s!"not a pair literal: {e}"

def row (env : Environment) (e : Expr) : Except String Row := do
  let a ← fields env ``Row.mk 9 e
  let strs := list env (str env fuel) fuel
  let names := list env (name env fuel) fuel
  return {
      component := ← name env fuel a[0]!
      contract := ← str env fuel a[1]!
      claim := ← str env fuel a[2]!
      claims := ← list env (pair env) fuel a[3]!
      subject := ← name env fuel a[4]!
      path := ← names a[5]!
      noCaller := ← str env fuel a[6]!
      residue := ← strs a[7]!
      unproven := ← strs a[8]! }

def ledger (env : Environment) (e : Expr) : Except String Ledger := do
  let a ← fields env ``Ledger.mk 6 e
  return {
      main := ← name env fuel a[0]!
      interpreter := ← name env fuel a[1]!
      plan := ← name env fuel a[2]!
      libs := ← list env (name env fuel) fuel a[3]!
      rows := ← list env (row env) fuel a[4]!
      residue := ← list env (residue env) fuel a[5]! }

/-! ## The environment's code graph -/

def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

/-- fvdep's own modules: `Main` + every module under a root starting with `Fvdep`. -/
def ownedModule (m : Name) : Bool := m == `Main || m.getRoot.toString.startsWith "Fvdep"

def owned (env : Environment) (n : Name) : Bool := (moduleOf env n).any ownedModule

/-- Owned definitions reachable from `roots` (the roots included) through definition values;
theorem proofs are no executed code, so they are not followed. -/
def closure (env : Environment) (roots : List Name) : NameSet :=
  Id.run do
    let mut todo := roots.toArray
    let mut seen : NameSet := {}
    while h : todo.size > 0 do
      let c := todo[todo.size - 1]
      todo := todo.pop
      if seen.contains c || !owned env c then
        continue
      if let some (.defnInfo d) := env.find? c then
        seen := seen.insert c
        for u in d.value.getUsedConstants do
          unless seen.contains u do
            todo := todo.push u
      else
        if let some _ := env.find? c then
          seen := seen.insert c
    return seen

/-- Compiler + elaborator auxiliaries (matchers, `casesOn`/`recOn`/`brecOn`, `noConfusion`,
`_proof_` names): each sits in its parent's closure, so coverage reports the parent. -/
def auxiliary (env : Environment) (n : Name) : Bool :=
  n.isInternal || isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n

def mentions (e : Expr) (n : Name) : Bool := e.getUsedConstants.contains n

/-! ## Checks -/

/-- One finding: where (a row's component or `root`), its code (contract L8), the detail. -/
structure Finding where
  place : String
  code : String
  detail : String

def Finding.line (f : Finding) : String := s!"ledger: {f.place}: {f.code}: {f.detail}"

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `main`'s value = `fun a => interpreter (plan a)` (metadata ignored). -/
def rootShaped (l : Ledger) : Expr → Bool
  | .mdata _ e => rootShaped l e
  | .lam _ _ body _ =>
    match body.consumeMData with
    | .app (.const i _) arg =>
      match arg.consumeMData with
      | .app (.const p _) (.bvar 0) => i == l.interpreter && p == l.plan
      | _ => false
    | _ => false
  | _ => false

/-- A statement's proposition: the value of a `Prop` definition. -/
def statementOf (env : Environment) (n : Name) : Option Expr :=
  match env.find? n with
  | some (.defnInfo d) => if d.type == .sort .zero then some d.value else none
  | _ => none

/-- The spec's `## Decisions` section (rulings count only there; it may open the file). -/
def decisionsOf (spec : String) : String :=
  match ("\n" ++ spec).splitOn "\n## Decisions\n" with
  | [_, rest] => (rest.splitOn "\n## ").headD ""
  | _ => ""

/-- An open Tasks row for `unit` in the spec text (`- [ ] <unit> …`). -/
def openUnit (spec unit : String) : Bool :=
  !unit.isEmpty && (spec.splitOn "\n").any fun l => l.startsWith s!"- [ ] {unit} "

/-- L4: a path from the root to the subject whose every edge holds (`main` → interpreter or plan;
another edge = reachable + a statement of the row mentioning both ends). -/
def pathOk (env : Environment) (l : Ledger) (r : Row) : Bool :=
  let stmts := r.claims.filterMap fun c => statementOf env c.1
  r.path.head? == some l.main && r.path.getLast? == some r.subject &&
    (r.path.zip r.path.tail).all fun e =>
      if e.1 == l.main then e.2 == l.interpreter || e.2 == l.plan
      else (closure env [e.1]).contains e.2 && stmts.any fun s => mentions s e.1 && mentions s e.2

def compiledFlags (env : Environment) (c : Name) : List String :=
  let info := env.find? c
  (if (Compiler.getImplementedBy? env c).isSome then ["@[implemented_by]"] else []) ++
    (if isExtern env c then ["@[extern]"] else []) ++
    (if info.any ConstantInfo.isPartial then ["partial"] else []) ++
    (if info.any ConstantInfo.isUnsafe then ["unsafe"] else []) ++
    match info with
    | some (.opaqueInfo _) => ["opaque"]
    | _ => []

/-- L2–L5 for one ledger; `axioms` = each claim theorem's axioms (computed in `CoreM`). -/
def findings (env : Environment) (l : Ledger) (spec : String) (axioms : NameMap (Array Name)) :
    Array Finding :=
  Id.run do
    let mut out : Array Finding := #[]
    let root := "root"
    -- L4 root shape
    match env.find? l.main with
    | some (.defnInfo d) =>
      unless rootShaped l d.value do
        out := out.push ⟨root, "root", s!"{l.main} is not `fun a => {l.interpreter} ({l.plan} a)`"⟩
    | _ =>
      out := out.push ⟨root, "root", s!"{l.main} is not a definition"⟩
    let reach := closure env [l.main]
    -- Coverage counts definitions (constructors + types are data shapes); auxiliary ones (matchers,
    -- `_proof_`, `_eq_`) sit in their parent's closure.
    let code :=
      reach.toList.filter fun c =>
        c != l.main && !auxiliary env c && (env.find? c matches some (.defnInfo _))
    let residueIds := l.residue.map (·.id)
    -- L2 coverage
    let covered := closure env ((l.rows.map (·.subject)).filter (· != l.main))
    for c in code do
      unless covered.contains c do
        out := out.push ⟨root, "uncovered", s!"{c}: reachable, outside every row's subject"⟩
    let components := l.rows.map (·.component)
    let entries := closure env ((l.rows.filter (pathOk env l)).map (·.subject))
    let mut needRow : NameSet := {}
    for c in code do
      if let some m := moduleOf env c then
        needRow := needRow.insert m
    for (m, d) in env.header.moduleNames.zip env.header.moduleData do
      if l.libs.any (·.isPrefixOf m) then
        let defines :=
          d.constNames.any fun n => !auxiliary env n && (env.find? n matches some (.defnInfo _))
        if defines then
          needRow := needRow.insert m
    for m in needRow.toList do
      unless components.contains m do
        out := out.push ⟨root, "module", s!"{m} defines shipped code, is no row's component"⟩
    -- per row
    for r in l.rows do
      let place := toString r.component
      match env.find? r.subject with
      | none =>
        out := out.push ⟨place, "subject", s!"{r.subject} does not exist"⟩
      | some _ =>
        unless moduleOf env r.subject == some r.component do
          out := out.push ⟨place, "subject", s!"{r.subject} is not defined in {r.component}"⟩
      if r.subject == l.main then
        out := out.push ⟨place, "subject", s!"the root {l.main} is no row subject"⟩
      -- L3 claims
      let mut stmts : Array Expr := #[]
      for (st, th) in r.claims do
        match statementOf env st with
        | none =>
          out := out.push ⟨place, "statement", s!"{st} is not a Prop definition"⟩
        | some prop =>
          stmts := stmts.push prop
          match env.find? th with
          | some (.thmInfo t) =>
            let lps :=
              match env.find? st with
              | some ci => ci.levelParams
              | none => []
            unless t.type == prop && t.levelParams.length == lps.length do
              out := out.push ⟨place, "statement", s!"the type of {th} is not the statement {st}"⟩
            let bad := (axioms.find? th).getD #[] |>.filter (!stdAxioms.contains ·)
            unless bad.isEmpty do
              out := out.push ⟨place, "axiom", s!"{th} depends on {bad.toList}"⟩
          | _ =>
            out := out.push ⟨place, "theorem", s!"{th} is not a theorem"⟩
      if !r.claims.isEmpty && !stmts.any (mentions · r.subject) then
        out := out.push ⟨place, "about", s!"no statement of the row mentions {r.subject}"⟩
      if r.claims.isEmpty && r.unproven.isEmpty then
        out := out.push ⟨place, "waiver", "a row without claims needs an unproven residue id"⟩
      for i in r.residue ++ r.unproven do
        unless residueIds.contains i do
          out := out.push ⟨place, "residue", s!"{i} names no residue entry"⟩
      -- L4 path + noCaller
      if r.path.isEmpty then
        if r.noCaller == "support" then
          unless entries.contains r.subject do
            out :=
              out.push ⟨place, "nocaller", s!"support: {r.subject} under no row with a valid path"⟩
        else
          if r.noCaller.isEmpty then
            out := out.push ⟨place, "nocaller", "an empty path needs noCaller"⟩
          else
            unless openUnit spec r.noCaller do
              out := out.push ⟨place, "nocaller", s!"{r.noCaller} has no open Tasks row"⟩
          if reach.contains r.subject then
            out := out.push ⟨place, "nocaller", s!"{r.subject} is reachable: list its path"⟩
      else
        unless r.noCaller.isEmpty do
          out := out.push ⟨place, "nocaller", "a row with a path has no noCaller"⟩
        unless r.path.head? == some l.main && r.path.getLast? == some r.subject do
          out := out.push ⟨place, "path", s!"the path must run from {l.main} to {r.subject}"⟩
        for (a, b) in r.path.zip r.path.tail do
          if a == l.main then
            unless b == l.interpreter || b == l.plan do
              out := out.push ⟨place, "path", s!"{l.main} calls {l.interpreter} + {l.plan} alone"⟩
          else
            unless (closure env [a]).contains b do
              out := out.push ⟨place, "edge", s!"{b} is unreachable from {a}"⟩
            unless stmts.any fun s => mentions s a && mentions s b do
              out := out.push ⟨place, "edge", s!"no statement relates {a} to {b}"⟩
      -- L5 compiled = checked
      unless r.claims.isEmpty do
        let cited := r.residue ++ r.unproven
        let allowed := (l.residue.filter (cited.contains ·.id)).flatMap (·.boundary)
        let roots := r.subject :: r.path.filter fun p => p != l.main && p != l.interpreter
        for c in (closure env roots).toList do
          unless allowed.contains c do
            let flags := compiledFlags env c
            unless flags.isEmpty do
              out := out.push ⟨place, "compiled", s!"{c} is {", ".intercalate flags}"⟩
    -- L3 rulings
    let decisions := decisionsOf spec
    for e in l.residue do
      unless !e.ruling.isEmpty && (decisions.splitOn e.ruling).length > 1 do
        out := out.push ⟨root, "ruling", s!"residue {e.id}: its ruling is absent from Decisions"⟩
    return out

/-! ## Axioms, replay, rendering -/

/-- Statements print whole: deep terms never collapse to `⋯`. -/
def coreContext : Core.Context :=
  { fileName := "<ledger>", fileMap := default,
    options := ({} : Options).setBool `pp.deepTerms true }

def runCore {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  let (a, _) ← x.toIO coreContext { env }
  return a

/-- Each claim theorem's axioms. -/
def axiomsOf (env : Environment) (l : Ledger) : IO (NameMap (Array Name)) := do
  let mut m : NameMap (Array Name) := {}
  for r in l.rows do
    for (_, th) in r.claims do
      if env.find? th matches some (.thmInfo _) then
        m := m.insert th (← runCore env (collectAxioms (m := CoreM) th))
  return m

/-- L6: the toolchain's `leanchecker` with every owned module of `env` as a target. -/
def replay (env : Environment) : IO (Array Finding) := do
  let mods := env.header.moduleNames.filter ownedModule |>.map toString
  let bin := (← findSysroot) / "bin" / "leanchecker"
  let r ← IO.Process.output { cmd := bin.toString, args := mods }
  if r.exitCode == 0 then
    return #[]
  let strip (l : String) : String :=
    let cs := (l.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace
    String.ofList cs.reverse
  let lines := (r.stdout ++ "\n" ++ r.stderr).splitOn "\n" |>.map strip |>.filter (!·.isEmpty)
  let first := (lines.find? fun l => (l.splitOn "(kernel)").length > 1).getD (lines.headD "")
  return #[⟨"root", "replay", s!"leanchecker rc {r.exitCode}: {first}"⟩]

def hex (n : UInt64) : String := "0x" ++ String.ofList (Nat.toDigits 16 n.toNat)

def pp (env : Environment) (e : Expr) : IO String := do
  let f ← runCore env (Meta.MetaM.run' (Meta.ppExpr e))
  return f.pretty 100

def code (n : Name) : String := s!"`{n}`"

/-- L7: the doc's bytes. -/
def render (env : Environment) (l : Ledger) (decl : Name) : IO String := do
  let reason (i : String) : String :=
    match l.residue.find? (·.id == i) with
    | some e => s!"`{i}` ({e.what})"
    | none => s!"`{i}`"
  let ids (xs : List String) : String :=
    if xs.isEmpty then "none" else ", ".intercalate (xs.map reason)
  let mut out :=
    "# Coverage ledger (generated; agent-read)\n\n" ++
      s!"Generated by `fvdep-ledger --write` from `{decl}` (contract " ++
      "`docs/contracts/U2-core.md` L1–L8); gate stage `coverage` regenerates it + compares the " ++
      "bytes. Edit the rows, then run `bash tools/ledger-doc.sh`.\n\n" ++
      s!"Root: {code l.main} = {code l.interpreter} (interpreter) applied to {code l.plan} " ++
      "(shape checked).\n"
  for r in l.rows do
    out :=
      out ++ s!"\n## {code r.component}\n\n- Contract: {r.contract}\n- Claim: {r.claim}\n" ++
        s!"- Subject: {code r.subject}\n"
    out :=
      out ++
        if !r.path.isEmpty then s!"- Path: {" → ".intercalate (r.path.map code)}\n"
        else
          if r.noCaller == "support" then "- Path: none (a supporting component)\n"
          else s!"- Path: none yet (wired by {r.noCaller})\n"
    for (st, th) in r.claims do
      let prop := (statementOf env st).getD (.const st [])
      out :=
        out ++ s!"- Statement {code st} (hash {hex prop.hash}), proved by {code th}:\n\n" ++
          s!"  ```lean\n  {"\n  ".intercalate ((← pp env prop).splitOn "\n")}\n  ```\n"
    let cited := r.residue ++ r.unproven
    let boundary := (l.residue.filter (cited.contains ·.id)).flatMap (·.boundary)
    let uninterpreted := (closure env [r.subject]).toList.filter boundary.contains |>.map code
    let uninterpreted := if uninterpreted.isEmpty then "none" else ", ".intercalate uninterpreted
    out :=
      out ++ s!"- Uninterpreted: {uninterpreted}\n" ++
        s!"- Residue: {ids r.residue}\n- Unproven: {ids r.unproven}\n"
  out := out ++ "\n## Trusted residue\n\n"
  for e in l.residue do
    out := out ++ s!"- `{e.id}` — {e.what}: {e.reason} (ruling: \"{e.ruling}\")\n"
  return out

/-! ## Command line -/

structure Args where
  write : Bool
  doc : System.FilePath
  module : Name := `FvdepLedger.Rows
  ledger : Name := `FvdepLedger.Rows.ledger
  spec : System.FilePath := "../.agent/spec.md"

def usage : String :=
  "usage: fvdep-ledger (--check|--write) <doc> [--module <M>] [--ledger <decl>] [--spec <file>]"

def parse : List String → Option Args → Option Args
  | [], acc => acc
  | "--check" :: d :: rest, none => parse rest (some { write := false, doc := d })
  | "--write" :: d :: rest, none => parse rest (some { write := true, doc := d })
  | "--module" :: m :: rest, some a => parse rest (some { a with module := m.toName })
  | "--ledger" :: n :: rest, some a => parse rest (some { a with ledger := n.toName })
  | "--spec" :: f :: rest, some a => parse rest (some { a with spec := f })
  | _, _ => none

/-- The first line where `a` and `b` differ (1-based), when they differ. -/
def firstDiff (a b : String) : Option Nat :=
  let la := a.splitOn "\n"
  let lb := b.splitOn "\n"
  if a == b then none
  else
    let i := ((la.zip lb).findIdx? fun (x, y) => x != y).getD (min la.length lb.length)
    some (i + 1)

unsafe def main (argv : List String) : IO UInt32 := do
  let some a := parse argv none
    |
    IO.eprintln usage
    return 2
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ←
    try
      importModules #[{ module := a.module }] {} (loadExts := true)
    catch e =>
      IO.eprintln s!"ledger: usage: cannot load {a.module}: {e}"
      return 2
  let some ci := env.find? a.ledger
    |
    IO.eprintln s!"ledger: usage: {a.ledger} not found in {a.module}"
    return 2
  let some v := ci.value?
    |
    IO.eprintln s!"ledger: usage: {a.ledger} has no value"
    return 2
  let l ←
    match ledger env v with
    | .ok l =>
      pure l
    | .error e =>
      IO.eprintln s!"ledger: usage: {a.ledger} is not a literal ledger: {e}"
      return 2
  let spec ←
    try
      IO.FS.readFile a.spec
    catch e =>
      IO.eprintln s!"ledger: usage: cannot read {a.spec}: {e}"
      return 2
  let mut fs := findings env l spec (← axiomsOf env l)
  fs := fs ++ (← replay env)
  let text ← render env l a.ledger
  unless fs.isEmpty do
    for f in fs do
      IO.eprintln f.line
    return 1
  if a.write then
    IO.FS.writeFile a.doc text
    return 0
  let old ←
    try
      IO.FS.readFile a.doc
    catch _ =>
      pure ""
  match firstDiff old text with
  | none =>
    return 0
  | some n =>
    IO.eprintln s!"ledger: root: doc: {a.doc} differs from the ledger at line {n}; run --write"
    return 1

end FvdepLedger.Check
