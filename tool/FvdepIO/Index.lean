import FvdepCore.Index.Command
import FvdepIO.Sys
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.NoncomputableAttr
import Lean.CoreM
import Lean.Structure
import Lean.Util.CollectAxioms

/-! `fvdep index`'s observation effects (contract `docs/contracts/U4-library.md` C1 + C2 + C4 + C5;
ledger residue `lean-env`): a fresh snapshot build of the working copy's library in
`.lake/fvdep-index/<pid>/` (its own Lake package: the working copy's `lakefile.lean`, `.lake/` +
`LEAN_PATH` never enter; one directory per process, so concurrent runs never share a build), Lake's
lines relayed through the line rule, the library loaded by `importModules`, its raw observations
(`Facts`, axiom lists, record fields, the kernel's certificate verdicts), and the toolchain's
`leanchecker` replay. The pure plan (`FvdepCore.Index.Command`) decides; this module observes. -/

namespace FvdepIO.Index

open Lean System FvdepCore FvdepCore.Index FvdepCore.Index.Registry

/-- What the interpreter keeps between one run's effects: the run directory + the sysroot. -/
structure State where
  run : Option FilePath := none
  sysroot : Option FilePath := none

/-- `./<name>` through the persistence API (F2): `none` = absent. -/
def readHere (name : String) (cap : Nat) : IO (Except String (Option ByteArray)) := do
  match Sys.Path.ofString? ".", Sys.Name.ofString? name with
  | some d, some n =>
    return (← Sys.readFile d n cap).mapError Sys.SysError.reason
  | _, _ =>
    return .error s!"internal: {name} is no file name"

/-- C1 (1): a library working copy here (`lean-toolchain` + `Fvdep/Registry.lean`), + the bytes of
`lean-toolchain` (at most 64 KiB). -/
def probe : IO Response := do
  try
    if
        !(← (FilePath.mk "lean-toolchain").pathExists) ||
          !(← (FilePath.mk "Fvdep" / "Registry.lean").pathExists) then
      return .probe (.ok none)
    return .probe (← readHere "lean-toolchain" 65536)
  catch e =>
    return .probe (.error s!"{e}")

/-! ## The snapshot -/

/-- A library source the snapshot took: its path in the working copy, its bytes, + whether it sits
there as a regular file (C4: no link on the way, no hard-link alias). -/
structure Source where
  path : String
  bytes : ByteArray
  regular : Bool

/-- What the snapshot walks: the three root modules + the three source trees. -/
def roots : List String :=
  ["Fvdep.lean", "FvdepPreview.lean", "FvdepProofs.lean", "Fvdep", "FvdepPreview", "FvdepProofs"]

/-- The `.lean` files at or under `rel`, at most `fuel` directories deep: links followed for their
content (the build compiles what Lake would read) + marked irregular, each directory once by its
real path (no link cycle), special files never opened (no FIFO blocks the run). -/
def collect : Nat → String → Bool → StateT (Array String × Array Source) IO Unit
  | 0, _, _ => pure ()
  | fuel + 1, rel, regular => do
    let p : FilePath := rel
    let some (lm : IO.FS.Metadata) ←
      (try
            pure (some (← p.symlinkMetadata))
          catch _ =>
            pure none :
          IO _) | return
    let link := lm.type == .symlink
    let some (m : IO.FS.Metadata) ←
      (if link then
            try
              pure (some (← p.metadata))
            catch _ =>
              pure none
          else pure (some lm) :
          IO _) | return
    match m.type with
    | .dir =>
      let real := (← IO.FS.realPath p).toString
      if (← get).1.contains real then
        return
      modify fun s => (s.1.push real, s.2)
      for e in (← p.readDir).qsort (·.fileName < ·.fileName) do
        collect fuel (rel ++ "/" ++ e.fileName) (regular && !link)
    | .file =>
      if rel.endsWith ".lean" then
        let bytes ← IO.FS.readBinFile p
        modify fun s => (s.1, s.2.push ⟨rel, bytes, regular && !link && m.numLinks == 1⟩)
    | _ =>
      pure ()

/-- Every library source of the working copy, read once (C4: the framed bytes = the compiled
ones). -/
def snapshot : IO (Array Source) := do
  let mut st : Array String × Array Source := (#[], #[])
  for r in roots do
    st := (← (collect 64 r true).run st).2
  return st.2

/-- `.lake/fvdep-index/<pid>/`, fresh: a directory of that name belongs to a dead process. -/
def prepare : IO FilePath := do
  let run : FilePath := ".lake" / "fvdep-index" / toString (← IO.Process.getPID)
  if ← run.pathExists then
    IO.FS.removeDirAll run
  IO.FS.createDirAll run
  return run

/-- The build configuration: fvdep's qualified elaboration profile (C1: a change requalifies the
library) + the three libraries; Lake's artifact cache off. -/
def lakefile : String :=
  "name = \"fvdepindex\"\nenableArtifactCache = false\n\n[leanOptions]\n" ++
    "autoImplicit = false\nrelaxedAutoImplicit = false\nwarningAsError = true\n" ++
    "linter.extra.dupNamespace = true\nlinter.extra.unnecessarySeqFocus = true\n" ++
    "linter.extra.unreachableTactic = true\nlinter.extra.unusedDecidableInType = true\n" ++
    "linter.redundantVisibility = true\n\n[[lean_lib]]\nname = \"Fvdep\"\n\n" ++
    "[[lean_lib]]\nname = \"FvdepPreview\"\n\n[[lean_lib]]\nname = \"FvdepProofs\"\n"

/-- C1's clean environment: `PATH`, `HOME` (+ `ELAN_HOME`) alone (elan finds the toolchain), the
Lake system cache off, + `extra`. -/
def cleanEnv (extra : Array (String × Option String)) : IO (Array (String × Option String)) := do
  let mut env := #[]
  for k in ["PATH", "HOME", "ELAN_HOME"] do
    if let some v← IO.getEnv k then
      env := env.push (k, some v)
  return env ++ #[("LAKE_CACHE_DIR", some "")] ++ extra

/-- The text without trailing whitespace (a tool's line ends). -/
def chomp (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- One relayed tool line: to stderr through the line rule; the first `error:` line kept (C9 `Build
failed: <line>`, its `error: ` dropped). -/
def relayLine (first : IO.Ref (Option String)) (b : ByteArray) : IO Unit := do
  let s := Command.textOfBytes b
  let err ← IO.getStderr
  err.putStr (Command.line s)
  err.flush
  if (← first.get).isNone && s.startsWith "error: " then
    first.set (some (String.ofList (s.toList.drop 7)))

/-- `b`'s complete lines relayed; the unterminated rest returned. -/
def relayLines (first : IO.Ref (Option String)) (b : ByteArray) : IO ByteArray := do
  let mut start := 0
  for i in [0:b.size] do
    if b[i]! == 0x0A then
      relayLine first (b.extract start i)
      start := i + 1
  return b.extract start b.size

/-- A stream relayed line by line as it arrives (the last fragment at its end). -/
partial def relayStream (first : IO.Ref (Option String)) (h : IO.FS.Handle) (carry : ByteArray) :
    IO Unit := do
  let chunk ← h.read 65536
  if chunk.isEmpty then
    unless carry.isEmpty do
      relayLine first carry
  else
    relayStream first h (← relayLines first (carry ++ chunk))

/-- C1 (2): the sysroot (`lean --print-prefix` where the copied `lean-toolchain` pins it), then
Lake's build of the three libraries; Lake's stdout relayed live, its stderr after the exit. -/
def build (run : FilePath) (env : Array (String × Option String)) : IO (Except String FilePath) :=
  do
  let out ←
    IO.Process.output
        { cmd := "lean"
          args := #["--print-prefix"]
          cwd := run
          env
          inheritEnv := false }
  if out.exitCode != 0 then
    return .error s!"lean --print-prefix exited with code {out.exitCode}: {chomp out.stderr}"
  let sys : FilePath := chomp out.stdout
  let child ←
    IO.Process.spawn
        { cmd := (sys / "bin" / "lake").toString
          args := #["build", "Fvdep", "FvdepPreview", "FvdepProofs"]
          cwd := run
          env
          inheritEnv := false
          stdin := .null
          stdout := .piped
          stderr := .piped }
  let errTask ← IO.asTask child.stderr.readBinToEnd
  let first ← IO.mkRef none
  relayStream first child.stdout .empty
  let errBytes ← IO.ofExcept (← IO.wait errTask)
  let rest ← relayLines first errBytes
  unless rest.isEmpty do
    relayLine first rest
  let rc ← child.wait
  if rc == 0 then
    return .ok sys
  return .error ((← first.get).getD s!"lake exited with code {rc}")

/-! ## Observations -/

def kindOf : ConstantInfo → DeclKind
  | .defnInfo _ => .defn
  | .thmInfo _ => .thm
  | .axiomInfo _ => .axiom
  | .opaqueInfo _ => .opaque
  | .quotInfo _ => .quot
  | .inductInfo _ => .induct
  | .ctorInfo _ => .ctor
  | .recInfo _ => .recursor

/-- C2's libraries: modules whose first name component is `Fvdep` or `FvdepProofs`. -/
def libRoot (m : Name) : Bool := m.getRoot == `Fvdep || m.getRoot == `FvdepProofs

/-- The library modules (load order) with their data. -/
def libModules (env : Environment) : List (Name × ModuleData) :=
  (env.header.moduleNames.zip env.header.moduleData).toList.filter (libRoot ·.1)

/-- Every declaration of a library module, in module order, then each module's order. -/
def decls (env : Environment) : List Decl :=
  (libModules env).flatMap fun x =>
    x.2.constNames.toList.filterMap fun n =>
      (env.find? n).map fun ci =>
        { name := n
          module := x.1
          kind := kindOf ci
          value := ci.value?
          type := ci.type
          safety := if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe
          implementedBy := (Compiler.getImplementedBy? env n).isSome
          isExtern := isExtern env n
          isNoncomputable := isNoncomputable env n }

/-- C4: a module's snapshot bytes when its canonical path holds a regular file. -/
def fileOf (sources : Array Source) (m : Name) : Option ByteArray :=
  (sources.find? (·.path == Rules.modulePath m)).bind fun s =>
    if s.regular then some s.bytes else none

/-- C3 V2: the entry files on disk (`Fvdep/Registry/<Dep>/<Op>/V*.lean`). -/
def entryFiles (sources : Array Source) : List String :=
  sources.toList.filterMap fun s =>
    match s.path.splitOn "/" with
    | ["Fvdep", "Registry", _, _, f] =>
      if f.startsWith "V" && f.endsWith ".lean" then some s.path else none
    | _ => none

def runCore {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  let (a, _) ← x.toIO { fileName := "<fvdep index>", fileMap := default } { env }
  return a

/-- C5: each `FvdepProofs` theorem's axioms (`collectAxioms`; the registry never read here). -/
def axiomLists (env : Environment) (ds : List Decl) : IO (List (Name × List Name)) := do
  let mut out := []
  for d in ds do
    if d.kind == .thm && d.module.getRoot == `FvdepProofs then
      out := (d.name, (← runCore env (collectAxioms (m := CoreM) d.name)).toList) :: out
  return out.reverse

/-- C2: the registry record types' fields as the environment declares them. -/
def recordFields (env : Environment) : List (Name × Option (List String)) :=
  [``Fvdep.Registry.Types.V1.Module, ``Fvdep.Registry.Types.V1.Notice,
        ``Fvdep.Registry.Types.V1.Removed].map
    fun t =>
    (t, if isStructure env t then some ((getStructureFields env t).toList.map toString) else none)

/-- C2's certificate for list constant `c`: the literal type-checks (synchronous kernel API: Lean
4.35's `addDecl` logs a rejection, it never throws) at `c`'s type + is defeq to `c`. -/
def certify (env : Environment) (c : Name) (lit : Expr) : Bool :=
  match env.find? c, Kernel.check env {} lit with
  | some ci, .ok ty =>
    (match Kernel.isDefEq env {} ty ci.type with
      | .ok true => true
      | _ => false) &&
      match Kernel.isDefEq env {} lit (.const c []) with
      | .ok true => true
      | _ => false
  | _, _ => false

/-- C3 V5: the type of `shape spec` (`none` = ill-typed). -/
def abiType (env : Environment) (shape spec : Name) : Option Expr :=
  match Kernel.check env {} (.app (.const shape []) (.const spec [])) with
  | .ok t => some t
  | .error _ => none

/-- C3 V6: whether the two specs' types are kernel-defeq (`none` = a spec is missing). -/
def specsDefeq (env : Environment) (a b : Name) : Option Bool :=
  match env.find? a, env.find? b with
  | some x, some y =>
    some <|
      match Kernel.isDefEq env {} x.type y.type with
      | .ok r => r
      | .error _ => false
  | _, _ => none

/-- C1 (4): the raw observations. The kernel questions follow from the registry the facts denote
(read by the proved readers); a question not asked = no observation ⇒ `validate` refuses as load. -/
def observe (env : Environment) (sources : Array Source) : IO Observed := do
  let ds := decls env
  let mods :=
    (libModules env).map fun x =>
      { name := x.1, imports := x.2.imports.toList.map (·.module), file := fileOf sources x.1 }
  let F0 : Facts := ⟨ds, mods, entryFiles sources, [], []⟩
  let axs ← axiomLists env ds
  let fields := recordFields env
  match readRaw F0 with
  | .error _ =>
    return ⟨F0, axs, fields, []⟩
  | .ok r =>
    let l := Lists.ofRaw r
    let certified := (certificate r).map fun x => (x.1, certify env x.1 (listLiteral x.2.1 x.2.2))
    let abi := l.entries.filterMap fun e => e.abi.map fun a => ((a, e.spec), abiType env a e.spec)
    let dfq :=
      l.entries.filterMap fun e =>
        e.compat.bind fun c =>
          (Rules.listedAt? l e.id c).bind fun old =>
            (specsDefeq env e.spec old.spec).map ((e.spec, old.spec), ·)
    return ⟨{ F0 with
          abiType := abi, specDefeq := dfq },
        axs, fields, certified⟩

/-- C1 (2)–(4): snapshot (read once) + build, load, observe. -/
def libraryFacts (st : IO.Ref State) : IO Response := do
  let prepared ←
    (do
          let run ← prepare
          st.modify fun s => { s with run := some run }
          let sources ← snapshot
          for s in sources do
            let dest := run / s.path
            if let some parent := dest.parent then
              IO.FS.createDirAll parent
            IO.FS.writeBinFile dest s.bytes
          IO.FS.writeFile (run / "lakefile.toml") lakefile
          IO.FS.writeBinFile (run / "lean-toolchain") (← IO.FS.readBinFile "lean-toolchain")
          return (run, sources) : IO _).toBaseIO
  let (run, sources) ←
    match prepared with
    | .ok x =>
      pure x
    | .error e =>
      return .facts (.error (.build s!"could not prepare the build: {e}"))
  let sys ←
    match
      ←
        (do
              build run (← cleanEnv #[]) : IO _).toBaseIO with
    | .ok (.ok sys) =>
      pure sys
    | .ok (.error l) =>
      return .facts (.error (.build l))
    | .error e =>
      return .facts (.error (.build s!"could not run Lake: {e}"))
  st.modify fun s => { s with sysroot := some sys }
  match
    ←
      (do
            searchPathRef.set [run / ".lake" / "build" / "lib" / "lean", sys / "lib" / "lean"]
            let env ←
              importModules
                  #[{ module := `Fvdep }, { module := `FvdepPreview }, { module := `FvdepProofs }]
                  {}
            observe env sources : IO _).toBaseIO with
  | .ok o =>
    return .facts (.ok o)
  | .error e =>
    return .facts (.error (.load s!"{e}"))

/-- C1 (5): the toolchain's `leanchecker`, one process over the three libraries (prefixes); a
rejection names the module leanchecker reports + the first kernel line; anything else = failed. -/
def replay (st : IO.Ref State) : IO Response := do
  let s ← st.get
  let (some run, some sys) := (s.run, s.sysroot) | return .replay (.error "no built library")
  try
    let env ←
      cleanEnv
          #[("LEAN_SYSROOT", some sys.toString),
            ("LEAN_PATH", some (run / ".lake" / "build" / "lib" / "lean").toString)]
    let out ←
      IO.Process.output
          { cmd := (sys / "bin" / "leanchecker").toString
            args := #["Fvdep", "FvdepPreview", "FvdepProofs"]
            env
            inheritEnv := false }
    if out.exitCode == 0 then
      return .replay (.ok none)
    let ls := ((out.stdout ++ "\n" ++ out.stderr).splitOn "\n").map chomp |>.filter (!·.isEmpty)
    let tag := "leanchecker found a problem in "
    match ls.find? (·.startsWith tag) with
    | some l =>
      let after := (ls.dropWhile (· != l)).drop 1
      let k := (after.find? fun x => (x.splitOn "(kernel)").length > 1).getD (after.headD "")
      let k := if k.startsWith "uncaught exception: " then String.ofList (k.toList.drop 20) else k
      return .replay (.ok (some (String.ofList (l.toList.drop tag.length), k)))
    | none =>
      return .replay (.error s!"leanchecker exited with code {out.exitCode}: {ls.headD ""}")
  catch e =>
    return .replay (.error s!"{e}")

/-- `index.json`'s bytes (F2 `readFile`), `none` = absent. -/
def readIndex : IO Response := do
  try
    return .read (← readHere "index.json" Sys.Model.readCap)
  catch e =>
    return .read (.error s!"{e}")

/-- F2 `replace` of `index.json` (temp, fsync, rename, directory fsync). -/
def replaceIndex (b : ByteArray) : IO Response := do
  try
    match Sys.Path.ofString? ".", Sys.Name.ofString? "index.json" with
    | some d, some n =>
      return .replace ((← Sys.replace d n b).mapError Sys.SysError.reason)
    | _, _ =>
      return .replace (.error "internal: index.json is no file name")
  catch e =>
    return .replace (.error s!"{e}")

/-- C1: the run directory removed at the end (a killed run leaves it). -/
def cleanup (st : IO.Ref State) : IO Unit := do
  if let some run := (← st.get).run then
    try
      IO.FS.removeDirAll run
    catch _ =>
      pure ()

end FvdepIO.Index
