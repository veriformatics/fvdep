import FvdepCore.Ids
import FvdepCore.Json.Decode
import FvdepCore.Json.Print

/-! The library build cache's pure parts (contract `docs/contracts/U5-sandbox.md` T1–T3, K1, K2,
K5, K6): recipes, key preimages, the build plan over a module graph, the eviction policy, entry
validation + the manifest codec, the toolchain fingerprint's record. Hashing
(`FvdepIO.Hash.sha256Hex`) + the filesystem = residue `cache-fs`. -/

namespace FvdepCore.Build

open FvdepCore.Json

/-! ## T2 recipes -/

/-- T2: how a module compiles — identity, toolchain content, argv template, search path order,
environment, options, threads. Its JSON value enters every key (K1). -/
structure Recipe where
  id : String
  release : String
  fingerprint : String
  argv : List String
  leanPath : List String
  env : List (String × String)
  options : List String
  threads : Nat
  deriving DecidableEq, Repr

/-- T2's compile argv tail shared by both recipes (`lean` + module paths are added per module). -/
def compileFlags (r : Recipe) : List String :=
  ["--json", "-j", String.ofList (FvdepCore.Ids.decimal r.threads), "-R", "/fvdep/src"] ++
    r.options.flatMap fun o => ["-D", o]

/-- T2: the search path inside a step — the library view, then the check's consumer modules built so
far (phase 1's frozen artifacts + this phase's earlier ones, one directory: Lean resolves a module's
root component to the first entry holding it, so a namespace split across two entries loses its
later modules — measured: `SandboxTrial.Proof` in a second entry is "does not exist"). -/
def leanPath : List String := ["/fvdep/lib", "/fvdep/prior"]

/-- T2: the environment of every compile (+ `LEAN_PATH`). -/
def compileEnv : List (String × String) :=
  [("PATH", "/fvdep/sysroot/bin:/usr/bin"), ("HOME", "/fvdep/work"), ("TMPDIR", "/tmp"),
    ("LC_ALL", "C")]

/-- T2: a step's environment under recipe `r` — `r`'s variables, then `LEAN_PATH` = its search path
joined by `:` (R1 clears every other variable). -/
def stepEnv (r : Recipe) : List (String × String) :=
  r.env ++ [("LEAN_PATH", ":".intercalate r.leanPath)]

/-- T2 `consumer/1`: Lean's default options for consumer modules (U6 governs their syntax). -/
def consumer (release fingerprint : String) : Recipe :=
  { id := "consumer/1"
    release
    fingerprint
    argv := ["lean"]
    leanPath
    env := compileEnv
    options := []
    threads := 4 }

/-- The library's elaboration options (name, value): every build of its sources takes them —
`library/1` here, `fvdep index`'s (`FvdepIO.Index.lakefile`) + the root `lakefile.lean`'s
`leanOptions` (gate stage `meta` compares that copy). -/
def libraryOptions : List (String × String) :=
  [("autoImplicit", "false"), ("relaxedAutoImplicit", "false"), ("warningAsError", "true"),
    ("linter.extra.dupNamespace", "true"), ("linter.extra.unnecessarySeqFocus", "true"),
    ("linter.extra.unreachableTactic", "true"), ("linter.extra.unusedDecidableInType", "true"),
    ("linter.redundantVisibility", "true")]

/-- T2 `library/1`: `consumer/1` with the library's options (`libraryOptions`). -/
def library (release fingerprint : String) : Recipe :=
  { consumer release fingerprint with
    id := "library/1"
    options := libraryOptions.map fun o => o.1 ++ "=" ++ o.2 }

/-! ## K1 keys -/

/-- An import as the header observation records it (K2): its flags + the module name, + the key of
the entry that provides it (K1's import vector). -/
structure Import where
  module : String
  isPublic : Bool
  isMeta : Bool
  all : Bool
  key : String
  deriving DecidableEq, Repr

/-- K1: everything a compiled module depends on. `source` = the SHA-256 (hex) of the source bytes
the step compiles (read once). -/
structure KeyInput where
  recipe : Recipe
  module : String
  path : String
  source : String
  imports : List Import
  deriving DecidableEq, Repr

/-- The recipe as a JSON object (keys ascending: the canonical printer keeps member order). -/
def recipeValue (r : Recipe) : Value :=
  .obj
    [("argv", .arr (r.argv.map .str)), ("env", .arr (r.env.map fun e => .arr [.str e.1, .str e.2])),
      ("fingerprint", .str r.fingerprint), ("id", .str r.id),
      ("leanPath", .arr (r.leanPath.map .str)), ("options", .arr (r.options.map .str)),
      ("release", .str r.release), ("threads", .int r.threads)]

def importValue (i : Import) : Value :=
  .obj
    [("all", .bool i.all), ("key", .str i.key), ("meta", .bool i.isMeta), ("module", .str i.module),
      ("public", .bool i.isPublic)]

/-- K1's preimage as a JSON value (keys ascending at every level). -/
def keyValue (k : KeyInput) : Value :=
  .obj
    [("imports", .arr (k.imports.map importValue)), ("kind", .str "fvdep/build/1"),
      ("module", .str k.module), ("path", .str k.path), ("recipe", recipeValue k.recipe),
      ("source", .str k.source)]

/-- K1's preimage bytes: the canonical JSON text of `keyValue`. -/
def preimage (k : KeyInput) : ByteArray := print (keyValue k)

/-- K1: a module's key = `h` (SHA-256, lowercase hex: `FvdepIO.Hash.sha256Hex`) of its preimage. -/
def keyOf (h : ByteArray → String) (k : KeyInput) : String := h (preimage k)

/-! ## K2 the build plan -/

/-- A module of a build graph: its name + the modules it imports that the graph provides
(toolchain modules left out by the caller). -/
structure Node where
  name : String
  imports : List String
  deriving DecidableEq, Repr

/-- Why no build order exists (K2). -/
inductive Refusal where
  /-- Two nodes share a name. -/
  | duplicate (name : String)
  /-- A reached module that no node provides, + the module importing it (`none`: a root). -/
  | missing (importer : Option String) (target : String)
  /-- Modules each importing another of them (a cyclic dependency): nonempty. -/
  | stuck (modules : List String)
  deriving DecidableEq, Repr

def names (nodes : List Node) : List String := nodes.map (·.name)

/-- The imports of the node named `m` (`[]` when none is). -/
def importsOf (nodes : List Node) (m : String) : List String :=
  ((nodes.find? (·.name == m)).map (·.imports)).getD []

/-- Every name a plan can reach: the roots + every import. -/
def space (nodes : List Node) (roots : List String) : List String :=
  roots ++ nodes.flatMap (·.imports)

/-- The modules reachable from `todo`, each visited once, in visiting order after `seen`; each new
visit spends one unit of fuel (enough: `space`'s length + 1). -/
def reach (nodes : List Node) (fuel : Nat) (todo seen : List String) : List String :=
  match fuel, todo with
  | _, [] => seen
  | 0, _ :: _ => seen
  | f + 1, m :: rest =>
    if seen.contains m then reach nodes (f + 1) rest seen
    else reach nodes f (importsOf nodes m ++ rest) (seen ++ [m])
termination_by (fuel, todo.length)

/-- K2: the closure of `roots` under imports. -/
def closure (nodes : List Node) (roots : List String) : List String :=
  reach nodes ((space nodes roots).length + 1) roots []

/-- The first name `nodes` repeats. -/
def firstDuplicate : List String → Option String
  | [] => none
  | n :: rest => if rest.contains n then some n else firstDuplicate rest

/-- The first missing module of the closure `c`, with the first reached module importing it. -/
def firstMissing (nodes : List Node) (c : List String) : Option (Option String × String) :=
  match c.find? (fun m => !(names nodes).contains m) with
  | none => none
  | some t =>
    match c.find? (fun a => (names nodes).contains a && (importsOf nodes a).contains t) with
    | some a => some (some a, t)
    | none => some (none, t)

/-- Kahn's layering: each round appends, in `rem`'s order, every remaining module whose imports
are all done; a round with none ready → the remaining modules are stuck. `fuel` = rounds left
(enough: `rem`'s length). -/
def layer (nodes : List Node) : Nat → List String → List String → Except Refusal (List String)
  | _, [], done => .ok done
  | 0, rem@(_ :: _), _ => .error (.stuck rem)
  | f + 1, rem@(_ :: _), done =>
    let ready := rem.filter fun m => (importsOf nodes m).all done.contains
    if ready.isEmpty then .error (.stuck rem)
    else layer nodes f (rem.filter fun m => !ready.contains m) (done ++ ready)

/-- K2: a build order of the closure of `roots` — each module after all its imports — or why none
exists. -/
def plan (nodes : List Node) (roots : List String) : Except Refusal (List String) :=
  match firstDuplicate (names nodes) with
  | some n => .error (.duplicate n)
  | none =>
    let c := closure nodes roots
    match firstMissing nodes c with
    | some (a, t) => .error (.missing a t)
    | none => layer nodes c.length c []

/-! ## K5 eviction -/

/-- A cache entry as K5 observes it: key, charged bytes, use stamp, + whether a pin holds it. -/
structure Entry where
  key : String
  bytes : Nat
  used : Nat
  pinned : Bool
  deriving DecidableEq, Repr

/-- The (used, key) order: least recently used first, ties by key. -/
def before (a b : Entry) : Bool := a.used < b.used || (a.used == b.used && decide (a.key ≤ b.key))

/-- Take candidates in order while the total stays above the target. -/
def takeWhileOver (target : Nat) : Nat → List Entry → List String
  | _, [] => []
  | total, e :: rest =>
    if target < total then e.key :: takeWhileOver target (total - e.bytes) rest else []

/-- K5: the entries to evict — unpinned ones, least recently used first (ties by key), until the
total charged bytes is at most `target` or none is left. -/
def evictPlan (entries : List Entry) (target : Nat) : List String :=
  takeWhileOver target (entries.foldl (· + ·.bytes) 0)
    ((entries.filter (!·.pinned)).mergeSort before)

/-! ## K6 entry validation -/

/-- A file: its path in the entry, its size + SHA-256 (hex) — as a manifest lists an artifact, or
as the directory listing observes any file. -/
structure FileRec where
  path : String
  size : Nat
  sha256 : String
  deriving DecidableEq, Repr

/-- K6: an entry's manifest (schema 1): the key's inputs (so the key recomputes) + the artifacts. -/
structure Manifest where
  schema : Nat
  input : KeyInput
  artifacts : List FileRec
  deriving DecidableEq, Repr

/-- K6's two metadata files. -/
def metadata : List String := ["manifest.json", "used"]

/-- K6: the manifest is schema 1, its inputs hash to this entry's directory name, no artifact takes
a metadata file's name, both metadata files are present, every listed artifact is present with its
size + digest + no file is outside the artifacts + the two metadata files. -/
def validate (h : ByteArray → String) (dir : String) (m : Manifest) (files : List FileRec) : Bool :=
  m.schema == 1 && keyOf h m.input == dir && !(m.artifacts.map (·.path)).any metadata.contains &&
    metadata.all (fun n => files.any (·.path == n)) &&
    m.artifacts.all (fun a => files.any fun f => f == a) &&
    files.all fun f => metadata.contains f.path || (m.artifacts.map (·.path)).contains f.path

/-! ## K6 manifest codec -/

def fileValue (f : FileRec) : Value :=
  .obj [("path", .str f.path), ("sha256", .str f.sha256), ("size", .int f.size)]

/-- K6: `manifest.json`'s value (keys ascending at every level; `input` = K1's `keyValue`). -/
def manifestValue (m : Manifest) : Value :=
  .obj
    [("artifacts", .arr (m.artifacts.map fileValue)), ("input", keyValue m.input),
      ("schema", .int m.schema)]

/-- K6: `manifest.json`'s bytes = the canonical JSON text of `manifestValue`. -/
def manifestText (m : Manifest) : ByteArray := print (manifestValue m)

/-- An object's member values when its keys are exactly `keys`, in that (ascending) order. -/
def members (keys : List String) : Value → Option (List Value)
  | .obj ms => if ms.map (·.1) == keys then some (ms.map (·.2)) else none
  | _ => none

def natOf : Value → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none

def strOf : Value → Option String
  | .str s => some s
  | _ => none

def boolOf : Value → Option Bool
  | .bool b => some b
  | _ => none

def arrOf : Value → Option (List Value)
  | .arr xs => some xs
  | _ => none

def strsOf (v : Value) : Option (List String) := do
  (← arrOf v).mapM strOf

def pairOf : Value → Option (String × String)
  | .arr [.str k, .str v] => some (k, v)
  | _ => none

def recipeOf (v : Value) : Option Recipe := do
  let [argv, env, fingerprint, id, leanPath, options, release, threads] ←
    members ["argv", "env", "fingerprint", "id", "leanPath", "options", "release", "threads"]
        v | none
  pure {
        id := ← strOf id
        release := ← strOf release
        fingerprint := ← strOf fingerprint
        argv := ← strsOf argv
        leanPath := ← strsOf leanPath
        env := ← (← arrOf env).mapM pairOf
        options := ← strsOf options
        threads := ← natOf threads }

def importOf (v : Value) : Option Import := do
  let [all, key, isMeta, module, isPublic] ←
    members ["all", "key", "meta", "module", "public"] v | none
  pure {
        module := ← strOf module
        isPublic := ← boolOf isPublic
        isMeta := ← boolOf isMeta
        all := ← boolOf all
        key := ← strOf key }

/-- K6: `keyValue`'s inverse on its image. -/
def keyInputOf (v : Value) : Option KeyInput := do
  let [imports, kind, module, path, recipe, source] ←
    members ["imports", "kind", "module", "path", "recipe", "source"] v | none
  unless kind == .str "fvdep/build/1" do
    none
  pure {
        recipe := ← recipeOf recipe
        module := ← strOf module
        path := ← strOf path
        source := ← strOf source
        imports := ← (← arrOf imports).mapM importOf }

def fileOf (v : Value) : Option FileRec := do
  let [path, sha256, size] ← members ["path", "sha256", "size"] v | none
  pure {
        path := ← strOf path
        size := ← natOf size
        sha256 := ← strOf sha256 }

/-- K6's intake: the manifest `b` decodes to, accepted only when `b` is exactly its canonical text
(another spelling of the same value, an unknown or missing member → `none`: an entry with it is a
miss, rebuilt; like the step frame's status record, R8). -/
def manifestOf (b : ByteArray) : Option Manifest := do
  let v ← (FvdepCore.Json.decode b).toOption
  let [artifacts, input, schema] ← members ["artifacts", "input", "schema"] v | none
  let m : Manifest :=
    { schema := ← natOf schema
      input := ← keyInputOf input
      artifacts := ← (← arrOf artifacts).mapM fileOf }
  if manifestText m == b then
    some m
  else
    none

/-! ## T1 toolchain fingerprint -/

/-- T1: the fingerprint's preimage = the canonical JSON array `[[path, size, sha256]…]` of the
toolchain's files (`bin/lean`, `bin/leanexport`, every file under `lib/lean`) in path order (code
point order = UTF-8 byte order); the fingerprint = its SHA-256 (hex). -/
def fingerprintText (files : List FileRec) : ByteArray :=
  print
    (.arr
      ((files.mergeSort fun a b => decide (a.path ≤ b.path)).map fun f =>
        .arr [.str f.path, .int f.size, .str f.sha256]))

/-- T1: the toolchain tree's stat stamp (file count, total bytes, newest modification time as
seconds + nanoseconds: J's integers stop at 2^53 − 1); a change triggers a recompute. -/
structure Stamp where
  files : Nat
  bytes : Nat
  sec : Nat
  nsec : Nat
  deriving DecidableEq, Repr

/-- T1's record `FVDEP_CACHE/toolchains/v1/<release>.json`: the fingerprint of the toolchain whose
tree had this stamp. -/
structure Fingerprint where
  release : String
  value : String
  stamp : Stamp
  deriving DecidableEq, Repr

def fingerprintValue (f : Fingerprint) : Value :=
  .obj
    [("fingerprint", .str f.value), ("release", .str f.release), ("schema", .int 1),
      ("stamp",
        .obj
          [("bytes", .int f.stamp.bytes), ("files", .int f.stamp.files),
            ("nsec", .int f.stamp.nsec), ("sec", .int f.stamp.sec)])]

def fingerprintRecord (f : Fingerprint) : ByteArray := print (fingerprintValue f)

/-- T1's record intake: canonical text alone (anything else = no record: recompute). -/
def fingerprintOf (b : ByteArray) : Option Fingerprint := do
  let v ← (FvdepCore.Json.decode b).toOption
  let [value, release, schema, stamp] ←
    members ["fingerprint", "release", "schema", "stamp"] v | none
  unless schema == .int 1 do
    none
  let [bytes, files, nsec, sec] ← members ["bytes", "files", "nsec", "sec"] stamp | none
  let f : Fingerprint :=
    { release := ← strOf release
      value := ← strOf value
      stamp :=
        { files := ← natOf files
          bytes := ← natOf bytes
          sec := ← natOf sec
          nsec := ← natOf nsec } }
  if fingerprintRecord f == b then
    some f
  else
    none

/-! ## K3 + K5 cache settings -/

/-- K5's default soft target: 4 GiB (`@[noinline]`: a literal ≥ 2^32 is parsed at each use). -/
@[noinline]
def defaultCacheBytes : Nat := 4294967296

/-- T3's cache limits (U5 defaults; U7 qualifies the production values): a fill's own deadline
(seconds), the wait for a key's exclusive lock (seconds: past another process's whole fill), K5's
soft target (bytes; `FVDEP_CACHE_BYTES`, 0 allowed). -/
structure CacheLimits where
  fillBudget : Nat := 600
  lockWait : Nat := 660
  cacheBytes : Nat := defaultCacheBytes
  deriving DecidableEq, Repr

/-- K2: a module the toolchain provides — first component `Init`, `Std`, `Lean` or `Lake` (the
reserved consumer names, Decisions U2) — never a library entry: its key in an import vector = the
recipe's fingerprint. -/
def toolchainModule (m : String) : Bool :=
  ["Init", "Std", "Lean", "Lake"].contains ((m.splitOn ".").headD "")

/-- K7's trace line for one compiled module. -/
def traceLine (key module : String) : String := key ++ " " ++ module ++ "\n"

end FvdepCore.Build
