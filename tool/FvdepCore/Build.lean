import FvdepCore.Ids
import FvdepCore.Json.Print

/-! The library build cache's pure parts (contract `docs/contracts/U5-sandbox.md` T2, K1, K2, K5,
K6): recipes, key preimages, the build plan over a module graph, the eviction policy, entry
validation. Hashing (`FvdepIO.Hash.sha256Hex`) + the filesystem = residue `cache-fs`. -/

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

/-- T2: the search path inside a step (library view, then phase 1's frozen artifacts, then this
phase's earlier modules). -/
def leanPath : List String := ["/fvdep/lib", "/fvdep/phase1", "/fvdep/prior"]

/-- T2: the environment of every compile (+ `LEAN_PATH`). -/
def compileEnv : List (String × String) :=
  [("PATH", "/fvdep/sysroot/bin:/usr/bin"), ("HOME", "/fvdep/work"), ("TMPDIR", "/tmp"),
    ("LC_ALL", "C")]

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

/-- T2 `library/1`: fvdep's qualified elaboration options for library modules (= `fvdep index`'s
build, `FvdepIO.Index.lakefile`). -/
def library (release fingerprint : String) : Recipe :=
  { id := "library/1"
    release
    fingerprint
    argv := ["lean"]
    leanPath
    env := compileEnv
    options :=
      ["autoImplicit=false", "relaxedAutoImplicit=false", "warningAsError=true",
        "linter.extra.dupNamespace=true", "linter.extra.unnecessarySeqFocus=true",
        "linter.extra.unreachableTactic=true", "linter.extra.unusedDecidableInType=true",
        "linter.redundantVisibility=true"]
    threads := 4 }

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

end FvdepCore.Build
