import FvdepCore.Export
import FvdepCore.Index.Assemble
import FvdepCore.Index.Doc
import FvdepCore.Manifest
import FvdepCore.Plan
import FvdepCore.Protocol.Sig

/-! The oracle's entry resolution (contract `docs/contracts/U5b-oracle.md` E1–E5), pure: the target
grammar, the target's `index.json` row, the snapshot's coherence over K's discovery, the entry
(export 1) → the spec constant, the spec (export 2) → its protocol signature. A refusal = its class;
the reason text = tested presentation. -/

namespace FvdepCore.Oracle

open Lean FvdepCore.Ids FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Assemble

/-! ## E1 targets + rows -/

/-- `oracle`'s target: an operation `<id>@<x.y.z>`, or a profile `<eco>:<pkg>@<ver>` (U10 defines
profiles; index schema 1 lists none, so every profile target is absent). -/
inductive Target where
  | op (id : ModuleId) (version : EntryVersion)
  | profile (text : String)
  deriving DecidableEq, Repr

/-- A profile target's package + version characters (provisional until U10: npm scopes + names,
crate + PyPI names, SemVer + PEP 440 versions). -/
def profileChar (c : Char) : Bool := c.isAlphanum || ['@', '/', '.', '_', '~', '+', '-'].contains c

/-- `<eco>:<pkg>@<ver>`: `eco` = one id segment; `pkg` + `ver` nonempty, of profile characters,
split at the last `@` (an npm scope keeps its own). -/
def profileShape (cs : List Char) : Bool :=
  match cs.dropWhile (· != ':') with
  | ':' :: rest =>
    let ver := rest.reverse.takeWhile (· != '@')
    let pkg := (rest.reverse.dropWhile (· != '@')).drop 1
    (Seg.parse (cs.takeWhile (· != ':'))).isSome && rest.all profileChar && !ver.isEmpty &&
      !pkg.isEmpty
  | _ => false

/-- E1's grammar: an operation reference with its version, else a profile shape. -/
def Target.parse (s : String) : Option Target :=
  match ModuleRef.parse s with
  | some ⟨m, some v⟩ => some (.op m v)
  | some ⟨_, none⟩ => none
  | none => if profileShape s.toList then some (.profile s) else none

def Target.text : Target → String
  | .op m v => toString (ModuleRef.mk m (some v))
  | .profile s => s

/-- E1: the target's row among `index.json`'s operations (a removed record is none; a notice
removes none). -/
def rowOf (i : IndexFile) (m : ModuleId) (v : EntryVersion) : Option Operation :=
  i.operations.find? fun o => o.id == m && o.version == v

/-! ## E2 coherence over K's discovery -/

/-- A dotted module name as a `Name` (K reads plain module names alone). -/
def nameOf (s : String) : Name := (s.splitOn ".").foldl Name.str .anonymous

/-- K2's discovery as C4's facts: each module with its imports + its source file; no declaration. -/
def factsOf (srcs : List Src) : Facts :=
  { decls := []
    modules :=
      srcs.map fun s =>
        { name := nameOf s.module
          imports := s.imports.map nameOf
          file := some s.bytes }
    entryFiles := []
    abiType := []
    specDefeq := [] }

/-- E2: the snapshot's coherence for the target's row `o` with entry module `M`: every module of
`M`'s closure (C4: `M` + the `Fvdep` modules its header graph reaches) among K's discovered modules
(C4: a closure module without its source = a refusal), `index.json`'s toolchain = the tree's
`lean-toolchain` trimmed, the row's digest = `h` of C4's entry frame over that closure (another
discovery root never enters it). `none` = coherent; else the first failure's reason. -/
def coherence (h : ByteArray → String) (treeToolchain : String) (i : IndexFile) (o : Operation)
    (M : Name) (srcs : List Src) : Option String :=
  match (closure (factsOf srcs) M).find? fun n => !srcs.any fun s => nameOf s.module == n with
  | some n => some s!"{n}, in the closure of the entry module {M}, has no source"
  | none =>
    if i.toolchain != trimText treeToolchain then
      some s!"index.json names {i.toolchain}, lean-toolchain names {trimText treeToolchain}"
    else
      let d := h (entryFrame (factsOf srcs) M)
      if d != o.digest then
        some s!"the entry {o.id}@{o.version} hashes to {d}, index.json lists {o.digest}"
      else none

/-! ## E3–E5 the entry + the spec -/

/-- E3–E5's refusals beyond E1 + E2. -/
inductive Why where
  /-- The snapshot contradicts itself (E3, E4's shape). -/
  | inconsistent (reason : String)
  /-- E5: the entry value's expanded size passes the budget. -/
  | budget
  /-- E4: `sigOf` refuses the spec's type. -/
  | cannotCarry
  deriving DecidableEq, Repr

/-- E5: `k` less the nodes C2's decoder may visit in `e` under the `let` values `env` (the
zeta-expanded tree: a `let` value counted at each use, metadata + applications included), `none`
once that count passes `k` — at most `k + 1` steps, whatever the export shares. -/
def within (k : Nat) (e : Expr) (env : List Expr) : Option Nat :=
  match k with
  | 0 => none
  | k + 1 =>
    match e with
    | .mdata _ b => within k b env
    | .letE _ _ v b _ => within k b (v :: env)
    | .bvar i =>
      match hv : env[i]? with
      | some v =>
        have := env_le hv
        within k v (env.drop (i + 1))
      | none => some k
    | .app f a =>
      match within k f env with
      | some k' => within k' a env
      | none => none
    | _ => some k
termination_by sizeOf e + envSize env
decreasing_by all_goals (simp; omega)

/-- C2's reading of an entry value with no read-through constant (a constant to unfold =
refused). -/
def noFacts : Facts := ⟨[], [], [], [], []⟩

/-- E3 + E5: export 1's declarations → the spec constant `S.<fn>`: `M.entry` a definition with a
value, its expanded size within `budget`, decoded by C2 (`moduleForm`, no read-through facts) to a
record naming the target's id + version + a spec `S.<fn>` (`fn` one plain component) whose module
`S` lies in `M`'s closure `mods`. -/
def entrySpec (budget : Nat) (m : ModuleId) (v : EntryVersion) (mods : List Name)
    (ds : List Export.Decl) : Except Why Name :=
  let M := entryModule m v
  let S := leanModule m v
  let c := Name.str M "entry"
  match ds.find? (·.name == c) with
  | none => .error (.inconsistent s!"export 1 declares no {c}")
  | some d =>
    match d.kind, d.value with
    | .defn, some val =>
      match within budget val [] with
      | none => .error .budget
      | some _ =>
        match decode noFacts moduleForm val [] [c] with
        | .error n => .error (.inconsistent s!"{c} uses a form fvdep cannot read: {n}")
        | .ok payload =>
          let e := entryOf (.entry M payload)
          if e.id != toString m then .error (.inconsistent s!"{c} names the id {e.id}")
          else
            if e.version != toString v then
              .error (.inconsistent s!"{c} names the version {e.version}")
            else
              match e.spec with
              | .str p fn =>
                if p == S && FvdepCore.Manifest.isComponent fn.toList then
                  if mods.contains S then .ok e.spec
                  else .error (.inconsistent s!"{M} does not import {S}")
                else .error (.inconsistent s!"{c} names the spec {e.spec}, not {S}.<fn>")
              | n => .error (.inconsistent s!"{c} names the spec {n}, not {S}.<fn>")
    | _, _ => .error (.inconsistent s!"{c} is not a definition")

/-- A spec constant's function name (its last component). -/
def fnOf : Name → String
  | .str _ s => s
  | _ => ""

/-- E4: export 2's declarations → the spec's protocol signature (`op` = its function name): the
spec a definition whose type `sigOf` reads. -/
def specSig (spec : Name) (ds : List Export.Decl) : Except Why Protocol.Sig :=
  match ds.find? (·.name == spec) with
  | none => .error (.inconsistent s!"export 2 declares no {spec}")
  | some d =>
    if d.kind != .defn then .error (.inconsistent s!"{spec} is not a definition")
    else
      match Protocol.sigOf d.type with
      | some (args, r) => .ok ⟨fnOf spec, args, r⟩
      | none => .error .cannotCarry

end FvdepCore.Oracle
