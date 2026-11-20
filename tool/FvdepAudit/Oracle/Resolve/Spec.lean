import FvdepCore.Oracle.Resolve

/-! Spec of the oracle's entry resolution (contract `docs/contracts/U5b-oracle.md` E1–E5), written
from the contract apart from `FvdepCore.Oracle.Resolve`: the target's row, the snapshot's
coherence, the expanded size C2's decoder may visit, the entry stage (export 1 → the spec constant)
+ the signature stage (export 2 → the protocol signature). Shared with the shipped code: the
claimed C2 decoder + record extraction (`decode`, `moduleForm`, `entryOf`), C4's entry frame
(`entryFrame`), `sigOf`, `trimText`, the module naming (`entryModule`, `leanModule`), the discovery
→ facts reading (`nameOf`, `factsOf`). -/

namespace FvdepAudit.Oracle.Resolve.Spec

open Lean FvdepCore FvdepCore.Ids FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Assemble FvdepCore.Oracle

/-- E1: an operation of `index.json` with the target's id + version. -/
def Listed (i : IndexFile) (m : ModuleId) (v : EntryVersion) (o : Operation) : Prop :=
  o ∈ i.operations ∧ o.id = m ∧ o.version = v

/-- E2: every module of `M`'s closure (C4) among the discovered modules (a closure module without
its source = a refusal; `M` is in its own closure), `index.json`'s toolchain = the tree's
`lean-toolchain` trimmed, the row's digest = `h` of C4's entry frame of `M`'s closure over the
discovery. -/
def Coherent (h : ByteArray → String) (tc : String) (i : IndexFile) (o : Operation) (M : Name)
    (srcs : List Src) : Prop :=
  (∀ n ∈ closure (factsOf srcs) M, ∃ s ∈ srcs, nameOf s.module = n) ∧
    i.toolchain = trimText tc ∧ o.digest = h (entryFrame (factsOf srcs) M)

/-- E5: the nodes C2's decoder may visit with no read-through facts: metadata, a `let` (its body
under the value), a bound variable (its `let` value, at every use) + an application are 1 + their
parts; any other node is 1. -/
def size (e : Expr) (env : List Expr) : Nat :=
  match e with
  | .mdata _ b => 1 + size b env
  | .letE _ _ v b _ => 1 + size b (v :: env)
  | .bvar i =>
    match hv : env[i]? with
    | some v =>
      have := env_le hv
      1 + size v (env.drop (i + 1))
    | none => 1
  | .app f a => 1 + size f env + size a env
  | _ => 1
termination_by sizeOf e + envSize env
decreasing_by all_goals (simp; omega)

/-- E3: the first declaration of export 1 named `<M>.entry` (`M` = the target's entry module). -/
def EntryDecl (m : ModuleId) (v : EntryVersion) (ds : List Export.Decl) (d : Export.Decl) : Prop :=
  ds.find? (fun x => x.name == .str (entryModule m v) "entry") = some d

/-- E3 + E5: the entry stage yields `spec` exactly when `<M>.entry` is a definition with a value
whose expanded size is within the budget, C2 reads that value (`moduleForm`, no read-through
facts) as a record naming the target's id + version + `spec` = `S.<fn>` (`S` the target's spec
module, `fn` one plain component), + `S` lies in `M`'s closure `mods`. -/
def EntryOk (budget : Nat) (m : ModuleId) (v : EntryVersion) (mods : List Name)
    (ds : List Export.Decl) (spec : Name) : Prop :=
  ∃ d val payload,
    EntryDecl m v ds d ∧
      d.kind = .defn ∧
      d.value = some val ∧
      size val [] ≤ budget ∧
      decode ⟨[], [], [], [], []⟩ moduleForm val [] [.str (entryModule m v) "entry"] = .ok payload ∧
      (entryOf (.entry (entryModule m v) payload)).id = toString m ∧
      (entryOf (.entry (entryModule m v) payload)).version = toString v ∧
      spec = (entryOf (.entry (entryModule m v) payload)).spec ∧
      (∃ fn, spec = .str (leanModule m v) fn ∧ FvdepCore.Manifest.isComponent fn.toList) ∧
      leanModule m v ∈ mods

/-- E5: the budget refusal — `<M>.entry` a definition with a value whose expanded size passes the
budget. -/
def EntryOver (budget : Nat) (m : ModuleId) (v : EntryVersion) (ds : List Export.Decl) : Prop :=
  ∃ d val, EntryDecl m v ds d ∧ d.kind = .defn ∧ d.value = some val ∧ budget < size val []

/-- A spec constant's last component (`""` for none: E3 hands E4 `S.<fn>` alone). -/
def lastPart : Name → String
  | .str _ s => s
  | _ => ""

/-- E4: the signature stage yields `sig` exactly when the first declaration of export 2 named
`spec` is a definition whose type `sigOf` reads as `sig`'s arguments + result, `sig.op` = the
spec's last component. -/
def SigOk (spec : Name) (ds : List Export.Decl) (sig : Protocol.Sig) : Prop :=
  ∃ d,
    ds.find? (fun x => x.name == spec) = some d ∧
      d.kind = .defn ∧ Protocol.sigOf d.type = some (sig.args, sig.result) ∧ sig.op = lastPart spec

/-- E4: the type refusal — the spec a definition whose type `sigOf` refuses. -/
def SigRefused (spec : Name) (ds : List Export.Decl) : Prop :=
  ∃ d, ds.find? (fun x => x.name == spec) = some d ∧ d.kind = .defn ∧ Protocol.sigOf d.type = none

end FvdepAudit.Oracle.Resolve.Spec
