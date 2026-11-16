import FvdepAudit.Index.Assemble.Spec
import FvdepCore.Index.Command

/-! `fvdep index [--check]` written apart (contract `docs/contracts/U4-library.md` C1 + C9): a
complete run as a relation over the observation answers, stage by stage in C9's order — library
presence, toolchain (`Trimmed`), build, load, registry form, certificate, entry rules, replay,
statuses + warnings, schema — then the one file effect. Messages + record fields are written here
from C9 + A2. Shared with the shipped code: the claimed functions (`readRaw`, `Lists.ofRaw`,
`certificate`, `validate`, `assemble`, `IndexFile.ofJson`, `encodeIndex`), the tested presentation
(`escapeControls`, `render`, `Warning.render`, `DocError.render`), the effect vocabulary. -/

namespace FvdepAudit.Index.Command.Spec

open Lean FvdepCore FvdepCore.Doc FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses FvdepCore.Index.Assemble FvdepAudit.Index.Assemble.Spec

/-- Interface §1's line rule: each message on its own line, control characters escaped. -/
def Out (ms : List String) : String := String.join (ms.map fun m => escapeControls m ++ "\n")

/-- `lean-toolchain`'s text: its UTF-8 reading, else one character per byte (its code point). -/
def TextOf (b : ByteArray) (s : String) : Prop :=
  String.fromUTF8? b = some s ∨
    String.fromUTF8? b = none ∧ s.toList = b.data.toList.map fun x => Char.ofNat x.toNat

/-- C1: the toolchain this fvdep checks = `leanprover/lean4:v` + the Lean it is built with. -/
def Toolchain : String := "leanprover/lean4:v" ++ Lean.versionString

/-- A refusal: the messages on stderr, nothing on stdout, exit 2. -/
def Refused (ms : List String) (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  evs = [(.err (Out ms), .done)] ∧ code = 2

/-- A result: one line on stdout, exit `c`. -/
def Said (m : String) (c : UInt32) (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  evs = [(.out (Out [m]), .done)] ∧ code = c

/-- C2 + A2: the record type + fields of a certified registry list (`profiles`: no field check —
its elements are unread). -/
def FieldsOk (o : Observed) (c : Name) : Prop :=
  (c = `Fvdep.Registry.modules →
      o.fields.lookup `Fvdep.Registry.Types.V1.Module =
        some (some ["id", "version", "spec", "obligations", "abi", "compat"])) ∧
    (c = `Fvdep.Registry.notices →
      o.fields.lookup `Fvdep.Registry.Types.V1.Notice =
        some (some ["id", "version", "reason", "replacement"])) ∧
    (c = `Fvdep.Registry.removed →
      o.fields.lookup `Fvdep.Registry.Types.V1.Removed =
        some (some ["id", "version", "kind", "digest", "toolchain", "lastCommit"]))

/-- C2: the kernel certified list `c`'s literal (type + definitional equality). -/
def Certified (o : Observed) (c : Name) : Prop := FieldsOk o c ∧ o.certified.lookup c = some true

def formMsg (c : Name) : String := s!"The registry uses a form fvdep cannot read: {c}."

/-- C9 registry form → certificate → entry rules over the observations: the lists, or the first
refusal (`certificate`'s order: `modules`, `profiles` while empty, `notices`, `removed`). -/
def Judged (o : Observed) (j : Except String Lists) : Prop :=
  match readRaw o.facts with
  | .error c => j = .error (formMsg c)
  | .ok r =>
    (∃ pre x post,
        certificate r = pre ++ x :: post ∧
          ¬Certified o x.1 ∧ (∀ y ∈ pre, Certified o y.1) ∧ j = .error (formMsg x.1)) ∨
      (∀ y ∈ certificate r, Certified o y.1) ∧
        match validate o.facts (Lists.ofRaw r) with
        | some f => j = .error (render f)
        | none => j = .ok (Lists.ofRaw r)

def schemaMsg (e : DocError) : String := s!"The index is outside schema 1: {e.render}."

/-- C9 after replay: statuses + warnings (`assemble`), then the schema (`IndexFile.ofJson`), then
the canonical bytes (`encodeIndex`) + the operation count — or the warnings + the refusal. -/
def Indexed (h : ByteArray → String) (raw : String) (o : Observed) (l : Lists)
    (j : Except (List String × String) (List String × ByteArray × Nat)) : Prop :=
  match assemble o.facts o.axioms l raw h with
  | .error f => j = .error ([], render f)
  | .ok (v, ws) =>
    match IndexFile.ofJson v with
    | .error e => j = .error (ws.map Warning.render, schemaMsg e)
    | .ok i =>
      match encodeIndex i with
      | .error e => j = .error (ws.map Warning.render, schemaMsg e)
      | .ok b => j = .ok (ws.map Warning.render, b, i.operations.length)

/-- `--check`'s result: the committed bytes against the decided ones (absent = differs). -/
def Compared (b : ByteArray) (rr : Except String (Option ByteArray)) (evs : List (Eff × Response))
    (code : UInt32) : Prop :=
  match rr with
  | .ok (some c) =>
    if c.data = b.data then Said "index.json is current" 0 evs code
    else Said "index.json differs from the library" 1 evs code
  | .ok none => Said "index.json differs from the library" 1 evs code
  | .error r => Refused [s!"Could not read index.json: {r}."] evs code

/-- The replace's result (`n` = the entry count). -/
def Wrote (n : Nat) (rr : Except String Unit) (evs : List (Eff × Response)) (code : UInt32) :
    Prop :=
  match rr with
  | .ok () => Said s!"Wrote index.json ({n} entries)" 0 evs code
  | .error r => Refused [s!"Could not finish writing index.json: {r}."] evs code

/-- After the decision: the warnings (when any) on stderr, then the one file effect — `--check`
reads `index.json` + compares, else `index.json` is replaced by the decided bytes. -/
def Decided (check : Bool) (ws : List String) (b : ByteArray) (n : Nat)
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  ∃ rest,
    evs = (if ws = [] then [] else [(.err (Out ws), .done)]) ++ rest ∧
      if check then ∃ rr post, rest = (.read .index, .read rr) :: post ∧ Compared b rr post code
      else ∃ rr post, rest = (.replace .index b, .replace rr) :: post ∧ Wrote n rr post code

/-- C9 replay, then the index stages + the decision. -/
def Replayed (h : ByteArray → String) (check : Bool) (raw : String) (o : Observed) (l : Lists)
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  ∃ rr rest,
    evs = (.replay, .replay rr) :: rest ∧
      match rr with
      | .ok (some (m, k)) => Refused [s!"Kernel replay rejected {m}: {k}"] rest code
      | .error r => Refused [s!"Could not run the kernel replay: {r}."] rest code
      | .ok none =>
        ∃ j,
          Indexed h raw o l j ∧
            match j with
            | .error (ws, m) => Refused (ws ++ [m]) rest code
            | .ok (ws, b, n) => Decided check ws b n rest code

/-- C9 build → load → registry form → certificate → entry rules, then the replay. -/
def Built (h : ByteArray → String) (check : Bool) (raw : String) (evs : List (Eff × Response))
    (code : UInt32) : Prop :=
  ∃ rf rest,
    evs = (.libraryFacts, .facts rf) :: rest ∧
      match rf with
      | .error (.build l) => Refused [s!"Build failed: {l}"] rest code
      | .error (.load r) => Refused [s!"Could not load the built library: {r}."] rest code
      | .ok o =>
        ∃ j,
          Judged o j ∧
            match j with
            | .error m => Refused [m] rest code
            | .ok l => Replayed h check raw o l rest code

def mismatchMsg (t : String) : String :=
  s!"This library uses Lean {t}; this fvdep checks Lean {Toolchain}. Install the matching fvdep."

/-- C1 + C9: a complete run of `fvdep index` (`check` = `--check`; `h` = the digest function): the
presence probe, the toolchain (`lean-toolchain` trimmed = fvdep's), then the observations. -/
def IndexRun (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response)) (code : UInt32) :
    Prop :=
  ∃ rp rest,
    evs = (.probe, .probe rp) :: rest ∧
      match rp with
      | .ok none =>
        Refused ["No fvdep library found here. Run \"fvdep index\" in a library working copy."] rest
          code
      | .error r => Refused [s!"Could not read lean-toolchain: {r}."] rest code
      | .ok (some b) =>
        ∃ raw t,
          TextOf b raw ∧
            Trimmed raw t ∧
            if t = Toolchain then Built h check raw rest code else Refused [mismatchMsg t] rest code

end FvdepAudit.Index.Command.Spec
