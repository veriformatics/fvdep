import FvdepCore.Index.Assemble
import FvdepCore.Plan

/-! `fvdep index [--check]` as a plan (contract `docs/contracts/U4-library.md` C1 + C9): the
observation effects (`probe`, `libraryFacts`, `replay`) answer; the pure stages decide in C9's
order — library presence, toolchain, build, load, registry form, certificate, entry rules, replay,
statuses + warnings, schema — and only then is `index.json` read (`--check`) or replaced. Every
message leaves through `line` (interface §1's line rule). -/

namespace FvdepCore.Index.Command

open Lean FvdepCore.Doc FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses FvdepCore.Index.Assemble

/-- Interface §1's line rule at the output seam: one message = one line, its control characters
escaped. -/
def line (m : String) : String := escapeControls m ++ "\n"

def lines (ms : List String) : String := String.join (ms.map line)

/-- The toolchain this fvdep checks, in `lean-toolchain` form: the Lean it is built with (the one
olean format it imports). -/
def toolchain : String := "leanprover/lean4:v" ++ Lean.versionString

/-- Bytes as text: UTF-8, else each byte as the character of that code point (total; the line rule
escapes the unprintable). -/
def textOfBytes (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => String.ofList (b.data.toList.map fun x => Char.ofNat x.toNat)

def absent : String := "No fvdep library found here. Run \"fvdep index\" in a library working copy."

def mismatch (x : String) : String :=
  s!"This library uses Lean {x}; this fvdep checks Lean {toolchain}. Install the matching fvdep."

def formLine (c : Name) : String := s!"The registry uses a form fvdep cannot read: {c}."

def schemaLine (e : DocError) : String := s!"The index is outside schema 1: {e.render}."

def internal (what : String) : String := s!"internal: {what} got another effect's response"

/-- C9 presence, then toolchain: the raw `lean-toolchain` text, or the refusal. -/
def probeStage : Response → Except String String
  | .probe (.ok (some b)) =>
    let x := textOfBytes b
    if trimText x = toolchain then .ok x else .error (mismatch (trimText x))
  | .probe (.ok none) => .error absent
  | .probe (.error r) => .error s!"Could not read lean-toolchain: {r}."
  | _ => .error (internal "the library probe")

/-- C2: the record type of a registry list's elements + the fields fvdep reads it with (`profiles`:
elements unread, no field check). -/
def listType (c : Name) : Option (Name × List String) :=
  if c == modulesName then some (``Fvdep.Registry.Types.V1.Module, moduleFields)
  else
    if c == noticesName then some (``Fvdep.Registry.Types.V1.Notice, noticeFields)
    else if c == removedName then some (``Fvdep.Registry.Types.V1.Removed, removedFields) else none

/-- C2's certificate of one registry list: its record type's fields = fvdep's + the kernel certified
its literal. -/
def certifiedList (o : Observed) (c : Name) : Bool :=
  (match listType c with
    | some (t, fs) => o.fields.lookup t == some (some fs)
    | none => true) &&
    o.certified.lookup c == some true

/-- C2's certificate: the first list, in `certificate` order, it does not certify. -/
def uncertified (o : Observed) (r : RawLists) : Option Name :=
  ((certificate r).find? fun x => !certifiedList o x.1).map (·.1)

/-- C9 build → load: the observations, or the refusal. -/
def factsStage : Response → Except String Observed
  | .facts (.ok o) => .ok o
  | .facts (.error (.build l)) => .error s!"Build failed: {l}"
  | .facts (.error (.load r)) => .error s!"Could not load the built library: {r}."
  | _ => .error (internal "the library observation")

/-- C9 registry form → certificate → entry rules over the observations: the registry lists, or the
refusal. -/
def judge (o : Observed) : Except String Lists :=
  match readRaw o.facts with
  | .error c => .error (formLine c)
  | .ok r =>
    match uncertified o r with
    | some c => .error (formLine c)
    | none =>
      match validate o.facts (Lists.ofRaw r) with
      | some f => .error (render f)
      | none => .ok (Lists.ofRaw r)

/-- C9 replay: `none` when every module replayed, else the refusal. -/
def replayStage : Response → Option String
  | .replay (.ok none) => none
  | .replay (.ok (some (m, l))) => some s!"Kernel replay rejected {m}: {l}"
  | .replay (.error r) => some s!"Could not run the kernel replay: {r}."
  | _ => some (internal "the kernel replay")

/-- C9 after replay: statuses + warnings, then the schema — the warnings + the refusal, or the
warnings + the canonical bytes + the operation count. -/
def indexStage (h : ByteArray → String) (tc : String) (o : Observed) (l : Lists) :
    Except (List String × String) (List String × ByteArray × Nat) :=
  match assemble o.facts o.axioms l tc h with
  | .error f => .error ([], render f)
  | .ok (v, ws) =>
    match IndexFile.ofJson v with
    | .error e => .error (ws.map Warning.render, schemaLine e)
    | .ok i =>
      match encodeIndex i with
      | .error e => .error (ws.map Warning.render, schemaLine e)
      | .ok b => .ok (ws.map Warning.render, b, i.operations.length)

/-- Stderr lines (when any), then the exit code. -/
def stop (ms : List String) (code : UInt32) : Plan UInt32 :=
  if ms.isEmpty then .pure code else .step (.err (lines ms)) fun _ => .pure code

/-- The result line on stdout, then the exit code. -/
def say (m : String) (code : UInt32) : Plan UInt32 := .step (.out (lines [m])) fun _ => .pure code

def current : String := "index.json is current"

def differs : String := "index.json differs from the library"

/-- `--check`: the committed bytes against the decided ones (absent = differs). -/
def compare (bytes : ByteArray) : Response → Plan UInt32
  | .read (.ok (some b)) => if b.data = bytes.data then say current 0 else say differs 1
  | .read (.ok none) => say differs 1
  | .read (.error r) => stop [s!"Could not read index.json: {r}."] 2
  | _ => stop [internal "the index read"] 2

/-- The replace's outcome (C1: a failure = `commit_io`). -/
def written (n : Nat) : Response → Plan UInt32
  | .replace (.ok ()) => say s!"Wrote index.json ({n} entries)" 0
  | .replace (.error r) => stop [s!"Could not finish writing index.json: {r}."] 2
  | _ => stop [internal "the index replace"] 2

/-- After the decision: the warnings, then the one file effect. -/
def finish (check : Bool) (ws : List String) (b : ByteArray) (n : Nat) : Plan UInt32 :=
  let act : Plan UInt32 :=
    if check then .step (.read .index) (compare b) else .step (.replace .index b) (written n)
  if ws.isEmpty then act else .step (.err (lines ws)) fun _ => act

/-- After the replay: the index stages, then the decision. -/
def onReplay (h : ByteArray → String) (check : Bool) (tc : String) (o : Observed) (l : Lists)
    (r : Response) : Plan UInt32 :=
  match replayStage r with
  | some m => stop [m] 2
  | none =>
    match indexStage h tc o l with
    | .error (ws, m) => stop (ws ++ [m]) 2
    | .ok (ws, b, n) => finish check ws b n

/-- After the observation: the registry's judgment, then the replay. -/
def onFacts (h : ByteArray → String) (check : Bool) (tc : String) (r : Response) : Plan UInt32 :=
  match factsStage r with
  | .error m => stop [m] 2
  | .ok o =>
    match judge o with
    | .error m => stop [m] 2
    | .ok l => .step .replay (onReplay h check tc o l)

/-- After the probe: the toolchain, then the observation. -/
def onProbe (h : ByteArray → String) (check : Bool) (r : Response) : Plan UInt32 :=
  match probeStage r with
  | .error m => stop [m] 2
  | .ok tc => .step .libraryFacts (onFacts h check tc)

/-- `fvdep index` (`check` = `--check`); `h` = the digest function (IO: SHA-256 hex). -/
def plan (h : ByteArray → String) (check : Bool) : Plan UInt32 := .step .probe (onProbe h check)

end FvdepCore.Index.Command
