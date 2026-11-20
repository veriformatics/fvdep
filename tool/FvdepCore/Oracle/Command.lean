import FvdepCore.Index.Command
import FvdepCore.Library
import FvdepCore.Oracle
import FvdepCore.Oracle.Driver
import FvdepCore.Oracle.Resolve

/-! `fvdep oracle <target>` as a plan (contract `docs/contracts/U5b-oracle.md` E1–E5, V1–V5,
O1–O3): the observation effects answer; the pure stages decide in E1's order — project, manifest,
snapshot, toolchain, index row, discovery + coherence, view, export 1 + the entry, export 2 + the
signature, stdin, staging, evaluation, merge, the batch budget — and the replies leave in one stdout
write after every check (I5). Every message = one line through interface §1's line rule; each
refusal exits 2. -/

namespace FvdepCore.Oracle.Command

open Lean FvdepCore.Ids FvdepCore.Index FvdepCore.Protocol FvdepCore.Index.Command
open FvdepCore.Index.Rules (entryModule closure)

/-- T's oracle limits (L's five + E5 + V's; the dev seam overrides them, `fvdep oracle` takes the
defaults). -/
structure Limits where
  library : FvdepCore.Library.Limits := {}
  decodeNodes : Nat := 1000000
  requestBytes : Nat := 67108864
  stagingBytes : Nat := 268435456
  batchBytes : Nat := 134217728
  oracleSeconds : Nat := 300
  deriving DecidableEq, Repr

/-- One `--limit <name>=<n>` of the dev seam (Q3): `none` = no limit of that name. -/
def Limits.set (l : Limits) (name : String) (n : Nat) : Option Limits :=
  match name with
  | "decodeNodes" => some { l with decodeNodes := n }
  | "requestBytes" => some { l with requestBytes := n }
  | "stagingBytes" => some { l with stagingBytes := n }
  | "batchBytes" => some { l with batchBytes := n }
  | "oracleSeconds" => some { l with oracleSeconds := n }
  | _ => (l.library.set name n).map fun x => { l with library := x }

/-! ## Texts (presentation) -/

def infraWord : FvdepCore.Evidence.Infra → String
  | .sandboxSetup => "sandbox_setup"
  | .toolMissing => "tool_missing"
  | .adapter => "adapter"
  | .fetchFailed => "fetch_failed"
  | .io => "io"

def causeLine (stage : String) (c : Cause) : String :=
  s!"infra {infraWord c.code}: oracle, {stage}: {c.detail}"

def manifestLine (dir : String) (e : FvdepCore.Manifest.ReadError) : String :=
  s!"infra {e.code.spelling}: {dir}/fvdep.toml: {e.detail}"

def unknownLine (t : Target) (commit : String) : String :=
  s!"unknown target {t.text}: the library snapshot {commit} does not list it"

def indexLine (commit : String) (e : IndexError) : String :=
  s!"the library snapshot {commit} holds an index.json outside schema 1: {e.render}"

def inconsistentLine (commit why : String) : String :=
  s!"the library snapshot {commit} is inconsistent: {why}"

def whyLine (t : Target) (commit : String) (budget : Nat) : Why → String
  | .inconsistent r => inconsistentLine commit r
  | .budget => s!"infra io: the registry entry of {t.text} exceeds {budget} nodes"
  | .cannotCarry => s!"the spec of {t.text} has a type the adapter protocol cannot carry"

def exportLine (k : Nat) (r : Export.Refusal) : String :=
  match r.cls with
  | .malformed =>
    s!"infra io: oracle, export {k}: the export is malformed at line {r.line}: " ++ r.reason
  | .profile =>
    s!"infra io: oracle, export {k}: the export is outside the reader's profile at line " ++
      s!"{r.line}: {r.reason}"

/-! ## V1–V2 staging -/

/-- The module W's `Val.version` needs in every view (W0). -/
def versionModule : String := "Fvdep.Semver.Version.V1_0_0"

/-- A name with plain components as K + the steps spell it. -/
def dotted (n : Name) : String := ".".intercalate (Driver.parts n)

/-- V2's state: the requests so far (reversed), the staged W1 text + its bytes, the bytes charged
to the batch budget (each refused request's encoded reply). -/
structure Staging where
  reqs : List Req := []
  staged : String := ""
  stagedBytes : Nat := 0
  charged : Nat := 0

/-- Which budget V2 passed. -/
inductive Over where
  | staging
  | batch
  deriving DecidableEq, Repr

/-- V1 + V2 from byte offset `i`: each LF-ended line (a final fragment without LF = one more line;
`Protocol.lines`' reading) through `decodeRequest`; a refused one = its `invalid` reply, charged to
the batch budget at once; a valid one = its W1 line staged for `requests.txt`. The first budget
passed stops. -/
def stageFrom (lim : Limits) (sig : Sig) (b : ByteArray) (i : Nat) (st : Staging) :
    Except Over Staging :=
  if h : i < b.size then
    have := Export.le_lineEnd b i (Nat.le_of_lt h)
    let e := Export.lineEnd b i
    match decodeRequest sig (b.extract i e) with
    | .error r =>
      let c := st.charged + (encodeReply (.invalid r)).size
      if lim.batchBytes < c then .error .batch
      else
        stageFrom lim sig b (e + 1)
          { st with
            reqs := .invalid r :: st.reqs, charged := c }
    | .ok xs =>
      let w := Wire.encodeArgs xs ++ "\n"
      let n := st.stagedBytes + w.utf8ByteSize
      if lim.stagingBytes < n then .error .staging
      else
        stageFrom lim sig b (e + 1)
          { st with
            reqs := .valid :: st.reqs
            staged := st.staged ++ w
            stagedBytes := n }
  else .ok st
termination_by b.size - i
decreasing_by all_goals omega

/-- V4: the replies' encoded bytes in order, counted while encoding: `none` once past `cap`. -/
def encodeAll (cap : Nat) : List Reply → ByteArray → Option ByteArray
  | [], acc => some acc
  | r :: rest, acc =>
    let acc := acc ++ encodeReply r
    if cap < acc.size then none else encodeAll cap rest acc

/-! ## The plan -/

/-- A refusal: its lines on stderr, exit 2. -/
def refuse (ms : List String) : Plan UInt32 := stop ms 2

/-- After every check: the encoded replies on stdout (no write for none), exit 0 — or the batch
budget's refusal. -/
def reply (lim : Limits) (rs : List Reply) : Plan UInt32 :=
  match encodeAll lim.batchBytes rs .empty with
  | none => refuse [s!"infra io: oracle, output: the encoded batch exceeds {lim.batchBytes} bytes"]
  | some b => if b.size == 0 then .pure 0 else .step (.outBytes b) fun _ => .pure 0

/-- V3 → V4: the step's reply lines merged with the refused requests. -/
def onEvaluate (lim : Limits) (sig : Sig) (reqs : List Req) : Response → Plan UInt32
  | .evaluate (.ok b) =>
    match merge sig.result reqs b with
    | .ok rs => reply lim rs
    | .error k => refuse [s!"infra io: oracle, evaluate: the driver's reply {k} is malformed"]
  | .evaluate (.error c) => refuse [causeLine "evaluate" c]
  | _ => refuse [internal "the evaluation"]

/-- V1–V3 after stdin: staging + budgets; no valid request ⇒ no step. -/
def onStdin (lim : Limits) (M spec : Name) (sig : Sig) (view : String) : Response → Plan UInt32
  | .stdin (.bytes b) =>
    if lim.requestBytes < b.size then
      refuse [s!"infra io: oracle, input: the batch exceeds {lim.requestBytes} bytes"]
    else
      match stageFrom lim sig b 0 {} with
      | .error .batch =>
        refuse [s!"infra io: oracle, output: the encoded batch exceeds {lim.batchBytes} bytes"]
      | .error .staging =>
        refuse
          [s!"infra io: oracle, input: the staged requests.txt exceeds {lim.stagingBytes} bytes"]
      | .ok st =>
        let reqs := st.reqs.reverse
        if reqs.all (· != .valid) then
          match merge sig.result reqs .empty with
          | .ok rs => reply lim rs
          | .error k => refuse [s!"infra io: oracle, evaluate: the driver's reply {k} is malformed"]
        else
          .step (.evaluate view (Driver.driverText M spec) st.staged.toUTF8 lim.oracleSeconds)
            (onEvaluate lim sig reqs)
  | .stdin .tooLarge =>
    refuse [s!"infra io: oracle, input: the batch exceeds {lim.requestBytes} bytes"]
  | .stdin (.failed r) => refuse [s!"infra io: oracle, input: {r}"]
  | _ => refuse [internal "the input read"]

/-- E4 after export 2: the signature, then stdin. -/
def onExport2 (lim : Limits) (t : Target) (commit : String) (M spec : Name) (view : String) :
    Response → Plan UInt32
  | .leanexport (.ok b) =>
    match Export.read Lean.githash Lean.versionString b with
    | .error r => refuse [exportLine 2 r]
    | .ok ds =>
      match specSig spec ds with
      | .error w => refuse [whyLine t commit lim.decodeNodes w]
      | .ok sig => .step (.stdin lim.requestBytes) (onStdin lim M spec sig view)
  | .leanexport (.error c) => refuse [causeLine "export 2" c]
  | _ => refuse [internal "export 2"]

/-- E3 + E5 after export 1: the spec constant, then export 2. -/
def onExport1 (lim : Limits) (t : Target) (m : ModuleId) (v : EntryVersion) (commit : String)
    (mods : List Name) (view : String) : Response → Plan UInt32
  | .leanexport (.ok b) =>
    match Export.read Lean.githash Lean.versionString b with
    | .error r => refuse [exportLine 1 r]
    | .ok ds =>
      match entrySpec lim.decodeNodes m v mods ds with
      | .error w => refuse [whyLine t commit lim.decodeNodes w]
      | .ok spec =>
        let S := FvdepCore.Ids.leanModule m v
        .step (.leanexport view [dotted S] [dotted spec])
          (onExport2 lim t commit (entryModule m v) spec view)
  | .leanexport (.error c) => refuse [causeLine "export 1" c]
  | _ => refuse [internal "export 1"]

/-- K after the coherence check: the view, then export 1. -/
def onView (lim : Limits) (t : Target) (m : ModuleId) (v : EntryVersion) (commit : String)
    (mods : List Name) : Response → Plan UInt32
  | .view (.ok view) =>
    let M := entryModule m v
    .step (.leanexport view [dotted M] [dotted M ++ ".entry"])
      (onExport1 lim t m v commit mods view)
  | .view (.error c) => refuse [causeLine "the library build" c]
  | _ => refuse [internal "the library view"]

/-- E2 after K's discovery: the coherence of the target's row, then the view. -/
def onClosure (h : ByteArray → String) (lim : Limits) (t : Target) (m : ModuleId) (v : EntryVersion)
    (s : Snap) (i : IndexFile) (o : Operation) : Response → Plan UInt32
  | .closure (.ok srcs) =>
    let M := entryModule m v
    match coherence h (textOfBytes s.toolchain) i o M srcs with
    | some why => refuse [inconsistentLine s.commit why]
    | none =>
      .step (.view s.tree [dotted M, versionModule])
        (onView lim t m v s.commit (closure (factsOf srcs) M))
  | .closure (.error r) => refuse [s!"infra io: oracle, the library: {r}"]
  | _ => refuse [internal "the library discovery"]

/-- L7 → E1 over the served snapshot: the toolchain, `index.json`, the target's row, then K's
discovery of the entry module + W's version module. -/
def served (h : ByteArray → String) (lim : Limits) (t : Target) (s : Snap) : Plan UInt32 :=
  match
    FvdepCore.Library.toolchainRefusal s.commit (textOfBytes s.toolchain)
      Index.Command.toolchain with
  | some r => refuse [r]
  | none =>
    match decodeIndex s.index with
    | .error e => refuse [indexLine s.commit e]
    | .ok i =>
      match t with
      | .profile _ => refuse [unknownLine t s.commit]
      | .op m v =>
        match rowOf i m v with
        | none => refuse [unknownLine t s.commit]
        | some o =>
          .step (.closure s.tree [dotted (entryModule m v), versionModule])
            (onClosure h lim t m v s i o)

/-- L: the snapshot (its notice first, on stderr), then the rest. -/
def onSnapshot (h : ByteArray → String) (lim : Limits) (t : Target) : Response → Plan UInt32
  | .snapshot (.ok s) =>
    match s.notice with
    | some n => .step (.err (lines [n])) fun _ => served h lim t s
    | none => served h lim t s
  | .snapshot (.error r) => refuse [r]
  | _ => refuse [internal "the library snapshot"]

/-- L for the pin (a project's) or the head. -/
def fetch (h : ByteArray → String) (lim : Limits) (t : Target) (pin : Option String) :
    Plan UInt32 := .step (.snapshot pin lim.library) (onSnapshot h lim t)

/-- P2 after Lake's parse: `validate` → the pin. -/
def onParse (h : ByteArray → String) (lim : Limits) (t : Target) (dir : String) :
    Response → Plan UInt32
  | .parse (.ok tree) =>
    match FvdepCore.Manifest.validate tree with
    | .ok mf => fetch h lim t (some (toString mf.library))
    | .error e => refuse [manifestLine dir (.schema e)]
  | .parse (.error e) => refuse [manifestLine dir (.parse e)]
  | _ => refuse [internal "the manifest parse"]

/-- P2 after the read: the text stage, then Lake's parse. -/
def onManifest (h : ByteArray → String) (lim : Limits) (t : Target) (dir : String) :
    Response → Plan UInt32
  | .manifest (.bytes b) =>
    match FvdepCore.Manifest.textStage b with
    | .ok text => .step (.parse text) (onParse h lim t dir)
    | .error e => refuse [manifestLine dir (.text e)]
  | .manifest .tooLarge => refuse [manifestLine dir (.text .tooLarge)]
  | .manifest .absent => refuse [s!"No fvdep.toml found in {dir}."]
  | .manifest (.failed r) => refuse [s!"infra io: {dir}/fvdep.toml could not be read: {r}"]
  | _ => refuse [internal "the manifest read"]

/-- P1–P3: the project (its pin) or none (the head). -/
def onProject (h : ByteArray → String) (lim : Limits) (t : Target) : Response → Plan UInt32
  | .project seen =>
    match FvdepCore.Project.selectProject seen with
    | .none => fetch h lim t none
    | .project dir => .step (.manifest dir) (onManifest h lim t dir)
    | .refuse r => refuse [r]
  | _ => refuse [internal "the project observation"]

/-- `fvdep oracle <target> [--project <dir>]` (`h` = the digest function; IO: SHA-256 hex). -/
def plan (h : ByteArray → String) (lim : Limits) (t : Target) (explicit : Option String) :
    Plan UInt32 := .step (.project explicit) (onProject h lim t)

/-! ## The command line -/

/-- Human-facing usage text of `fvdep oracle` (CLI help). -/
def usage : String :=
  "Usage: fvdep oracle <id>@<version> [--project <dir>]\n\n" ++
    "Answers adapter protocol v1 requests with the spec of one library operation.\n" ++
    "Reads JSON request lines on stdin until the end of the input. Then writes one\n" ++
    "JSON reply line per request on stdout, in request order.\n\n" ++
    "The library snapshot is the commit that fvdep.toml pins. Outside a project,\n" ++
    "it is the head of the library source (FVDEP_LIBRARY_URL).\n\n" ++
    "Options:\n" ++
    "  --project <dir>  Use the project in <dir>.\n" ++
    "  --help           Show this help.\n"

/-- `oracle`'s arguments: one target + at most one `--project <dir>`, on either side of it (a first
`--project` = the option; an option-shaped target fails E1's grammar, so it needs no check here). -/
def parseArgs : List String → Option (String × Option String)
  | [t] => some (t, none)
  | [a, b, c] =>
    if a == "--project" then some (c, some b)
    else if b == "--project" then some (a, some c) else none
  | _ => none

end FvdepCore.Oracle.Command
