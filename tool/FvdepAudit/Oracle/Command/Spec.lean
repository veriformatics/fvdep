import FvdepAudit.Index.Command.Spec
import FvdepAudit.Oracle.Resolve.Spec
import FvdepCore.Oracle.Command

/-! `fvdep oracle <target> [--project <dir>]` written apart (contract
`docs/contracts/U5b-oracle.md` E1–E5, V1–V5, O1–O3): a complete run as a relation over the
observation answers, stage by stage in E1's order — project, manifest, Lake's parse, snapshot (its
notice), toolchain, `index.json`, the target's row, K's discovery + coherence, the view, export 1 +
the entry, export 2 + the signature, stdin, the staging + its budgets, the evaluation (none for no
valid request), the merge, the batch budget — then the replies in one stdout write. Messages are
written here from the contract. Shared with the shipped code: the claimed functions
(`selectProject`, `textStage`, `validate`, `toolchainRefusal`, `decodeIndex`, `rowOf`,
`coherence`, `entrySpec`, `specSig`, `Export.read`, `decodeRequest`, `encodeArgs`, `merge`,
`encodeReply`, `Protocol.lines`), the tested presentation (`escapeControls`, the U3 + index +
export refusal renderings, `textOfBytes`), the module naming, the driver text (residue
`oracle-driver`), the effect vocabulary. -/

namespace FvdepAudit.Oracle.Command.Spec

open Lean FvdepCore FvdepCore.Ids FvdepCore.Index FvdepCore.Protocol FvdepCore.Oracle
open FvdepCore.Index.Rules (entryModule closure)
open FvdepAudit.Index.Command.Spec (Refused Out)

/-- A cause's interface code as the contract spells it. -/
def word : FvdepCore.Evidence.Infra → String
  | .sandboxSetup => "sandbox_setup"
  | .toolMissing => "tool_missing"
  | .adapter => "adapter"
  | .fetchFailed => "fetch_failed"
  | .io => "io"

/-- `infra <code>: oracle, <stage>: <detail>`. -/
def causeMsg (stage : String) (c : Cause) : String :=
  "infra " ++ word c.code ++ ": oracle, " ++ stage ++ ": " ++ c.detail

/-- A response of another effect's kind (no fitting run reaches it). -/
def kindMsg (what : String) : String := "internal: " ++ what ++ " got another effect's response"

/-- A name with plain components as K + the steps spell it (its components `.`-joined). -/
def dotted (n : Name) : String := ".".intercalate (FvdepCore.Oracle.Driver.parts n)

/-! ## V1–V5 -/

/-- V2: a request line's place in the merge. -/
def reqOf (sig : Sig) (l : ByteArray) : Req :=
  match decodeRequest sig l with
  | .error r => .invalid r
  | .ok _ => .valid

/-- V2: a request line's W1 text for `requests.txt` (a refused line stages nothing). -/
def stagedOf (sig : Sig) (l : ByteArray) : String :=
  match decodeRequest sig l with
  | .ok xs => Wire.encodeArgs xs ++ "\n"
  | .error _ => ""

/-- V2: a request line's charge against the batch budget (a refused line's `invalid` reply). -/
def chargeOf (sig : Sig) (l : ByteArray) : Nat :=
  match decodeRequest sig l with
  | .error r => (encodeReply (.invalid r)).size
  | .ok _ => 0

/-- V2: lines `ls` keep both budgets — their staged bytes + their charges. -/
def Within (lim : Command.Limits) (sig : Sig) (ls : List ByteArray) : Prop :=
  (String.join (ls.map (stagedOf sig))).utf8ByteSize ≤ lim.stagingBytes ∧
    (ls.map (chargeOf sig)).sum ≤ lim.batchBytes

/-- V2's outcome over the requests' lines: every line within both budgets → the requests in order
+ the staged text; else refused at the first line whose addition passes a budget — the staging
budget for a valid line, the batch budget for a refused one. -/
def Staged (lim : Command.Limits) (sig : Sig) (ls : List ByteArray)
    (r : Except Command.Over (List Req × String)) : Prop :=
  (Within lim sig ls ∧ r = .ok (ls.map (reqOf sig), String.join (ls.map (stagedOf sig)))) ∨
    ∃ pre l post,
      ls = pre ++ l :: post ∧
        Within lim sig pre ∧
        ¬Within lim sig (pre ++ [l]) ∧
        r = .error (if reqOf sig l = .valid then .staging else .batch)

/-- V4 + I5: the replies' bytes in order, in one stdout write (none when empty) within the batch
budget, exit 0; past it, the output refusal + no reply. -/
def Replied (lim : Command.Limits) (rs : List Reply) (evs : List (Eff × Response)) (code : UInt32) :
    Prop :=
  let b := (rs.map encodeReply).foldl (· ++ ·) .empty
  if lim.batchBytes < b.size then
    Refused
      ["infra io: oracle, output: the encoded batch exceeds " ++ toString lim.batchBytes ++
          " bytes"]
      evs code
  else if b.size = 0 then evs = [] ∧ code = 0 else evs = [(.outBytes b, .done)] ∧ code = 0

/-- V4: the replies of the requests `reqs` from the step's bytes, else the malformed-reply
refusal. -/
def Merged (lim : Command.Limits) (sig : Sig) (reqs : List Req) (b : ByteArray)
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  match merge sig.result reqs b with
  | .ok rs => Replied lim rs evs code
  | .error k =>
    Refused ["infra io: oracle, evaluate: the driver's reply " ++ toString k ++ " is malformed"] evs
      code

/-- V1–V3 after stdin: the batch cap, V2's staging, then the one evaluation step over the view
(the driver of entry module `M` + spec constant `spec`, `requests.txt` = the staged text) — none
when no request is valid. -/
def Input (lim : Command.Limits) (M spec : Name) (sig : Sig) (view : String) (r : FileRead)
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  let over := "infra io: oracle, input: the batch exceeds " ++ toString lim.requestBytes ++ " bytes"
  match r with
  | .tooLarge => Refused [over] evs code
  | .failed x => Refused ["infra io: oracle, input: " ++ x] evs code
  | .absent => Refused [kindMsg "the input read"] evs code
  | .bytes b =>
    if lim.requestBytes < b.size then Refused [over] evs code
    else
      ∃ st,
        Staged lim sig (Protocol.lines b) st ∧
          match st with
          | .error .batch =>
            Refused
              ["infra io: oracle, output: the encoded batch exceeds " ++ toString lim.batchBytes ++
                  " bytes"]
              evs code
          | .error .staging =>
            Refused
              ["infra io: oracle, input: the staged requests.txt exceeds " ++
                  toString lim.stagingBytes ++
                  " bytes"]
              evs code
          | .ok (reqs, staged) =>
            if Req.valid ∈ reqs then
              ∃ rr rest,
                evs =
                    (.evaluate view (Driver.driverText M spec) staged.toUTF8 lim.oracleSeconds,
                        .evaluate rr) ::
                      rest ∧
                  match rr with
                  | .ok rb => Merged lim sig reqs rb rest code
                  | .error c => Refused [causeMsg "evaluate" c] rest code
            else Merged lim sig reqs .empty evs code

/-! ## E1–E5 -/

/-- E3–E5's refusal texts. -/
def whyMsg (t : Target) (commit : String) (budget : Nat) : Why → String
  | .inconsistent r => "the library snapshot " ++ commit ++ " is inconsistent: " ++ r
  | .budget =>
    "infra io: the registry entry of " ++ t.text ++ " exceeds " ++ toString budget ++ " nodes"
  | .cannotCarry => "the spec of " ++ t.text ++ " has a type the adapter protocol cannot carry"

/-- X5's refusal of export `k`. -/
def exportMsg (k : Nat) (r : Export.Refusal) : String :=
  "infra io: oracle, export " ++ toString k ++ ": the export " ++
    (match r.cls with
    | .malformed => "is malformed"
    | .profile => "is outside the reader's profile") ++
    " at line " ++
    toString r.line ++
    ": " ++
    r.reason

/-- An export answer read by X, then `next` over its declarations. -/
def Exported (k : Nat) (r : Except Cause ByteArray) (evs : List (Eff × Response)) (code : UInt32)
    (next : List Export.Decl → List (Eff × Response) → UInt32 → Prop) : Prop :=
  match r with
  | .error c => Refused [causeMsg ("export " ++ toString k) c] evs code
  | .ok b =>
    match Export.read Lean.githash Lean.versionString b with
    | .error x => Refused [exportMsg k x] evs code
    | .ok ds => next ds evs code

/-- E4 after export 2 (imports = [S], roots = [`spec`]): the signature, then stdin. -/
def Signed (lim : Command.Limits) (t : Target) (commit : String) (M spec : Name) (view : String)
    (ds : List Export.Decl) (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  match specSig spec ds with
  | .error w => Refused [whyMsg t commit lim.decodeNodes w] evs code
  | .ok sig =>
    ∃ r rest,
      evs = (.stdin lim.requestBytes, .stdin r) :: rest ∧ Input lim M spec sig view r rest code

/-- E3 + E5 after export 1 (imports = [M], roots = [`M.entry`]): the spec constant, then export 2
over the same view. -/
def Entered (lim : Command.Limits) (t : Target) (m : ModuleId) (v : EntryVersion) (commit : String)
    (mods : List Name) (view : String) (ds : List Export.Decl) (evs : List (Eff × Response))
    (code : UInt32) : Prop :=
  match entrySpec lim.decodeNodes m v mods ds with
  | .error w => Refused [whyMsg t commit lim.decodeNodes w] evs code
  | .ok spec =>
    ∃ r rest,
      evs =
          (.leanexport view [dotted (FvdepCore.Ids.leanModule m v)] [dotted spec], .leanexport r) ::
            rest ∧
        Exported 2 r rest code (Signed lim t commit (entryModule m v) spec view)

/-- O1 + K after the coherence check: the view of the discovery's closure, then export 1 over
it. -/
def Viewed (lim : Command.Limits) (t : Target) (m : ModuleId) (v : EntryVersion) (commit : String)
    (mods : List Name) (r : Except Cause String) (evs : List (Eff × Response)) (code : UInt32) :
    Prop :=
  match r with
  | .error c => Refused [causeMsg "the library build" c] evs code
  | .ok view =>
    ∃ r1 rest,
      evs =
          (.leanexport view [dotted (entryModule m v)] [dotted (entryModule m v) ++ ".entry"],
              .leanexport r1) ::
            rest ∧
        Exported 1 r1 rest code (Entered lim t m v commit mods view)

/-- E2 after K's discovery of the entry module + W's version module. -/
def Discovered (h : ByteArray → String) (lim : Command.Limits) (t : Target) (m : ModuleId)
    (v : EntryVersion) (s : Snap) (i : IndexFile) (o : Operation) (r : Except String (List Src))
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  match r with
  | .error x => Refused ["infra io: oracle, the library: " ++ x] evs code
  | .ok srcs =>
    match
      coherence h (FvdepCore.Index.Command.textOfBytes s.toolchain) i o (entryModule m v) srcs with
    | some why =>
      Refused ["the library snapshot " ++ s.commit ++ " is inconsistent: " ++ why] evs code
    | none =>
      ∃ rv rest,
        evs =
            (.view s.tree [dotted (entryModule m v), "Fvdep.Semver.Version.V1_0_0"], .view rv) ::
              rest ∧
          Viewed lim t m v s.commit (closure (factsOf srcs) (entryModule m v)) rv rest code

/-- `unknown target <t>`. -/
def unknownMsg (t : Target) (commit : String) : String :=
  "unknown target " ++ t.text ++ ": the library snapshot " ++ commit ++ " does not list it"

/-- L7 + E1 over the served snapshot: the toolchain, `index.json`, the target's row, then K's
discovery. -/
def Served (h : ByteArray → String) (lim : Command.Limits) (t : Target) (s : Snap)
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  match
    FvdepCore.Library.toolchainRefusal s.commit (FvdepCore.Index.Command.textOfBytes s.toolchain)
      FvdepCore.Index.Command.toolchain with
  | some x => Refused [x] evs code
  | none =>
    match decodeIndex s.index with
    | .error e =>
      Refused
        ["the library snapshot " ++ s.commit ++ " holds an index.json outside schema 1: " ++
            e.render]
        evs code
    | .ok i =>
      match t with
      | .profile _ => Refused [unknownMsg t s.commit] evs code
      | .op m v =>
        match rowOf i m v with
        | none => Refused [unknownMsg t s.commit] evs code
        | some o =>
          ∃ r rest,
            evs =
                (.closure s.tree [dotted (entryModule m v), "Fvdep.Semver.Version.V1_0_0"],
                    .closure r) ::
                  rest ∧
              Discovered h lim t m v s i o r rest code

/-- L: the snapshot of `pin` (`none` = the head) under L's limits; a served head's notice first
on stderr. -/
def Fetched (h : ByteArray → String) (lim : Command.Limits) (t : Target) (pin : Option String)
    (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  ∃ r rest,
    evs = (.snapshot pin lim.library, .snapshot r) :: rest ∧
      match r with
      | .error x => Refused [x] rest code
      | .ok s =>
        match s.notice with
        | none => Served h lim t s rest code
        | some n => ∃ post, rest = (.err (Out [n]), .done) :: post ∧ Served h lim t s post code

/-- U3's refusal of `<dir>/fvdep.toml`. -/
def manifestMsg (dir : String) (e : FvdepCore.Manifest.ReadError) : String :=
  "infra " ++ e.code.spelling ++ ": " ++ dir ++ "/fvdep.toml: " ++ e.detail

/-- P2 after the read: U3's text stage, Lake's parse, `validate` → the pin. -/
def ManifestRead (h : ByteArray → String) (lim : Command.Limits) (t : Target) (dir : String)
    (r : FileRead) (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  match r with
  | .absent => Refused ["No fvdep.toml found in " ++ dir ++ "."] evs code
  | .tooLarge => Refused [manifestMsg dir (.text .tooLarge)] evs code
  | .failed x => Refused ["infra io: " ++ dir ++ "/fvdep.toml could not be read: " ++ x] evs code
  | .bytes b =>
    match FvdepCore.Manifest.textStage b with
    | .error e => Refused [manifestMsg dir (.text e)] evs code
    | .ok text =>
      ∃ pr rest,
        evs = (.parse text, .parse pr) :: rest ∧
          match pr with
          | .error e => Refused [manifestMsg dir (.parse e)] rest code
          | .ok tree =>
            match FvdepCore.Manifest.validate tree with
            | .error e => Refused [manifestMsg dir (.schema e)] rest code
            | .ok mf => Fetched h lim t (some (toString mf.library)) rest code

/-- O3: a complete run of `fvdep oracle` (`h` = the digest function; `explicit` = `--project`):
the project observation, then (a project) its manifest's pin or (none) the head. -/
def OracleRun (h : ByteArray → String) (lim : Command.Limits) (t : Target)
    (explicit : Option String) (evs : List (Eff × Response)) (code : UInt32) : Prop :=
  ∃ seen rest,
    evs = (.project explicit, .project seen) :: rest ∧
      match FvdepCore.Project.selectProject seen with
      | .refuse x => Refused [x] rest code
      | .none => Fetched h lim t none rest code
      | .project dir =>
        ∃ r post, rest = (.manifest dir, .manifest r) :: post ∧ ManifestRead h lim t dir r post code

end FvdepAudit.Oracle.Command.Spec
