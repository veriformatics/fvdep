import FvdepAudit.Profile.Stage.Spec
import FvdepCore.Profile.Barrier

/-! U6 P5c + P5b + B3 + C1's spec of the supervisor's verdict + the batch's conclusion, written
apart from `FvdepCore.Profile.judge` + `conclude`: P5c's failures of the parse step's run as one
list in P5c's order (the first = the infrastructure line), else P5b's intake of the record bytes +
B3's outcome mapping; the batch = the header stage's first event over every module in batch order
(each header's findings from `Stage.Spec.headerRules`), then the body stage's (each module's
observed event), else accepted. Shared + read as spec text: `least` (the least path by bytes),
`intake` (P5b: claimed by `intakeExact`), `grammars` (P3's lists: `grammarInit` + tested),
`outcomeOf` (an event in a module → P5b's outcome). -/

namespace FvdepAudit.Profile.Barrier.Spec

open FvdepCore.Profile FvdepAudit.Profile.Stage.Spec
open FvdepCore.Evidence (Infra)

/-- P5c's failures of the parse step's run, in P5c's order: bwrap's setup (`sandbox_setup`), the
deadline, the frame over `frameBytes`, an invalid frame (a status the helper's exit code
contradicts included), the child's signal, a child that never started, a size cap, a nonzero exit,
no `results.json`, another file beside it (the least path). -/
def failures (seconds frameBytes : Nat) : Run → List (Infra × String)
  | .setup d => [(.sandboxSetup, s!"profile, {d}")]
  | .timedOut => [(.io, s!"profile, the parse step timed out after {seconds} s")]
  | .overflow => [(.io, s!"profile, the parse step's frame passed frameBytes {frameBytes}")]
  | .invalid => [(.io, "profile, the parse step's frame is invalid")]
  | .framed n o =>
    (if o.status.child.helperExit == n then []
      else [(.io, "profile, the parse step's frame is invalid")]) ++
      (match o.status.child with
      | .signaled k => [(.io, s!"profile, the parse step died by signal {k}")]
      | .notStarted r => [(.io, s!"profile, the parse step did not start: {r}")]
      | .exited c =>
        (if o.status.workFull || o.status.tmpFull then
            [(.io, "profile, the parse step exceeded a size cap")]
          else []) ++
          if c == 0 then [] else [(.io, s!"profile, the parse step exited with code {c}")]) ++
      (match o.files.lookup "results.json" with
      | some _ => []
      | none => [(.io, "profile, the parse step wrote no result record")]) ++
      match least ((o.files.map (·.1)).filter (· != "results.json")) with
      | some p => [(.io, s!"profile, the parse step wrote {p} beside the result record")]
      | none => []

/-- The record's bytes a run carries (`results.json` in its frame). -/
def recordBytes : Run → Option ByteArray
  | .framed _ o => o.files.lookup "results.json"
  | _ => none

/-- B3 over P5b's intake of the record bytes: an unreadable or mis-bound record = infrastructure
naming the intake's reason; accepted → the compile may start; refused → NOT PROVEN at the record's
location + cause; P6's `over` = infrastructure naming the batch cap. -/
def outcomeVerdict (req : Request) (digest : String) (b : ByteArray) : Verdict :=
  match intake profileId req digest b with
  | .error e => .infra .io s!"profile, the result record {e.text}"
  | .ok r =>
    match r.outcome with
    | .accepted => .accepted r
    | .refused f => .refused r f
    | .over => .infra .io s!"profile, the batch passed batchNodes {req.limits.batchNodes}"

/-- The supervisor's verdict: P5c's first failure, else the record's verdict (no failure ⇒ the run
carries `results.json`: `judgeRecord`, so the last arm is never taken). -/
def judgeSpec (req : Request) (digest : String) (seconds frameBytes : Nat) (run : Run) : Verdict :=
  match (failures seconds frameBytes run).head?, recordBytes run with
  | some e, _ => .infra e.1 e.2
  | none, some b => outcomeVerdict req digest b
  | none, none => .infra .io "profile, the parse step wrote no result record"

/-- C1's header stage over the observations in batch order: a module whose header was never
observed stops it short (no outcome); its stop event or its header's first finding
(`headerRules`) ends it. -/
def headSpec (role : Role) (lib batch : List String) : List Observed → Stage
  | [] => .clean
  | o :: os =>
    match o.head with
    | none => .short
    | some (.stop e) => .event o.module e
    | some (.tree h _) =>
      match (headerRules role lib batch o.module h).head? with
      | some f => .event o.module (.finding f)
      | none => headSpec role lib batch os

/-- C1's body stage over the observations in batch order: the first module whose observed state
holds an event; a module stopped short of its end with none = no outcome. -/
def bodySpec : List Observed → Stage
  | [] => .clean
  | o :: os =>
    match o.state.event with
    | some e => .event o.module e
    | none => if o.ended then bodySpec os else .short

/-- C1 + P5b: the batch — the observations name the request's modules in batch order, else no
outcome; the header stage's first event (its module's outcome, no grammar), else the body stage's,
else accepted; once the header stage is clean, every module's grammar (P3). -/
def concludeSpec (req : Request) (obs : List Observed) : Option (Outcome × List (List String)) :=
  if obs.map (·.module) = req.modules.map (·.module) then
    match headSpec req.role (req.library.map (·.module)) (req.modules.map (·.module)) obs with
    | .short => none
    | .event m e => some (outcomeOf m e, obs.map fun _ => [])
    | .clean =>
      match bodySpec obs with
      | .short => none
      | .event m e => some (outcomeOf m e, grammars req obs)
      | .clean => some (.accepted, grammars req obs)
  else none

end FvdepAudit.Profile.Barrier.Spec
