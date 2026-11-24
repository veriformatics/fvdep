import FvdepCore.Evidence
import FvdepCore.Profile.Batch
import FvdepCore.Step

/-! The supervisor's side of the parse step (contract `docs/contracts/U6-profile.md` P5a, P5c, B):
the request it writes, the step's disposition (P5c's order), P5b's intake + B3's outcome. Pure. -/

namespace FvdepCore.Profile

open FvdepCore.Evidence

/-- P5a: a batch's request — the library rows + the batch modules (name, S1's digest) each
ascending by name, a module's path = its file (S2), the role's recipe, this profile's id. -/
def requestOf (role : Role) (library : List LibModule) (limits : Limits)
    (mods : List (String × String)) (toolchain : String) : Request :=
  { library := library.mergeSort fun a b => Decidable.decide (a.module ≤ b.module)
    limits
    modules :=
      (mods.mergeSort fun a b => Decidable.decide (a.1 ≤ b.1)).map fun x =>
        ⟨x.1, modulePath x.1, x.2⟩
    profile := profileId
    recipe := role.recipe
    role
    toolchain }

/-- The parse step's run as P5c reads it: bwrap's setup failure (U5 R6's `setupFailed` +
`protocol`), the deadline, a frame over `frameBytes`, an invalid frame, or bwrap's exit code + the
frame read back. -/
inductive Run where
  | setup (detail : String)
  | timedOut
  | overflow
  | invalid
  | framed (exit : Nat) (o : FvdepCore.Step.Output)

/-- The least path by bytes among `ps` (`none` when empty). -/
def least : List String → Option String
  | [] => none
  | p :: ps =>
    match least ps with
    | some q => some (if q < p then q else p)
    | none => some p

/-- P5c in order: bwrap's setup failure, the deadline, the frame over its cap or invalid (a status
the helper's exit code contradicts included: it is not the child's), the child's signal, a child
that never started, a size cap hit, a nonzero exit; then the frame's files: no `results.json`,
another file beside it (the least path); else the record's bytes. -/
def disposition (seconds frameBytes : Nat) : Run → Except (Infra × String) ByteArray
  | .setup d => .error (.sandboxSetup, s!"profile, {d}")
  | .timedOut => .error (.io, s!"profile, the parse step timed out after {seconds} s")
  | .overflow => .error (.io, s!"profile, the parse step's frame passed frameBytes {frameBytes}")
  | .invalid => .error (.io, "profile, the parse step's frame is invalid")
  | .framed n o =>
    if o.status.child.helperExit != n then
      .error (.io, "profile, the parse step's frame is invalid")
    else
      match o.status.child with
      | .signaled k => .error (.io, s!"profile, the parse step died by signal {k}")
      | .notStarted r => .error (.io, s!"profile, the parse step did not start: {r}")
      | .exited c =>
        if o.status.workFull || o.status.tmpFull then
          .error (.io, "profile, the parse step exceeded a size cap")
        else
          if c != 0 then .error (.io, s!"profile, the parse step exited with code {c}")
          else
            match o.files.lookup "results.json" with
            | none => .error (.io, "profile, the parse step wrote no result record")
            | some b =>
              match least ((o.files.map (·.1)).filter (· != "results.json")) with
              | some p =>
                .error (.io, s!"profile, the parse step wrote {p} beside the result record")
              | none => .ok b

/-- B3: what a batch's profile check decides — the compile may start, a refusal (NOT PROVEN at the
record's location + cause), or infrastructure (exit 2). -/
inductive Verdict where
  | accepted (r : Record)
  | refused (r : Record) (f : Refusal)
  | infra (code : Infra) (detail : String)

/-- P5b's intake, then B3: the record bytes `b` for `req` (the SHA-256 of the request bytes =
`digest`) → the verdict; P6's `over` = infrastructure naming the batch cap. -/
def verdictOf (req : Request) (digest : String) (b : ByteArray) : Verdict :=
  match intake profileId req digest b with
  | .error e => .infra .io s!"profile, the result record {e.text}"
  | .ok r =>
    match r.outcome with
    | .accepted => .accepted r
    | .refused f => .refused r f
    | .over => .infra .io s!"profile, the batch passed batchNodes {req.limits.batchNodes}"

/-- P5c, then `verdictOf`. -/
def judge (req : Request) (digest : String) (seconds frameBytes : Nat) (run : Run) : Verdict :=
  match disposition seconds frameBytes run with
  | .error e => .infra e.1 e.2
  | .ok b => verdictOf req digest b

end FvdepCore.Profile
