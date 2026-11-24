import FvdepCore.Profile.Record

/-! U6 P5b (contract `docs/contracts/U6-profile.md` P5b): the supervisor's intake of a result
record, written apart from `FvdepCore.Profile.intake` — every binding check of a read record listed
in P5b's order, the first failing one = the refusal. -/

namespace FvdepAudit.Profile.Spec

open FvdepCore.Profile

/-- Each module's name check, positions numbered from `i`. -/
def nameChecks (i : Nat) (ms : List ModuleRec) (qs : List ReqModule) : List (Bool × IntakeError) :=
  ((ms.zip qs).zipIdx i).map fun p =>
    (p.1.1.module == p.1.2.module, .name p.1.1.module p.2 p.1.2.module)

/-- Each module's digest check. -/
def digestChecks (ms : List ModuleRec) (qs : List ReqModule) : List (Bool × IntakeError) :=
  (ms.zip qs).map fun p => (p.1.sha256 == p.2.sha256, .digest p.1.sha256 p.1.module p.2.sha256)

/-- A refusal's module inside the batch. -/
def outsideChecks (req : Request) (r : Record) : List (Bool × IntakeError) :=
  match r.outcome with
  | .refused f => [(req.modules.any (·.module == f.module), .outside f.module)]
  | _ => []

/-- P5b's binding checks of the record `r` read for `req` (whose request bytes hash to `digest`)
under the supervisor's `profile`, in order, each with the failure it names: the profile, the
request digest, the recipe, the module count, then every module's name (1-based position), then
every module's digest, then a refusal's module inside the batch. -/
def checks (profile : String) (req : Request) (digest : String) (r : Record) :
    List (Bool × IntakeError) :=
  [(r.profile == profile, .profile r.profile), (r.request == digest, .request r.request digest),
      (r.recipe == req.recipe, .recipe r.recipe),
      (r.modules.length == req.modules.length, .count r.modules.length req.modules.length)] ++
    nameChecks 1 r.modules req.modules ++
    digestChecks r.modules req.modules ++
    outsideChecks req r

/-- P5b's intake of the record bytes `b`: unreadable → malformed; read → its first failing check,
else the record. -/
def intake (profile : String) (req : Request) (digest : String) (b : ByteArray) :
    Except IntakeError Record :=
  match readRecord b with
  | none => .error .malformed
  | some r =>
    match (checks profile req digest r).find? (fun c => !c.1) with
    | some c => .error c.2
    | none => .ok r

end FvdepAudit.Profile.Spec
