import FvdepAudit.Doc.Proof.Envelope
import FvdepAudit.Doc.Proof.Lock
import FvdepAudit.Json.Proof.Access
import FvdepAudit.Json.Proof.Corollaries
import FvdepLedger.Types
import Main

/-! fvdep's coverage ledger (contract `docs/contracts/U2-core.md` L1; rendered into
`docs/verification.md` by `fvdep-ledger --write`). Each statement = a claim's exact proposition; the
checker holds each named theorem's type equal to it. -/

namespace FvdepLedger.Rows

open FvdepCore

/-- U1 K2: every invocation writes one stream alone. -/
def cliStreams : Prop :=
  ∀ args : List String,
    (Cli.run args).exit = 0 ∧ (Cli.run args).stderr = "" ∨
      (Cli.run args).exit = 2 ∧ (Cli.run args).stdout = "" ∧ (Cli.run args).stderr = Cli.usage

/-- U2 X5: a completed run of the CLI plan performs exactly the outcome's outputs, then exits with
its code. -/
def cliPlanComplete : Prop :=
  ∀ (args : List String) (evs : List (Eff × Response)) (code : UInt32),
    Plan.Runs (Cli.plan args) evs (some code) ↔
      evs = Cli.outputs (Cli.run args) ∧ code = (Cli.run args).exit

/-- U2 X5: an interrupted run performs a prefix of the outcome's outputs. -/
def cliPlanInterrupted : Prop :=
  ∀ (args : List String) (evs : List (Eff × Response)),
    Plan.Runs (Cli.plan args) evs none → evs <+: Cli.outputs (Cli.run args)

/-- U2 X1: a finished plan performs nothing + yields its value. -/
def planPure : Prop :=
  ∀ {α : Type} (a : α) (evs : List (Eff × Response)) (r : Option α),
    Plan.Runs (.pure a) evs r ↔ evs = [] ∧ r = some a

/-- U2 X1: one step = interrupted before the effect, or the effect with a fitting response, then the
rest. -/
def planStep : Prop :=
  ∀ {α : Type} (e : Eff) (k : Response → Plan α) (evs : List (Eff × Response)) (r : Option α),
    Plan.Runs (.step e k) evs r ↔
      evs = [] ∧ r = none ∨
        ∃ resp rest, evs = (e, resp) :: rest ∧ Fits e resp ∧ Plan.Runs (k resp) rest r

/-- U2 X1: a completed run of `p >>= f` = a completed run of `p`, then of `f` on its value. -/
def planBindSome : Prop :=
  ∀ {α β : Type} (p : Plan α) (f : α → Plan β) (evs : List (Eff × Response)) (b : β),
    Plan.Runs (p.bind f) evs (some b) ↔
      ∃ evs₁ evs₂ a, evs = evs₁ ++ evs₂ ∧ Plan.Runs p evs₁ (some a) ∧ Plan.Runs (f a) evs₂ (some b)

/-- U2 X1: an interrupted run of `p >>= f` = an interrupted `p`, or a completed `p`, then an
interrupted `f`. -/
def planBindNone : Prop :=
  ∀ {α β : Type} (p : Plan α) (f : α → Plan β) (evs : List (Eff × Response)),
    Plan.Runs (p.bind f) evs none ↔
      Plan.Runs p evs none ∨
        ∃ evs₁ evs₂ a, evs = evs₁ ++ evs₂ ∧ Plan.Runs p evs₁ (some a) ∧ Plan.Runs (f a) evs₂ none

end FvdepLedger.Rows

namespace FvdepLedger.Rows.IdsClaims

open FvdepCore.Ids

/-- I1: printing then parsing gives the module id back. -/
def moduleIdRoundTrip : Prop := ∀ (m : ModuleId), ModuleId.parse (toString m) = some m

/-- I1: a parsed module id prints back to exactly the text. -/
def moduleIdCanonical : Prop :=
  ∀ {s : String} {m : ModuleId} (_h : ModuleId.parse s = some m), toString m = s

/-- I2: printing then parsing gives the version back. -/
def versionRoundTrip : Prop := ∀ (v : EntryVersion), EntryVersion.parse (toString v) = some v

/-- I2: a parsed version prints back to exactly the text. -/
def versionCanonical : Prop :=
  ∀ {s : String} {v : EntryVersion} (_h : EntryVersion.parse s = some v), toString v = s

/-- I2: the version order is total. -/
def versionTotal : Prop := ∀ (a b : EntryVersion), a.le b ∨ b.le a

/-- I2: the version order is antisymmetric. -/
def versionAntisymm : Prop := ∀ (a b : EntryVersion) (_h₁ : a.le b) (_h₂ : b.le a), a = b

/-- I2: the version order is transitive. -/
def versionTrans : Prop := ∀ (a b c : EntryVersion) (_h₁ : a.le b) (_h₂ : b.le c), a.le c

/-- I2: `compare` agrees with the order. -/
def versionCompare : Prop :=
  ∀ (a b : EntryVersion),
    (EntryVersion.cmp a b ≠ .gt ↔ a.le b) ∧ (EntryVersion.cmp a b = .eq ↔ a = b)

/-- I3: distinct entries never share a Lean module. -/
def leanModuleInjective : Prop :=
  ∀ {m m' : ModuleId} {v v' : EntryVersion} (_h : leanModule m v = leanModule m' v'),
    m = m' ∧ v = v'

/-- I4: printing then parsing gives the reference back. -/
def refRoundTrip : Prop := ∀ (r : ModuleRef), ModuleRef.parse (toString r) = some r

/-- I4: a parsed reference prints back to exactly the text. -/
def refCanonical : Prop :=
  ∀ {s : String} {r : ModuleRef} (_h : ModuleRef.parse s = some r), toString r = s

/-- I5: a one-component name is reserved by its spelling. -/
def reservedRoot : Prop :=
  ∀ (s : String),
    reserved (.str .anonymous s) =
      (["Init", "Std", "Lean", "Lake"].contains s || s.startsWith "Fvdep")

/-- I5: only the first component decides. -/
def reservedPrefix : Prop :=
  ∀ (p : Lean.Name) (s : String) (_hp : p ≠ .anonymous), reserved (.str p s) = reserved p

/-- I5: a numeric component after the first never decides either. -/
def reservedNum : Prop :=
  ∀ (p : Lean.Name) (k : Nat) (_hp : p ≠ .anonymous), reserved (.num p k) = reserved p

/-- I5: the empty name is never reserved. -/
def reservedAnonymous : Prop := reserved .anonymous = false

/-- I5: a numeric first component is never reserved. -/
def reservedNumRoot : Prop := ∀ (k : Nat), reserved (.num .anonymous k) = false

/-- I6: printing then parsing gives the commit back. -/
def commitRoundTrip : Prop := ∀ (c : Commit), Commit.parse (toString c) = some c

/-- I6: a parsed commit prints back to exactly the text. -/
def commitCanonical : Prop :=
  ∀ {s : String} {c : Commit} (_h : Commit.parse s = some c), toString c = s

end FvdepLedger.Rows.IdsClaims

namespace FvdepLedger.Rows.EvidenceClaims

open FvdepCore.Ids FvdepCore.Evidence

/-- E3: observations under another key never change a result. -/
def isolation : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation),
    result c os = result c (os.filter fun o => o.key == c)

/-- E3: the result depends on the attributed observations alone (challenge key + export
bindings). -/
def attribution : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation), result c (attributed c os) = result c os

/-- E3: an identical duplicate of an observation counts once. -/
def duplicates : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation) (o : Observation) (_ho : o ∈ os),
    result c (os ++ [o]) = result c os

/-- E6: PROVEN ⇔ a proof request whose observations under its key hold every observation of a
passing proof (axioms inside the allowlist) + nothing else but identical duplicates,
observations bound to other exports + comparisons. -/
def provenIff : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation),
    result c os = .verdict .proven [] ↔
      c.request.decl.kind = .proof ∧
        ∃ e1 e2 names,
          (∀ a ∈ names, a ∈ c.profile.allowedAxioms) ∧
            (∀ o ∈ passing e1 e2 names, o ∈ keyed c os) ∧
            ∀ o ∈ keyed c os, o ∈ passing e1 e2 names ∨ Elsewhere e1 e2 o

/-- E5 + E5a: the first attributed infrastructure observation's code beside the walk's negatives,
else PROVEN, NOT PROVEN with the failed phase's reasons, or `internal` for a missing phase or a
protocol violation (negatives kept); the walk obeys `Spec`. -/
def phaseRule : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation) (_hk : c.request.decl.kind = .proof),
    ∃ w,
      Spec c.profile.allowedAxioms (attributedObs c os) w ∧
        (∀ code d rest,
          infras (attributedObs c os) = (code, d) :: rest →
            result c os = .infra ⟨infraCode code, d⟩ (negatives w)) ∧
        (infras (attributedObs c os) = [] →
          (w = .passed → result c os = .verdict .proven []) ∧
            (∀ rs, w = .failed rs → result c os = .verdict .notProven rs) ∧
            (∀ ph ns, w = .missing ph ns → ∃ d, result c os = .infra ⟨.internal, d⟩ ns) ∧
            ∀ d ns, w = .protocol d ns → result c os = .infra ⟨.internal, d⟩ ns)

/-- E4: a verdict names reasons ⇔ it is NOT PROVEN or MISMATCH. -/
def reasonsShape : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation) (v : Verdict) (rs : List Reason)
    (_h : result c os = .verdict v rs), rs ≠ [] ↔ v = .notProven ∨ v = .mismatch

/-- E6: an attributed infrastructure observation ⇒ an infrastructure result. -/
def infraWins : Prop :=
  ∀ (c : ChallengeKey) (os : List Observation) (_h : infras (keyed c os) ≠ []),
    ∃ cause negs, result c os = .infra cause negs

/-- E5: kernel decline + reject keep their own codes. -/
def declineApart : Prop :=
  ∀ (k : Kernel) (st : KernelStatus),
    ((kernelReason k st).map (·.code) = some .kernelReject ↔ st = .reject) ∧
      ((kernelReason k st).map (·.code) = some .kernelDecline ↔ ∃ d, st = .decline d)

/-- E7: MATCHED ⇔ supported comparisons, all matched, no infrastructure failure. -/
def diffMatched : Prop :=
  ∀ (adapter : Option Digest) (ks : List Obs),
    diffResult adapter ks = .verdict .matched [] ↔
      infras ks = [] ∧
        supported (comparisons adapter ks) ≠ [] ∧
        (supported (comparisons adapter ks)).filterMap mismatchReason = []

/-- E7: MISMATCH ⇔ a supported comparison differs, no infrastructure failure. -/
def diffMismatch : Prop :=
  ∀ (adapter : Option Digest) (ks : List Obs),
    (∃ rs, diffResult adapter ks = .verdict .mismatch rs) ↔
      infras ks = [] ∧ (supported (comparisons adapter ks)).filterMap mismatchReason ≠ []

/-- E7: differential evidence is never PROVEN. -/
def diffNotProven : Prop :=
  ∀ (adapter : Option Digest) (ks : List Obs) (rs : List Reason),
    diffResult adapter ks ≠ .verdict .proven rs

/-- E7: an infrastructure observation ⇒ infrastructure with its code, the mismatches seen kept. -/
def diffInfra : Prop :=
  ∀ (adapter : Option Digest) (ks : List Obs) (code : Infra) (d : String)
    (rest : List (Infra × String)) (_h : infras ks = (code, d) :: rest),
    diffResult adapter ks =
      .infra ⟨infraCode code, d⟩ ((supported (comparisons adapter ks)).filterMap mismatchReason)

/-- E7: no supported comparison ⇒ infrastructure `adapter`. -/
def diffUnsupported : Prop :=
  ∀ (adapter : Option Digest) (ks : List Obs) (_h : infras ks = [])
    (_hs : supported (comparisons adapter ks) = []),
    diffResult adapter ks = .infra ⟨.adapter, "no supported comparison"⟩ []

/-- E7: a proof request never reads comparisons. -/
def proofIgnoresComparisons : Prop :=
  ∀ (allowed : List String) (a : Digest) (op i : String) (r : Comparison) (ks : List Obs),
    proofResult allowed (.compare a op i r :: ks) = proofResult allowed ks

end FvdepLedger.Rows.EvidenceClaims

namespace FvdepLedger.Rows.StatusClaims

open FvdepCore FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status

/-- P1: proof required ⇔ PROVEN + not retracted. -/
def meetsRequired : Prop :=
  ∀ (r : Result) (ret : Option Retraction),
    meets .required r ret = true ↔ (∃ rs, r = .verdict .proven rs) ∧ ret = none

/-- P1: development ⇔ PROVEN or MATCHED. -/
def meetsDevelopment : Prop :=
  ∀ (r : Result) (ret : Option Retraction),
    meets .development r ret = true ↔ ∃ rs, r = .verdict .proven rs ∨ r = .verdict .matched rs

/-- P2: exit 0 ⇔ every module 0. -/
def exitOk : Prop := ∀ (es : List Exit), commandExit es = .ok ↔ ∀ e ∈ es, e = .ok

/-- P2: exit 2 ⇔ some module 2. -/
def exitFailure : Prop := ∀ (es : List Exit), commandExit es = .failure ↔ .failure ∈ es

/-- P2: the exit codes 0, 1, 2. -/
def exitCodes : Prop := Exit.code .ok = 0 ∧ Exit.code .negative = 1 ∧ Exit.code .failure = 2

/-- P2: a module exits 2 ⇔ its result is infrastructure. -/
def moduleFailure : Prop :=
  ∀ (p : Policy) (r : Result) (ret : Option Retraction),
    moduleExit p r ret = .failure ↔ ∃ c ns, r = .infra c ns

/-- P2: a module exits 0 ⇔ its result meets the policy. -/
def moduleOk : Prop :=
  ∀ (p : Policy) (r : Result) (ret : Option Retraction),
    moduleExit p r ret = .ok ↔ meets p r ret = true

/-- P2 + P9: `check` exits 0 ⇔ every fresh result meets the policy. -/
def checkOk : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)),
    checkExit p rs = .ok ↔ ∀ x ∈ rs, meets p x.1 x.2 = true

/-- P2 + P9: `check` exits 2 ⇔ some fresh result is infrastructure. -/
def checkFailure : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)),
    checkExit p rs = .failure ↔ ∃ x ∈ rs, ∃ c ns, x.1 = .infra c ns

/-- P3: a proof receipt ⇔ a well-shaped proof request PROVEN with its exports. -/
def proofReceipt : Prop :=
  ∀ (c : Common) (r : Result) (ex : Option (Digest × Digest)) (c' : Common) (e1 e2 : Digest),
    receiptOf c r ex = some (.proof c' e1 e2) ↔
      shaped c.request = true ∧
        c.request.decl.kind = .proof ∧ (∃ rs, r = .verdict .proven rs) ∧ ex = some (e1, e2) ∧ c' = c

/-- P3: a differential receipt ⇔ a well-shaped differential request MATCHED. -/
def differentialReceipt : Prop :=
  ∀ (c : Common) (r : Result) (ex : Option (Digest × Digest)) (c' : Common),
    receiptOf c r ex = some (.differential c') ↔
      shaped c.request = true ∧
        c.request.decl.kind = .differential ∧ (∃ rs, r = .verdict .matched rs) ∧ c' = c

/-- P4: no change ⇔ same request, library + profile. -/
def noChanges : Prop :=
  ∀ (rc : Receipt) (i : Inputs),
    changes rc i = [] ↔
      rc.common.request = i.request ∧ rc.common.library = i.library ∧ rc.common.profile = i.profile

/-- P4: the changes = exactly the differing input fields, in report order. -/
def changesExact : Prop :=
  ∀ (rc : Receipt) (i : Inputs), changes rc i = inputFields.filter (inputDiffers rc i)

/-- P5: exactly the disagreements, each with its cause. -/
def agreementExact : Prop :=
  ∀ (mf : Manifest) (lk : Lock) (d : Disagreement),
    d ∈ agreement mf lk ↔
      d = .library ∧ lk.library ≠ mf.library ∨
        (∃ x ∈ mf.decls,
          entriesFor lk x.module = [] ∧ d = .missing x.module ∨
            2 ≤ (entriesFor lk x.module).length ∧ d = .duplicate x.module ∨
            ∃ rc,
              entriesFor lk x.module = [rc] ∧
                rc.common.request.decl ≠ x ∧ d = .declaration x.module) ∨
        ∃ rc ∈ lk.entries,
          (∀ x ∈ mf.decls, x.module ≠ rc.common.request.decl.module) ∧
            d = .extra rc.common.request.decl.module

/-- P8: a retraction = the first notice naming (id, version), its reason + replacement. -/
def retractionFirst : Prop :=
  ∀ (s : Snapshot) (m : ModuleId) (v : EntryVersion) (r : Retraction),
    retraction s m v = some r ↔
      ∃ pre n post,
        s.notices = pre ++ n :: post ∧
          (n.module = m ∧ n.version = v) ∧
          (∀ x ∈ pre, ¬(x.module = m ∧ x.version = v)) ∧ r = ⟨n.reason, n.replacement⟩

/-- P8: no notice names (id, version) ⇒ no retraction. -/
def retractionNone : Prop :=
  ∀ (s : Snapshot) (m : ModuleId) (v : EntryVersion),
    retraction s m v = none ↔ ∀ n ∈ s.notices, ¬(n.module = m ∧ n.version = v)

/-- P8: appending notices never removes a retraction. -/
def retractionMonotone : Prop :=
  ∀ (s : Snapshot) (more : List Notice) (m : ModuleId) (v : EntryVersion) (r : Retraction)
    (_h : retraction s m v = some r), retraction ⟨s.notices ++ more⟩ m v = some r

/-- P8: a listed (id, version) is retracted. -/
def retractionListed : Prop :=
  ∀ (s : Snapshot) (n : Notice) (_h : n ∈ s.notices), retraction s n.module n.version ≠ none

/-- P6: no status reason ⇔ delivered. -/
def deliveredReason : Prop :=
  ∀ (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs),
    statusReason mf lk s i = none ↔ Delivered mf lk s i

/-- P6: the status reason = the first that applies, with its payload. -/
def statusReasonOrder : Prop :=
  ∀ (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) (r : StatusReason),
    statusReason mf lk s i = some r ↔
      agreement mf lk ≠ [] ∧ r = .disagree (agreement mf lk) ∨
        agreement mf lk = [] ∧
          ((entriesFor lk i.request.decl.module).head? = none ∧ r = .noEntry ∨
            ∃ rc,
              (entriesFor lk i.request.decl.module).head? = some rc ∧
                (rc.common.profile ≠ i.profile ∧ r = .olderProfile ∨
                  rc.common.profile = i.profile ∧
                    (changes rc i ≠ [] ∧ r = .stale (changes rc i) ∨
                      changes rc i = [] ∧
                        ((∃ c, rc = .differential c) ∧ r = .testEvidenceOnly ∨
                          ∃ c e1 e2 rt,
                            rc = .proof c e1 e2 ∧
                              retraction s i.request.decl.module i.request.decl.version = some rt ∧
                              r = .retracted rt))))

/-- P8: a retracted module is never delivered. -/
def retractedUndelivered : Prop :=
  ∀ (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) (n : Notice) (_hn : n ∈ s.notices)
    (_hm : n.module = i.request.decl.module) (_hv : n.version = i.request.decl.version),
    ¬Delivered mf lk s i

/-- P7: `status` exit 0 under proof policy ⇔ the files agree + every module delivered. -/
def statusRequired : Prop :=
  ∀ (mf : Manifest) (lk : Lock) (s : Snapshot) (is : List Inputs),
    statusExit .required mf lk s is = .ok ↔ agreement mf lk = [] ∧ ∀ i ∈ is, Delivered mf lk s i

/-- P7: `status` exit 0 under development policy ⇔ the files agree + every module's receipt
current. -/
def statusDevelopment : Prop :=
  ∀ (mf : Manifest) (lk : Lock) (s : Snapshot) (is : List Inputs),
    statusExit .development mf lk s is = .ok ↔
      agreement mf lk = [] ∧
        ∀ i ∈ is, ∃ rc, (entriesFor lk i.request.decl.module).head? = some rc ∧ changes rc i = []

/-- P9: the lock is written ⇔ every module meets the policy. -/
def lockCommit : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)),
    lockDecision p rs = .commit ↔ ∀ x ∈ rs, meets p x.1 x.2 = true

/-- P9: a refusal exits 1 or 2. -/
def lockRefuse : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (e : Exit)
    (_h : lockDecision p rs = .refuse e), e = .negative ∨ e = .failure

/-- P9: a refusal ⇔ some module misses the policy; its exit = `check`'s. -/
def lockRefuseExact : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (e : Exit),
    lockDecision p rs = .refuse e ↔ (∃ x ∈ rs, meets p x.1 x.2 = false) ∧ e = checkExit p rs

/-- P9: a lock entry is current ⇔ no input, policy or export changed. -/
def lockCurrent : Prop :=
  ∀ (rc fresh : Receipt),
    lockState (some rc) fresh = .current ↔
      changes rc fresh.inputs = [] ∧
        rc.common.policy = fresh.common.policy ∧ rc.exports = fresh.exports

/-- P9: an out-of-date lock entry always names what changed. -/
def lockOutOfDate : Prop :=
  ∀ (rc fresh : Receipt) (cs : List Change),
    lockState (some rc) fresh = .outOfDate cs ↔ cs ≠ [] ∧ cs = lockChanges rc fresh

/-- P9: the lock changes = exactly the differing fields, in report order. -/
def lockChangesExact : Prop :=
  ∀ (rc fresh : Receipt), lockChanges rc fresh = lockFields.filter (lockDiffers rc fresh)

/-- X2: a completed commit replaced every file, in order. -/
def commitAll : Prop :=
  ∀ (fs : List (ProjectFile × ByteArray)) (evs : List (Eff × Response))
    (_h : Plan.Runs (commitFiles fs) evs (some none)),
    evs = fs.map fun x => (Eff.replace x.1 x.2, Response.replace (.ok ()))

/-- X2: a failed replace ends the writes. -/
def commitStops : Prop :=
  ∀ (fs : List (ProjectFile × ByteArray)) (evs : List (Eff × Response)) (f : ProjectFile)
    (e : String) (_h : Plan.Runs (commitFiles fs) evs (some (some (f, e)))),
    ∃ pre b,
      evs = pre ++ [(Eff.replace f b, Response.replace (.error e))] ∧
        ∀ x ∈ pre, x.2 = Response.replace (.ok ())

/-- X2: the commit performs its replaces alone, in order. -/
def commitOrder : Prop :=
  ∀ (fs : List (ProjectFile × ByteArray)) (evs : List (Eff × Response))
    (r : Option (Option (ProjectFile × String))) (_h : Plan.Runs (commitFiles fs) evs r),
    evs.map Prod.fst <+: fs.map fun x => Eff.replace x.1 x.2

/-- X3: a refusal performs no effect. -/
def refuseNoEffect : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet) (e : Exit)
    (_hd : lockDecision p rs = .refuse e) (evs : List (Eff × Response)) (r : Option Exit)
    (_h : Plan.Runs (authorize p rs ws) evs r), evs = [] ∧ (r = some e)

/-- X3: every replace follows a commit decision + writes the write set's bytes. -/
def replaceAfterDecision : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (evs : List (Eff × Response)) (r : Option Exit) (_h : Plan.Runs (authorize p rs ws) evs r)
    (f : ProjectFile) (b : ByteArray) (resp : Response) (_hm : (Eff.replace f b, resp) ∈ evs),
    lockDecision p rs = .commit ∧ ws.bytes f = some b

/-- X3: a complete run after a commit decision: every replace succeeded + exit 0, or the first
failed replace, its diagnostic on stderr + exit 2. -/
def commitComplete : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (evs : List (Eff × Response)) (x : Exit) (_hd : lockDecision p rs = .commit)
    (_h : Plan.Runs (authorize p rs ws) evs (some x)),
    x = .ok ∧ evs = ws.files.map (fun f => (Eff.replace f.1 f.2, Response.replace (.ok ()))) ∨
      x = .failure ∧
        ∃ pre f b e resp,
          evs =
              pre ++
                [(Eff.replace f b, Response.replace (.error e)),
                  (Eff.err
                      (s!"Could not finish writing {fileName f}: {e}. " ++
                        "Run \"fvdep status\" to see the state.\n"),
                    resp)] ∧
            ∀ y ∈ pre, y.2 = Response.replace (.ok ())

/-- X3: with every replace succeeding, a commit decision writes the write set's files in canonical
order, then exits 0. -/
def commitWrites : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (_hd : lockDecision p rs = .commit),
    Plan.Runs (authorize p rs ws)
      (ws.files.map fun f => (Eff.replace f.1 f.2, Response.replace (.ok ()))) (some .ok)

/-- X4: after any run each file holds its old or its new bytes. -/
def oldOrNew : Prop :=
  ∀ (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (evs : List (Eff × Response)) (r : Option Exit) (_h : Plan.Runs (authorize p rs ws) evs r)
    (f : ProjectFile) (old c : ByteArray) (_hh : Holds f old evs c),
    c = old ∨ ∃ b, ws.bytes f = some b ∧ c = b

end FvdepLedger.Rows.StatusClaims

namespace FvdepLedger.Rows.JsonClaims

open FvdepCore.Json

/-- J6: decoding returns exactly the outcome the byte grammar assigns (total + deterministic; errors
+ the duplicate-key site included). -/
def decodeExact : Prop :=
  ∀ (b : ByteArray) (r : Except DecodeError Value),
    decode b = r ↔ FvdepAudit.Json.Spec.Outcome b.data.toList r

/-- J1, J6: a successful decode returns a valid value. -/
def decodeValid : Prop :=
  ∀ (b : ByteArray) (v : Value), decode b = .ok v → FvdepAudit.Json.Spec.Valid v

/-- J6: the grammar is deterministic: a text denotes one value (members in text order). -/
def textUnique : Prop :=
  ∀ (bs : FvdepAudit.Json.Spec.Bytes) (v w : Value),
    FvdepAudit.Json.Spec.Text bs v → FvdepAudit.Json.Spec.Text bs w → v = w

/-- J6: the shipped printer emits exactly the reviewed canonical text. -/
def printExact : Prop := ∀ v : Value, (print v).data.toList = FvdepAudit.Json.Spec.canonical v

/-- J6: the canonical text of a valid value decodes, by the grammar, to that value. -/
def roundTrip : Prop :=
  ∀ v : Value,
    FvdepAudit.Json.Spec.Valid v →
      FvdepAudit.Json.Spec.Outcome (FvdepAudit.Json.Spec.canonical v) (.ok v)

/-- J6 corollary: shipped `print`, then shipped `decode`, returns a valid value unchanged. -/
def printDecode : Prop := ∀ v : Value, FvdepAudit.Json.Spec.Valid v → decode (print v) = .ok v

/-- J6 corollary: canonical text tells valid values apart. -/
def canonicalInjective : Prop :=
  ∀ v w : Value,
    FvdepAudit.Json.Spec.Valid v →
      FvdepAudit.Json.Spec.Valid w →
      FvdepAudit.Json.Spec.canonical v = FvdepAudit.Json.Spec.canonical w → v = w

/-- J5: `Value.object ms` = `ms` stably sorted by key: a permutation, keys ascending, members with
equal keys in their original order (children untouched). -/
def objectLaw : Prop :=
  ∀ ms : List (String × Value),
    ∃ ms',
      Value.object ms = .obj ms' ∧
        ms'.Perm ms ∧
        ms'.Pairwise (fun a b => a.1 ≤ b.1) ∧ ∀ k, ms'.filter (·.1 == k) = ms.filter (·.1 == k)

/-- J5: `get? key` = the value of the first member whose key equals `key`; `none` for an absent key
or a non-object. -/
def getLaw : Prop :=
  (∀ (ms : List (String × Value)) (k : String) (w : Value),
      (Value.obj ms).get? k = some w ↔
        ∃ pre post, ms = pre ++ (k, w) :: post ∧ ∀ p ∈ pre, p.1 ≠ k) ∧
    (∀ (ms : List (String × Value)) (k : String),
      (Value.obj ms).get? k = none ↔ ∀ p ∈ ms, p.1 ≠ k) ∧
    ∀ (v : Value) (k : String), (∀ ms, v ≠ .obj ms) → v.get? k = none

/-- J5: each projection returns exactly its constructor's payload, `none` for the rest. -/
def asLaws : Prop :=
  (∀ v b, Value.asBool? v = some b ↔ v = .bool b) ∧
    (∀ v n, Value.asInt? v = some n ↔ v = .int n) ∧
    (∀ v s, Value.asStr? v = some s ↔ v = .str s) ∧
    (∀ v xs, Value.asArr? v = some xs ↔ v = .arr xs) ∧
    ∀ v ms, Value.asObj? v = some ms ↔ v = .obj ms

end FvdepLedger.Rows.JsonClaims

namespace FvdepLedger.Rows.DocClaims

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepAudit.Doc.Spec

/-- D7: a receipt's JSON is exactly its D3 layout (`evidence` = the receipt constructor's kind). -/
def receiptEncodeExact : Prop := ∀ (r : Receipt), r.toJson = receiptLayout r

/-- D7: on a J1-valid value the D5 walk finds no violation exactly when the value is the layout of a
well-formed receipt. -/
def receiptSchemaExact : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v),
    firstViolation receiptTy v = none ↔ ∃ r, ReceiptWF r ∧ v = receiptLayout r

/-- D7: on a J1-valid value, `Receipt.ofJson` accepts exactly the layouts of well-formed receipts,
returning that receipt. -/
def receiptDecodeOk : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v) (r : Receipt),
    Receipt.ofJson v = .ok r ↔ ReceiptWF r ∧ v = receiptLayout r

/-- D7: `Receipt.ofJson` refuses with exactly the walk's first violation (D5 order), on every value.
-/
def receiptDecodeError : Prop :=
  ∀ (v : Value) (e : DocError), Receipt.ofJson v = .error e ↔ firstViolation receiptTy v = some e

/-- D7: a well-formed receipt's JSON is a J1-valid value. -/
def receiptValid : Prop := ∀ (r : Receipt) (_h : ReceiptWF r), FvdepAudit.Json.Spec.Valid r.toJson

/-- D8: `Receipt.wellFormed` decides D2 + D3 well-formedness. -/
def receiptCheck : Prop := ∀ (r : Receipt), r.wellFormed = true ↔ ReceiptWF r

end FvdepLedger.Rows.DocClaims

namespace FvdepLedger.Rows.DocClaims

open FvdepCore.Json FvdepCore.Ids FvdepCore.Evidence FvdepCore.Status FvdepCore.Doc
  FvdepAudit.Doc.Spec

/-- D7: a lock's JSON is exactly its D4 layout. -/
def lockEncodeExact : Prop := ∀ (l : Lock), l.toJson = lockLayout l

/-- D7: on a J1-valid value the D5 walk finds no violation exactly when the value is the layout of a
well-formed lock. -/
def lockSchemaExact : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v),
    firstViolation lockTy v = none ↔ ∃ l, LockWF l ∧ v = lockLayout l

/-- D7: on a J1-valid value, `Lock.ofJson` accepts exactly the layouts of well-formed locks,
returning that lock. -/
def lockDecodeOk : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v) (l : Lock),
    Lock.ofJson v = .ok l ↔ LockWF l ∧ v = lockLayout l

/-- D7: `Lock.ofJson` refuses with exactly the walk's first violation, on every value. -/
def lockDecodeError : Prop :=
  ∀ (v : Value) (e : DocError), Lock.ofJson v = .error e ↔ firstViolation lockTy v = some e

/-- D7: a well-formed lock's JSON is a J1-valid value. -/
def lockValid : Prop := ∀ (l : Lock) (_h : LockWF l), FvdepAudit.Json.Spec.Valid l.toJson

/-- D8: `Lock.wellFormed` decides D2 + D4 well-formedness (receipts + strictly ascending module
ids). -/
def lockCheck : Prop := ∀ (l : Lock), l.wellFormed = true ↔ LockWF l

/-- D7 LockBytes: a well-formed lock's canonical bytes decode back to it. -/
def lockBytesEncode : Prop := ∀ (l : Lock) (_h : LockWF l), decodeLock (encodeLock l) = .ok l

/-- D7 LockBytes: bytes `decodeLock` accepts decode (J3) to the layout of the well-formed lock it
returns. -/
def lockBytesOk : Prop :=
  ∀ (b : ByteArray) (l : Lock) (_h : decodeLock b = .ok l),
    LockWF l ∧ ∃ v, decode b = .ok v ∧ v = lockLayout l

/-- D7 LockBytes: `decodeLock` refuses with J3's text error first, else the walk's first violation.
-/
def lockBytesError : Prop :=
  ∀ (b : ByteArray) (e : LockError),
    decodeLock b = .error e ↔
      (∃ j, decode b = .error j ∧ e = .text j) ∨
        ∃ v d, decode b = .ok v ∧ firstViolation lockTy v = some d ∧ e = .doc d

/-- D7: `Lock.normalize` keeps the library + the receipts (a permutation), orders module ids
nondecreasingly, keeps equal ids in input order. -/
def normalizePreserves : Prop :=
  ∀ (l : Lock),
    l.normalize.library = l.library ∧
      l.normalize.entries.Perm l.entries ∧
      (l.normalize.entries.map idOf).Pairwise (· ≤ ·) ∧
      ∀ a b, [a, b].Sublist l.entries → idOf a = idOf b → [a, b].Sublist l.normalize.entries

/-- D7: normalizing well-formed receipts with distinct module ids gives a well-formed lock. -/
def normalizeSorted : Prop :=
  ∀ (l : Lock) (_hd : (l.entries.map idOf).Nodup) (_hw : ∀ r ∈ l.entries, ReceiptWF r),
    LockWF l.normalize

end FvdepLedger.Rows.DocClaims

namespace FvdepLedger.Rows.DocClaims

open FvdepCore.Ids FvdepCore.Status FvdepCore.Doc FvdepAudit.Doc.Spec FvdepAudit.Json.Spec

/-- D7: the envelope's JSON is exactly its D6 layout (the result members verbatim; diagnostics
clipped). -/
def envelopeEncodeExact : Prop := ∀ (e : Envelope), e.toJson = envelopeLayout e

/-- D8: `Envelope.wellFormed` decides D6 well-formedness. -/
def envelopeCheck : Prop := ∀ (e : Envelope), e.wellFormed = true ↔ EnvelopeWF e

/-- D7: a well-formed envelope's JSON is a J1-valid value. -/
def envelopeValid : Prop := ∀ (e : Envelope) (_h : EnvelopeWF e), Valid e.toJson

end FvdepLedger.Rows.DocClaims

namespace FvdepLedger.Rows.DocClaims

open FvdepCore.Doc FvdepAudit.Doc.Spec

/-- D7: `clip` keeps a text within 65,536 bytes, else its longest scalar-boundary prefix within
65,520 bytes followed by ` [truncated]`. -/
def clipExact : Prop := ∀ (s : String), clip s = clipSpec s

/-- D7: every clipped text fits 65,536 UTF-8 bytes. -/
def clipBound : Prop := ∀ (s : String), (clip s).utf8ByteSize ≤ 65536

end FvdepLedger.Rows.DocClaims

namespace FvdepLedger.Rows

open FvdepCore

def residue : List Residue :=
  [{  id := "interpreter"
      what := "the IO interpreter's effect → primitive mapping (`FvdepIO.Run`)"
      reason :=
        "an IO primitive has no Lean semantics to prove against; the U1 K2 smoke cases test the " ++
          "output mapping (full device, broken pipe)"
      ruling := "the IO interpreter's effect → primitive mapping (tested)"
      boundary := [] },
    { id := "runtime"
      what :=
        "Lean compiler + runtime (compiled code = the kernel definition; string + IO primitives)"
      reason := "the toolchain is trusted (Decisions `Self-verification scope`)"
      ruling := "Lean compiler + runtime"
      boundary := [] },
    { id := "os"
      what := "OS, filesystem + process semantics"
      reason := "outside Lean; fvdep's effects reach them through the interpreter"
      ruling := "OS, filesystem + process semantics"
      boundary := [] },
    { id := "literal"
      what := "literal data (the version string `Fvdep.version`)"
      reason :=
        "a constant has no behaviour to prove; the gate's `meta` stage holds it equal to both " ++
          "lakefiles"
      ruling := "Literal data (the version string) is checked by the gate's `meta` stage"
      boundary := [] }]

def cliRow : Row :=
  { component := `FvdepCore.Cli
    contract := "U1 K2; docs/interface.md §1–§2; U2 X5"
    claim :=
      "Every invocation writes one stream alone: exit 0 with stderr empty, or exit 2 with the " ++
        "usage on stderr + stdout empty. The plan performs exactly the outcome's outputs " ++
        "(stdout, then stderr), an interrupted run a prefix of them; it never reads or replaces " ++
        "a file."
    claims :=
      [(``cliStreams, ``Cli.run_streams), (``cliPlanComplete, ``Cli.plan_complete),
        (``cliPlanInterrupted, ``Cli.plan_interrupted)]
    subject := ``Cli.plan
    path := [``main, ``Cli.plan]
    noCaller := ""
    residue := ["interpreter", "runtime"]
    unproven := [] }

def planRow : Row :=
  { component := `FvdepCore.Plan
    contract := "U2 X1"
    claim :=
      "The trace semantics of effect plans: a finished plan performs nothing; a step is " ++
        "interrupted or performs its effect with a fitting response; runs of `p >>= f` " ++
        "decompose into runs of `p` and of `f`."
    claims :=
      [(``planPure, ``Plan.runs_pure_iff), (``planStep, ``Plan.runs_step_iff),
        (``planBindSome, ``Plan.runs_bind_some), (``planBindNone, ``Plan.runs_bind_none)]
    subject := ``Plan.bind
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def interpreterRow : Row :=
  { component := `FvdepIO.Run
    contract := "U1 K2 (failed output write → exit 2); U2 X6"
    claim :=
      "`main`'s interpreter performs each effect on the real streams; a failed output write " ++
        "exits 2, with `Could not write the output: <reason>.` on stderr unless the reader " ++
        "closed the pipe."
    claims := []
    subject := ``FvdepIO.execute
    path := [``main, ``FvdepIO.execute]
    noCaller := ""
    residue := ["os", "runtime"]
    unproven := ["interpreter"] }

def versionRow : Row :=
  { component := `Fvdep.Version
    contract := "U1 K1–K2"
    claim := "The version string `fvdep --version` prints."
    claims := []
    subject := ``Fvdep.version
    path := []
    noCaller := "support"
    residue := []
    unproven := ["literal"] }

def idsRow : Row :=
  { component := `FvdepCore.Ids
    contract := "U2 I1–I6; docs/library.md Naming; docs/interface.md §3 + §7"
    claim :=
      "Module ids, entry versions, module references + commits parse only their canonical " ++
        "text and print back to it; versions are ordered numerically by field (total, " ++
        "antisymmetric, transitive, `compare` agreeing); distinct entries never share a Lean " ++
        "module; a reserved consumer module name is decided by its first component alone " ++
        "(string, numeric or none)."
    claims :=
      [(``IdsClaims.moduleIdRoundTrip, ``FvdepCore.Ids.ModuleId.parse_toString),
        (``IdsClaims.moduleIdCanonical, ``FvdepCore.Ids.ModuleId.toString_parse),
        (``IdsClaims.versionRoundTrip, ``FvdepCore.Ids.EntryVersion.parse_toString),
        (``IdsClaims.versionCanonical, ``FvdepCore.Ids.EntryVersion.toString_parse),
        (``IdsClaims.versionTotal, ``FvdepCore.Ids.EntryVersion.le_total),
        (``IdsClaims.versionAntisymm, ``FvdepCore.Ids.EntryVersion.le_antisymm),
        (``IdsClaims.versionTrans, ``FvdepCore.Ids.EntryVersion.le_trans),
        (``IdsClaims.versionCompare, ``FvdepCore.Ids.EntryVersion.cmp_spec),
        (``IdsClaims.leanModuleInjective, ``FvdepCore.Ids.leanModule_inj),
        (``IdsClaims.refRoundTrip, ``FvdepCore.Ids.ModuleRef.parse_toString),
        (``IdsClaims.refCanonical, ``FvdepCore.Ids.ModuleRef.toString_parse),
        (``IdsClaims.reservedRoot, ``FvdepCore.Ids.reserved_root),
        (``IdsClaims.reservedPrefix, ``FvdepCore.Ids.reserved_str),
        (``IdsClaims.reservedNum, ``FvdepCore.Ids.reserved_num),
        (``IdsClaims.reservedAnonymous, ``FvdepCore.Ids.reserved_anonymous),
        (``IdsClaims.reservedNumRoot, ``FvdepCore.Ids.reserved_num_root),
        (``IdsClaims.commitRoundTrip, ``FvdepCore.Ids.Commit.parse_toString),
        (``IdsClaims.commitCanonical, ``FvdepCore.Ids.Commit.toString_parse)]
    subject := ``FvdepCore.Ids.ModuleId.parse
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def evidenceRow : Row :=
  { component := `FvdepCore.Evidence
    contract :=
      "U2 E1–E7; Decisions Conformance method + Verification profile; docs/interface.md §4 + §6"
    claim :=
      "A result depends only on the attributed observations (the request's challenge key + " ++
        "export bindings; identical duplicates count once). PROVEN ⇔ a passing proof's " ++
        "observations (implementation profile, both builds, statement, graph, axioms inside " ++
        "the allowlist, all three kernels) with nothing contradicting them. Else the first " ++
        "attributed infrastructure observation (exit 2, negatives kept), else the phase rule: " ++
        "the first failed phase's reasons (NOT PROVEN), a missing phase or a protocol " ++
        "violation → `internal` (negatives kept); reasons appear exactly on NOT PROVEN + " ++
        "MISMATCH. Differential evidence is MATCHED or MISMATCH by its supported comparisons " ++
        "(none → `adapter`), never PROVEN, and proof requests ignore it."
    claims :=
      [(``EvidenceClaims.isolation, ``FvdepCore.Evidence.result_keyed),
        (``EvidenceClaims.attribution, ``FvdepCore.Evidence.result_attributed),
        (``EvidenceClaims.duplicates, ``FvdepCore.Evidence.result_dup),
        (``EvidenceClaims.provenIff, ``FvdepCore.Evidence.proven_iff),
        (``EvidenceClaims.phaseRule, ``FvdepCore.Evidence.result_spec),
        (``EvidenceClaims.reasonsShape, ``FvdepCore.Evidence.result_reasons),
        (``EvidenceClaims.infraWins, ``FvdepCore.Evidence.infra_result),
        (``EvidenceClaims.declineApart, ``FvdepCore.Evidence.kernelReason_code),
        (``EvidenceClaims.diffMatched, ``FvdepCore.Evidence.diff_matched),
        (``EvidenceClaims.diffMismatch, ``FvdepCore.Evidence.diff_mismatch),
        (``EvidenceClaims.diffNotProven, ``FvdepCore.Evidence.diff_not_proven),
        (``EvidenceClaims.diffInfra, ``FvdepCore.Evidence.diff_infra),
        (``EvidenceClaims.diffUnsupported, ``FvdepCore.Evidence.diff_unsupported),
        (``EvidenceClaims.proofIgnoresComparisons, ``FvdepCore.Evidence.proof_ignores_compare)]
    subject := ``FvdepCore.Evidence.result
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def statusRow : Row :=
  { component := `FvdepCore.Status
    contract :=
      "U2 P1–P9 + X2–X4; Decisions Proof policy + Lifecycle + Data formats; docs/interface.md §2–§6"
    claim :=
      "Policy acceptance; exit codes per module + command (`check` from its fresh results " ++
        "alone); receipts only for well-shaped requests, the verdict = the evidence kind; " ++
        "staleness + lock changes = exactly the differing fields, in report order; the exact " ++
        "file disagreements; the first status reason with its payload (delivered ⇔ none); " ++
        "retraction = the first matching notice (monotone, never delivered); `status` exit " ++
        "per policy (the files agree first); the lock decision (a refusal exits as `check` " ++
        "does); the commit step: a refusal performs no effect, a commit writes the write set " ++
        "in canonical order + exits 0 or stops at the first failure with its diagnostic + " ++
        "exit 2, and each file ends old or new."
    claims :=
      [(``StatusClaims.meetsRequired, ``FvdepCore.Status.meets_required),
        (``StatusClaims.meetsDevelopment, ``FvdepCore.Status.meets_development),
        (``StatusClaims.exitOk, ``FvdepCore.Status.commandExit_ok),
        (``StatusClaims.exitFailure, ``FvdepCore.Status.commandExit_failure),
        (``StatusClaims.exitCodes, ``FvdepCore.Status.exit_codes),
        (``StatusClaims.moduleFailure, ``FvdepCore.Status.moduleExit_failure),
        (``StatusClaims.moduleOk, ``FvdepCore.Status.moduleExit_ok),
        (``StatusClaims.checkOk, ``FvdepCore.Status.checkExit_ok),
        (``StatusClaims.checkFailure, ``FvdepCore.Status.checkExit_failure),
        (``StatusClaims.proofReceipt, ``FvdepCore.Status.receiptOf_proof),
        (``StatusClaims.differentialReceipt, ``FvdepCore.Status.receiptOf_differential),
        (``StatusClaims.noChanges, ``FvdepCore.Status.changes_nil),
        (``StatusClaims.changesExact, ``FvdepCore.Status.changes_exact),
        (``StatusClaims.agreementExact, ``FvdepCore.Status.agreement_mem),
        (``StatusClaims.retractionFirst, ``FvdepCore.Status.retraction_some),
        (``StatusClaims.retractionNone, ``FvdepCore.Status.retraction_none),
        (``StatusClaims.retractionMonotone, ``FvdepCore.Status.retraction_append),
        (``StatusClaims.retractionListed, ``FvdepCore.Status.retraction_listed),
        (``StatusClaims.deliveredReason, ``FvdepCore.Status.statusReason_none),
        (``StatusClaims.statusReasonOrder, ``FvdepCore.Status.statusReason_some),
        (``StatusClaims.retractedUndelivered, ``FvdepCore.Status.retracted_not_delivered),
        (``StatusClaims.statusRequired, ``FvdepCore.Status.statusExit_required),
        (``StatusClaims.statusDevelopment, ``FvdepCore.Status.statusExit_development),
        (``StatusClaims.lockCommit, ``FvdepCore.Status.lockDecision_commit),
        (``StatusClaims.lockRefuse, ``FvdepCore.Status.lockDecision_refuse),
        (``StatusClaims.lockRefuseExact, ``FvdepCore.Status.lockDecision_refuse_iff),
        (``StatusClaims.lockCurrent, ``FvdepCore.Status.lockState_current),
        (``StatusClaims.lockOutOfDate, ``FvdepCore.Status.lockState_outOfDate),
        (``StatusClaims.lockChangesExact, ``FvdepCore.Status.lockChanges_exact),
        (``StatusClaims.commitAll, ``FvdepCore.Status.commitFiles_ok),
        (``StatusClaims.commitStops, ``FvdepCore.Status.commitFiles_failed),
        (``StatusClaims.commitOrder, ``FvdepCore.Status.commitFiles_prefix),
        (``StatusClaims.refuseNoEffect, ``FvdepCore.Status.authorize_refuse),
        (``StatusClaims.replaceAfterDecision, ``FvdepCore.Status.authorize_replaces),
        (``StatusClaims.commitComplete, ``FvdepCore.Status.authorize_commit),
        (``StatusClaims.commitWrites, ``FvdepCore.Status.authorize_commit_ok),
        (``StatusClaims.oldOrNew, ``FvdepCore.Status.authorize_old_or_new)]
    subject := ``FvdepCore.Status.authorize
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U3 J: the JSON profile codec (port of fvapi's; J3's duplicate-key site added). -/
def jsonValueRow : Row :=
  { component := `FvdepCore.Json.Value
    contract := "U3 J1 + J5; Decisions Data formats"
    claim :=
      "`Value.object` = the members stably sorted by key; `get?` = the first equal key's value " ++
        "(`none` when absent or not an object); each projection = exactly its constructor's " ++
        "payload."
    claims :=
      [(``JsonClaims.objectLaw, ``FvdepAudit.Json.Proof.object_law),
        (``JsonClaims.getLaw, ``FvdepAudit.Json.Proof.get_law),
        (``JsonClaims.asLaws, ``FvdepAudit.Json.Proof.as_laws)]
    subject := ``FvdepCore.Json.Value.get?
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def jsonDecodeRow : Row :=
  { component := `FvdepCore.Json.Decode
    contract := "U3 J1–J3 + J5–J6; Decisions Data formats"
    claim :=
      "`decode` returns exactly the outcome the reviewed byte grammar assigns (too deep, " ++
        "malformed, too large, the duplicate key's site, else the canonical value); every " ++
        "success is a valid value; a text denotes one value."
    claims :=
      [(``JsonClaims.decodeExact, ``FvdepAudit.Json.Proof.decode_exact),
        (``JsonClaims.decodeValid, ``FvdepAudit.Json.Proof.decode_valid),
        (``JsonClaims.textUnique, ``FvdepAudit.Json.Proof.text_unique)]
    subject := ``FvdepCore.Json.decode
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def jsonPrintRow : Row :=
  { component := `FvdepCore.Json.Print
    contract := "U3 J4 + J6; Decisions Data formats"
    claim :=
      "`print` emits exactly the reviewed canonical text; a valid value's text decodes back to " ++
        "it (by the grammar + through the shipped decoder); canonical text tells valid values " ++
        "apart."
    claims :=
      [(``JsonClaims.printExact, ``FvdepAudit.Json.Proof.print_exact),
        (``JsonClaims.roundTrip, ``FvdepAudit.Json.Proof.round_trip),
        (``JsonClaims.printDecode, ``FvdepAudit.Json.Proof.print_decode),
        (``JsonClaims.canonicalInjective, ``FvdepAudit.Json.Proof.canonical_injective)]
    subject := ``FvdepCore.Json.print
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U3 D: the documents fvdep reads + writes (receipts, `fvdep.lock`, the `--json` envelope) + the
text bound. -/
def docReceiptRow : Row :=
  { component := `FvdepCore.Doc
    contract := "U3 D2 + D3 + D5 + D7 + D8; Decisions Data formats"
    claim :=
      "`Receipt.toJson` emits exactly the D3 layout; on a J1-valid value `Receipt.ofJson` " ++
        "accepts exactly the layouts of well-formed receipts (returning that receipt) and " ++
        "refuses with the D5 walk's first violation; a well-formed receipt encodes to a valid " ++
        "value; " ++
        "`Receipt.wellFormed` decides well-formedness."
    claims :=
      [(``DocClaims.receiptEncodeExact, ``FvdepAudit.Doc.Proof.receipt_encode),
        (``DocClaims.receiptSchemaExact, ``FvdepAudit.Doc.Proof.receipt_schema_exact),
        (``DocClaims.receiptDecodeOk, ``FvdepAudit.Doc.Proof.receipt_ok),
        (``DocClaims.receiptDecodeError, ``FvdepAudit.Doc.Proof.receipt_error),
        (``DocClaims.receiptValid, ``FvdepAudit.Doc.Proof.receipt_valid),
        (``DocClaims.receiptCheck, ``FvdepAudit.Doc.Proof.receipt_check)]
    subject := ``FvdepCore.Status.Receipt.ofJson
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def docLockRow : Row :=
  { component := `FvdepCore.Doc
    contract := "U3 D2 + D4 + D5 + D7 + D8; Decisions Data formats"
    claim :=
      "`fvdep.lock`: a lock's JSON is exactly the D4 layout; on a J1-valid value `Lock.ofJson` " ++
        "accepts exactly the layouts of well-formed locks and refuses with the D5 walk's first " ++
        "violation; `decodeLock` returns a well-formed lock's canonical bytes back as that lock " ++
        "and refuses with J3's text error first, else the walk's first violation; " ++
        "`Lock.normalize` keeps the receipts + library, orders module ids (stable), and yields " ++
        "a well-formed lock from distinct well-formed receipts; `Lock.wellFormed` decides " ++
        "well-formedness."
    claims :=
      [(``DocClaims.lockEncodeExact, ``FvdepAudit.Doc.Proof.lock_encode),
        (``DocClaims.lockSchemaExact, ``FvdepAudit.Doc.Proof.lock_schema_exact),
        (``DocClaims.lockDecodeOk, ``FvdepAudit.Doc.Proof.lock_ok),
        (``DocClaims.lockDecodeError, ``FvdepAudit.Doc.Proof.lock_error),
        (``DocClaims.lockValid, ``FvdepAudit.Doc.Proof.lock_valid),
        (``DocClaims.lockCheck, ``FvdepAudit.Doc.Proof.lock_check),
        (``DocClaims.lockBytesEncode, ``FvdepAudit.Doc.Proof.lock_bytes_encode),
        (``DocClaims.lockBytesOk, ``FvdepAudit.Doc.Proof.lock_bytes_ok),
        (``DocClaims.lockBytesError, ``FvdepAudit.Doc.Proof.lock_bytes_error),
        (``DocClaims.normalizePreserves, ``FvdepAudit.Doc.Proof.normalize_preserves),
        (``DocClaims.normalizeSorted, ``FvdepAudit.Doc.Proof.normalize_sorted)]
    subject := ``FvdepCore.Doc.decodeLock
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def docEnvelopeRow : Row :=
  { component := `FvdepCore.Doc
    contract := "U3 D6 + D7 + D8; docs/interface.md §6"
    claim :=
      "The `--json` envelope's JSON is exactly the D6 layout (result members verbatim, " ++
        "diagnostics clipped); a well-formed envelope encodes to a valid value; " ++
        "`Envelope.wellFormed` decides well-formedness."
    claims :=
      [(``DocClaims.envelopeEncodeExact, ``FvdepAudit.Doc.Proof.envelope_encode),
        (``DocClaims.envelopeCheck, ``FvdepAudit.Doc.Proof.envelope_check),
        (``DocClaims.envelopeValid, ``FvdepAudit.Doc.Proof.envelope_valid)]
    subject := ``FvdepCore.Doc.Envelope.toJson
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def docClipRow : Row :=
  { component := `FvdepCore.Doc
    contract := "U3 D1 + D7"
    claim :=
      "`clip` keeps a text within 65,536 UTF-8 bytes, else its longest scalar-boundary prefix " ++
        "within 65,520 bytes + ` [truncated]`; every clipped text fits 65,536 bytes."
    claims :=
      [(``DocClaims.clipExact, ``FvdepAudit.Doc.Proof.clip_exact),
        (``DocClaims.clipBound, ``FvdepAudit.Doc.Proof.clip_bound)]
    subject := ``FvdepCore.Doc.clip
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

def ledger : Ledger :=
  { main := ``main
    interpreter := ``FvdepIO.execute
    plan := ``Cli.plan
    libs := [`FvdepCore, `FvdepIO]
    rows :=
      [cliRow, planRow, interpreterRow, versionRow, idsRow, evidenceRow, statusRow, jsonValueRow,
        jsonDecodeRow, jsonPrintRow, docReceiptRow, docLockRow, docEnvelopeRow, docClipRow]
    residue := residue }

end FvdepLedger.Rows
