import FvdepAudit.Build.Proof.Cache
import FvdepAudit.Build.Proof.Key
import FvdepAudit.Build.Proof.Plan
import FvdepAudit.Doc.Proof.Envelope
import FvdepAudit.Doc.Proof.Lock
import FvdepAudit.Hash.Proof.Sha256
import FvdepAudit.Index.Assemble.Proof.Claims
import FvdepAudit.Index.Command.Proof.Claims
import FvdepAudit.Index.History.Proof.Claims
import FvdepAudit.Index.Proof.Claims
import FvdepAudit.Index.Statuses.Proof.Files
import FvdepAudit.Json.Proof.Access
import FvdepAudit.Manifest.Proof.Denote
import FvdepAudit.Manifest.Proof.Lake
import FvdepAudit.Manifest.Proof.Text
import FvdepAudit.Phase.Proof
import FvdepAudit.Protocol.Proof.Lines
import FvdepAudit.Protocol.Proof.Request
import FvdepAudit.Protocol.Proof.Sig
import FvdepAudit.Sandbox.Proof
import FvdepAudit.Step.Proof
import FvdepAudit.Sys.Proof.Claims
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
  ∀ (args : List String),
    ¬Cli.IndexArgs args →
      ∀ (evs : List (Eff × Response)) (code : UInt32),
        Plan.Runs (Cli.plan args) evs (some code) ↔
          evs = Cli.outputs (Cli.run args) ∧ code = (Cli.run args).exit

/-- U2 X5: an interrupted run performs a prefix of the outcome's outputs. -/
def cliPlanInterrupted : Prop :=
  ∀ (args : List String),
    ¬Cli.IndexArgs args →
      ∀ (evs : List (Eff × Response)),
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

/-- D5 + D8: each receipt field's general type (what `wrong_type` is judged against) in the shared
schema data = interface §6 + D3's, written apart. -/
def receiptKindsExact : Prop := kindTable "" [] receiptTy = receiptKinds

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

/-- D5 + D8: each lock field's general type in the shared schema data = interface §6 + D4's,
written apart. -/
def lockKindsExact : Prop := kindTable "" [] lockTy = lockKinds

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
nondecreasingly, keeps equal ids in input order (each id's receipts = the same sequence). -/
def normalizePreserves : Prop :=
  ∀ (l : Lock),
    l.normalize.library = l.library ∧
      l.normalize.entries.Perm l.entries ∧
      (l.normalize.entries.map idOf).Pairwise (· ≤ ·) ∧
      ∀ k,
        l.normalize.entries.filter (fun r => idOf r == k) = l.entries.filter (fun r => idOf r == k)

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

namespace FvdepLedger.Rows.HashClaims

open FvdepCore.Hash FvdepAudit.Hash.Spec

/-- H4: `hex` = each byte's two lowercase hex digits, high nibble first. -/
def hexExact : Prop := ∀ (b : ByteArray), hex b = hexSpec b

/-- H4: `frame`'s bytes = H2's layout. -/
def frameLayout : Prop :=
  ∀ (t : String) (fs : List (String × ByteArray)), (frame t fs).data.toList = frameSpec t fs

/-- H4: inside H2's domain, `unframe` returns the tag + the files in path order. -/
def frameDecode : Prop :=
  ∀ (t : String) (fs : List (String × ByteArray)) (_h : FrameDomain t fs),
    unframe (frame t fs) = some (t, byPath fs)

/-- H4: inside H2's domain, equal frames have equal tags + the same files (in any order). -/
def frameInjective : Prop :=
  ∀ (t : String) (fs : List (String × ByteArray)) (t' : String) (fs' : List (String × ByteArray))
    (_h : FrameDomain t fs) (_h' : FrameDomain t' fs') (_he : frame t fs = frame t' fs'),
    t = t' ∧ fs.Perm fs'

/-- H4: `unframe` accepts exactly frames: a decoded tag + files lie in H2's domain, their paths
strictly ascend, and they frame back to the input bytes. -/
def unframeExact : Prop :=
  ∀ (b : ByteArray) (t : String) (fs : List (String × ByteArray)) (_h : unframe b = some (t, fs)),
    FrameDomain t fs ∧ (fs.map (·.1)).Pairwise (· < ·) ∧ frame t fs = b

/-- S3: a stream's byte count saturates at 2^64 − 1 on its way to the C limit check (never wraps).
-/
def saturateLaw : Prop :=
  ∀ (n : Nat), (FvdepIO.Hash.Sha256.saturate n).toNat = min n (UInt64.size - 1)

end FvdepLedger.Rows.HashClaims

namespace FvdepLedger.Rows.ManifestClaims

open FvdepCore.Manifest FvdepAudit.Manifest.Spec

/-- T5 `Utf8Offset`: `none` exactly on valid UTF-8, else the length of the longest valid prefix. -/
def utf8Offset : Prop :=
  ∀ (b : ByteArray),
    (utf8ErrorOffset b = none ↔ ValidUtf8 b) ∧
      ∀ k,
        utf8ErrorOffset b = some k ↔
          ¬ValidUtf8 b ∧
            ValidUtf8 (b.extract 0 k) ∧ ∀ j, k < j → j ≤ b.size → ¬ValidUtf8 (b.extract 0 j)

/-- T5 `TextStage`: size first, then a BOM, then the first UTF-8 offset, else the text whose bytes
are the input. -/
def textStageExact : Prop := ∀ (b : ByteArray), TextSpec b (textStage b)

end FvdepLedger.Rows.ManifestClaims

namespace FvdepLedger.Rows.ManifestClaims

open Lean FvdepCore.Manifest FvdepIO.Toml FvdepAudit.Manifest.Spec

/-- T5 `OfLakeExact`: `ofLake` rebuilds Lake's table exactly when every key is one string component
(else it names a key of another shape), + always answers one of the two. -/
def ofLakeExact : Prop :=
  ∀ (d : Lake.Toml.Table),
    (∀ t, ofLake d = .ok t ↔ ∃ ms, t = .tbl ms ∧ LakeMembers d.items.toList ms) ∧
      (∀ n, ofLake d = .error n → BadKey d n) ∧ ((∀ n, ¬BadKey d n) → ∃ t, ofLake d = .ok t)

end FvdepLedger.Rows.ManifestClaims

namespace FvdepLedger.Rows.ManifestClaims

open FvdepCore.Manifest FvdepAudit.Manifest.Spec

/-- T5 `ValidateExact`: `validate` accepts exactly the trees that spell a well-formed manifest,
returning it. -/
def validateOk : Prop := ∀ (t : Tree) (m : ManifestFile), validate t = .ok m ↔ ManifestSpec t m

/-- T5 `ValidateExact`: `validate` refuses with exactly the first of T3 + D5's ordered
violations. -/
def validateError : Prop :=
  ∀ (t : Tree) (e : ManifestError),
    validate t = .error e ↔ FvdepAudit.Manifest.Spec.firstViolation t = some e

/-- T5 `ValidateWellFormed`: every manifest `validate` returns is well formed. -/
def validateWellFormed : Prop :=
  ∀ (t : Tree) (m : ManifestFile) (_h : validate t = .ok m), WellFormed m

/-- T5 `TreeRoundTrip`: the tree a well-formed manifest prints to validates back to it. -/
def treeRoundTrip : Prop := ∀ (m : ManifestFile) (_hw : WellFormed m), validate (toTree m) = .ok m

/-- T5 `PrintExact`: the printer's bytes = T4's canonical layout. -/
def printExact : Prop :=
  ∀ (m : ManifestFile) (_hw : WellFormed m), (printManifest m).data.toList = canonicalManifest m

/-- T5 `PrintDenotes`: the printer's bytes are a document of T4's TOML 1.0 subset denoting
`toTree m`. -/
def printDenotes : Prop :=
  ∀ (m : ManifestFile) (_hw : WellFormed m), TomlText (printManifest m).data.toList (toTree m)

end FvdepLedger.Rows.ManifestClaims

namespace FvdepLedger.Rows.SysClaims

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy FvdepAudit.Sys.Spec

/-- F4 `NoFalseSuccess` + `ErrorExact` + `RetryBounded` (create): the result is exactly the one the
protocol relation `Create` assigns to the calls (ok + error alike). -/
def createExact : Prop :=
  ∀ (path : Path) (mode : Mode) (script : Script) (r : Except SysError Nat),
    ((create scripted path mode).run script).result = r ↔
      Create path mode ((create scripted path mode).run script).events r

/-- F4 `NoFalseSuccess` + `ErrorExact` + `RetryBounded` (writer calls): the result is exactly the
one `WriterOperation` assigns to the calls. -/
def writerExact : Prop :=
  ∀ (owned : WriterState) (action : WriterAction) (script : Script)
    (_hc : Consistent ((writer scripted owned action).run script).events) (r : Except SysError Nat),
    ((writer scripted owned action).run script).result = r ↔
      WriterOperation owned action ((writer scripted owned action).run script).events r

/-- F4 `NoFalseSuccess` + `ErrorExact` + `RetryBounded` (`syncDir`): the result is exactly the one
`Directory` assigns to the calls. -/
def directoryExact : Prop :=
  ∀ (path : Path) (script : Script) (r : Except SysError Nat),
    ((directory scripted path).run script).result = r ↔
      Directory path ((directory scripted path).run script).events r

/-- F4 `NoFalseSuccess`: a successful write's calls acknowledge exactly its bytes. -/
def writeAcknowledged : Prop :=
  ∀ (owned : WriterState) (size : Nat) (script : Script) (n : Nat)
    (_hc : Consistent ((writer scripted owned (.write size)).run script).events)
    (_ok : ((writer scripted owned (.write size)).run script).result = .ok n),
    acknowledged ((writer scripted owned (.write size)).run script).events = size

/-- F4 `RetryBounded`: one F3 step = at most `budget + 1` calls of one request; with 64 retries the
65th EINTR ends it as `retryExhausted`. -/
def retryBounded : Prop :=
  (∀ (request : Request) (budget : Nat) (events : Trace) (result : Except Cause Nat),
      Retry request budget events result → events.length ≤ budget + 1) ∧
    (∀ request : Request,
      Retry request 64 (List.replicate 65 ⟨request, .error 4⟩) (.error .retryExhausted)) ∧
    ∀ (request : Request) (budget : Nat) (events : Trace) (result : Except Cause Nat),
      Retry request budget events result → ∀ e ∈ events, e.request = request

/-- F4 `CloseOnce`: a writer's calls (the finalizer included) attempt close at most once, never on a
closed writer. -/
def closeOnceActions : Prop :=
  ∀ (owned : WriterState) (steps : List WriterAction) (script : Script)
    (_hc : Consistent ((actions scripted owned steps).run script).events),
    closeCount ((actions scripted owned steps).run script).events ≤ if owned.closed then 0 else 1

/-- F4 `CloseOnce`: `syncDir` attempts close at most once, exactly once after its open succeeded. -/
def closeOnceDirectory : Prop :=
  ∀ (path : Path) (script : Script),
    closeCount ((directory scripted path).run script).events ≤ 1 ∧
      ((∃ e ∈ ((directory scripted path).run script).events,
          ∃ fd, e.request = .openDir path ∧ e.response = .ok fd) →
        closeCount ((directory scripted path).run script).events = 1)

/-- F4 `SameDescription`: a writer call uses only the writer's descriptor (write chunks ≤ 2^30
bytes); a closed writer issues no call. -/
def sameDescription : Prop :=
  ∀ (owned : WriterState) (action : WriterAction) (script : Script)
    (_hc : Consistent ((writer scripted owned action).run script).events),
    writerOnly owned.fd ((writer scripted owned action).run script).events ∧
      (owned.closed = true → ((writer scripted owned action).run script).events = [])

/-- F4 `ReplaceExact`: `replace`'s calls + result follow F2's protocol written apart (`Replace`:
temp walk, all bytes, fsync, one close, one rename step, `syncDir`, cleanup order + causes,
`durability`), which fixes the result from the calls. -/
def replaceExact : Prop :=
  ∀ (dir : Path) (name : Name) (pid size : Nat) (script : Script) (r : Except SysError Unit)
    (_hc : Consistent ((replace scripted dir name pid size).run script).events),
    ((replace scripted dir name pid size).run script).result = r ↔
      Replace dir name pid size ((replace scripted dir name pid size).run script).events r

/-- F4 `ReplaceOldOrNew` over the directory model: after a complete run the target holds its old
state or the new bytes (new on success + on a `durability` failure, old when no rename was
attempted); the same at every interruption (the call in flight taking effect or not), absent +
present targets alike. -/
def replaceOldOrNew : Prop :=
  ∀ (dir : Path) (name : Name) (pid : Nat) (payload : List UInt8) (script : Script) (s₀ : DirState)
    (run : Recorded (Except SysError Unit))
    (_hrun : run = (replace scripted dir name pid payload.length).run script)
    (_hc : Consistent run.events),
    (∀ s,
        Steps payload s₀ run.events s →
          OldOrNew payload s₀ s (targetText dir name) ∧
            (run.result = .ok () → s.files (targetText dir name) = some payload) ∧
            (∀ e,
              run.result = .error e →
                e.durability = true → s.files (targetText dir name) = some payload) ∧
            (NoRename run.events →
              s.files (targetText dir name) = s₀.files (targetText dir name))) ∧
      ∀ done x rest s₁ s,
        run.events = done ++ x :: rest →
          Steps payload s₀ done s₁ →
          InFlight payload s₁ x.request s →
          OldOrNew payload s₀ s (targetText dir name) ∧
            (NoRename (done ++ [x]) →
              s.files (targetText dir name) = s₀.files (targetText dir name))

/-- F4: `ReplaceOldOrNew`'s bridge to U2 X4's `Holds` for a present target: a complete success =
`Holds`' `ok` step, a failure or an interruption (any message) = `keep` or `land`. -/
def replaceHolds : Prop :=
  ∀ (dir : Path) (name : Name) (pid : Nat) (payload old : List UInt8) (script : Script)
    (s₀ : DirState) (f : FvdepCore.ProjectFile) (run : Recorded (Except SysError Unit))
    (_hrun : run = (replace scripted dir name pid payload.length).run script)
    (_hc : Consistent run.events) (_hold : s₀.files (targetText dir name) = some old),
    (∀ s,
        Steps payload s₀ run.events s →
          ∃ c,
            s.files (targetText dir name) = some c ∧
              (run.result = .ok () →
                FvdepCore.Status.Holds f (bytesOf old)
                  [(.replace f (bytesOf payload), .replace (.ok ()))] (bytesOf c)) ∧
              ∀ e msg,
                run.result = .error e →
                  FvdepCore.Status.Holds f (bytesOf old)
                    [(.replace f (bytesOf payload), .replace (.error msg))] (bytesOf c)) ∧
      ∀ done x rest s₁ s msg,
        run.events = done ++ x :: rest →
          Steps payload s₀ done s₁ →
          InFlight payload s₁ x.request s →
          ∃ c,
            s.files (targetText dir name) = some c ∧
              FvdepCore.Status.Holds f (bytesOf old)
                [(.replace f (bytesOf payload), .replace (.error msg))] (bytesOf c)

/-- F4's model step, policy half: a scripted `replace` reads its answers in order (`Causal`: its
record lists the script's answers in order, the answers it consumed fix its run, and its call k +
whether it is issued depend on answers 0…k−1 alone). -/
def replaceCausal : Prop :=
  ∀ (dir : Path) (name : Name) (pid size : Nat), Causal (replace scripted dir name pid size)

/-- F2 `readFile`: the calls + result follow the protocol written apart (`ReadFile`: ENOENT =
absent, reads of ≤ 2^20 bytes until 0, the caller's byte cap, one close, the close's failure as
primary or secondary cause), which fixes the result from the calls. -/
def readExact : Prop :=
  ∀ (path : Path) (cap : Nat) (script : Script) (r : Except SysError (Option Nat))
    (_hc : Consistent ((readFile scripted path cap).run script).events),
    ((readFile scripted path cap).run script).result = r ↔
      ReadFile path cap ((readFile scripted path cap).run script).events r

/-- F4 `LockExact`: `act` runs exactly when the lock file's open + `flock` succeed, once, on the
answers that follow; its result is returned; the description is closed on every exit after its open;
a refusal (EWOULDBLOCK = `busy`) or an open failure runs nothing. -/
def lockExact : Prop :=
  ∀ {α : Type} (dir : Path) (act : ScriptIO α) (script : Script) (r : Except SysError α),
    ((withLock scripted dir act).run script).result = r ↔
      Lock dir act script ((withLock scripted dir act).run script).events r

/-- F4 `ReplaceSingleTouch`: one rename step is the only call naming the target (none when the run
stops before it); every write, the data fsync + the temp's close use the descriptor the temp's
create returned; nothing after the rename writes. -/
def replaceSingleTouch : Prop :=
  ∀ (dir : Path) (name : Name) (pid size : Nat) (script : Script)
    (_hc : Consistent ((replace scripted dir name pid size).run script).events),
    (∀ e ∈ ((replace scripted dir name pid size).run script).events,
        ¬Names (targetText dir name) e.request) ∨
      ∃ (walk data renames rest : Trace) (temp target : Path) (mode : Mode) (fd : Nat) (renamed :
        Except Cause Nat),
        ((replace scripted dir name pid size).run script).events =
            walk ++ ⟨.create temp mode, .ok fd⟩ :: data ++ renames ++ rest ∧
          target.toString = targetText dir name ∧
          Retry (.rename temp target) 64 renames renamed ∧
          writerOnly fd data ∧
          (∀ e ∈ rest, ∀ g o c, e.request ≠ .write g o c) ∧
          ∀ e ∈ walk ++ ⟨.create temp mode, .ok fd⟩ :: data ++ rest,
            ¬Names (targetText dir name) e.request

/-- F2: attempt `n`'s temp = `<dir>/.<name>.tmp-<pid>-<n>` (the text the protocol claims name). -/
def tempPathText : Prop :=
  ∀ (dir : Path) (name : Name) (pid n : Nat),
    (tempPath dir name pid n).toString = tempText dir name pid n

/-- F2: the target = `<dir>/<name>`. -/
def atText : Prop := ∀ (dir : Path) (name : Name), (dir.at name).toString = targetText dir name

/-- F2: the writer lock = `<dir>/.fvdep-writer.lock`. -/
def lockPathText : Prop := ∀ (dir : Path), (lockPath dir).toString = lockText dir

end FvdepLedger.Rows.SysClaims

namespace FvdepLedger.Rows.ProtocolClaims

open FvdepCore.Json FvdepCore.Protocol FvdepAudit.Protocol.Spec

/-- U4 B2: each value encodes to its §8 wire layout, written apart. -/
def valLayout : Prop := ∀ (x : Val), encodeVal x = valSpec x

/-- U4 B2: decoding at a type returns exactly the value of that type whose layout it is; every
other value is refused. -/
def valExact : Prop :=
  ∀ (t : Ty) (v : Value) (x : Val), decodeVal t v = some x ↔ x.ty = t ∧ valSpec x = v

/-- U4 B4: a value whose wire strings fit J1's bound encodes to a J1-valid value (integers, depth
+ key order hold by construction). -/
def valValid : Prop :=
  ∀ x : Val,
    FvdepAudit.Json.Spec.stringsFit (valSpec x) = true → FvdepAudit.Json.Spec.Valid (encodeVal x)

/-- U4 B3: a request line decodes to arguments exactly when J decodes it to the request object
of the target's op whose arguments are their layouts, in order, typed by the signature. -/
def requestExact : Prop :=
  ∀ (sig : Sig) (b : ByteArray) (xs : List Val),
    decodeRequest sig b = .ok xs ↔
      decode b = .ok (requestLayout sig.op (xs.map valSpec)) ∧ xs.map Val.ty = sig.args

/-- U4 B3: a reply line = the canonical text of its reply object (written apart) + LF. -/
def replyExact : Prop :=
  ∀ r : Reply, encodeReply r = (FvdepCore.Json.print (replyLayout r)).push 0x0A

end FvdepLedger.Rows.ProtocolClaims

namespace FvdepLedger.Rows.ProtocolClaims

open FvdepCore.Protocol FvdepAudit.Protocol.Spec

/-- U4 B3: the request lines = the LF-separated segments, a final empty segment dropped (EOF adds
no line). -/
def linesExact : Prop := ∀ (b : ByteArray), (lines b).map (·.data.toList) = linesSpec b.data.toList

/-- U4 B1: `sigOf` = the type table over `Expr` shapes, written apart. -/
def sigExact : Prop :=
  ∀ (e : Lean.Expr) (ts : List Ty) (r : RTy), sigOf e = some (ts, r) ↔ SigIs e ts r

end FvdepLedger.Rows.ProtocolClaims

namespace FvdepLedger.Rows.IndexClaims

open FvdepCore.Json FvdepCore.Ids FvdepCore.Doc FvdepCore.Index FvdepAudit.Doc.Spec
  FvdepAudit.Index.Spec

/-- U4 C6: an index's JSON is exactly its layout, written apart. -/
def indexEncodeExact : Prop := ∀ (i : IndexFile), i.toJson = indexLayout i

/-- U4 C6 + C8: on a J1-valid value the D5 walk finds no violation exactly when the value is the
layout of an index whose every node is well formed. -/
def indexSchemaExact : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v),
    firstViolation indexTy v = none ↔ ∃ i, IndexNodeWF i ∧ v = indexLayout i

/-- U4 C6: on a J1-valid value, `IndexFile.ofJson` accepts exactly the layouts of well-formed
indexes (nodes + relational clauses), returning that index. -/
def indexDecodeOk : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v) (i : IndexFile),
    IndexFile.ofJson v = .ok i ↔ IndexWF i ∧ v = indexLayout i

/-- U4 C6: `IndexFile.ofJson` refuses with the walk's first violation, else the first relational
violation (notices, then removed records, in order). -/
def indexDecodeError : Prop :=
  ∀ (v : Value) (_hv : FvdepAudit.Json.Spec.Valid v) (e : DocError),
    IndexFile.ofJson v = .error e ↔
      firstViolation indexTy v = some e ∨
        ∃ i,
          IndexNodeWF i ∧
            firstViolation indexTy v = none ∧
            v = indexLayout i ∧ (relationViolations i).head? = some e

/-- U4 C6: a well-formed index's JSON is a J1-valid value. -/
def indexValid : Prop := ∀ (i : IndexFile) (_h : IndexWF i), FvdepAudit.Json.Spec.Valid i.toJson

/-- U4 C6: `IndexFile.wellFormed` decides `IndexWellFormed`. -/
def indexCheck : Prop := ∀ (i : IndexFile), i.wellFormed = true ↔ IndexWF i

/-- U4 C6 + C8: each index field's general type in the schema data = C6's, written apart. -/
def indexKindsExact : Prop := kindTable "" [] indexTy = indexKinds

/-- U4 C6: `encodeIndex` refuses an index outside schema 1, else returns its canonical text + LF. -/
def indexEncodeBytes : Prop :=
  ∀ (i : IndexFile) (b : ByteArray),
    encodeIndex i = .ok b ↔ IndexWF i ∧ b = (print (indexLayout i)).push 0x0A

/-- U4 C6 + C9: `encodeIndex` refuses with the first violation of the index's layout: the walk's,
else the first relational one. -/
def indexEncodeError : Prop :=
  ∀ (i : IndexFile) (e : DocError),
    encodeIndex i = .error e ↔
      firstViolation indexTy (indexLayout i) = some e ∨
        firstViolation indexTy (indexLayout i) = none ∧ (relationViolations i).head? = some e

/-- U4 C8 `IndexBytes`: a well-formed index's bytes decode back to it. -/
def indexBytesEncode : Prop :=
  ∀ (i : IndexFile) (_h : IndexWF i), decodeIndex ((print (indexLayout i)).push 0x0A) = .ok i

/-- U4 C8 `IndexBytes`: `decodeIndex` accepts exactly the bytes whose text (one final LF removed) J
decodes to the layout of a well-formed index, returning that index. -/
def indexBytesOk : Prop :=
  ∀ (b : ByteArray) (i : IndexFile),
    decodeIndex b = .ok i ↔ decode (withoutFinalLF b) = .ok (indexLayout i) ∧ IndexWF i

/-- U4 C8 `IndexBytes`: a document refusal of `decodeIndex` = the first violation of the value J
decodes from the bytes (one final LF removed): the walk's, else the first relational one. -/
def indexBytesDoc : Prop :=
  ∀ (b : ByteArray) (e : DocError),
    decodeIndex b = .error (.doc e) ↔
      ∃ v,
        decode (withoutFinalLF b) = .ok v ∧
          (firstViolation indexTy v = some e ∨
            ∃ i,
              IndexNodeWF i ∧
                firstViolation indexTy v = none ∧
                v = indexLayout i ∧ (relationViolations i).head? = some e)

/-- U4 C8 `IndexBytes`: a text refusal of `decodeIndex` = J's refusal of the bytes (one final LF
removed). -/
def indexBytesText : Prop :=
  ∀ (b : ByteArray) (j : DecodeError),
    decodeIndex b = .error (.text j) ↔ decode (withoutFinalLF b) = .error j

end FvdepLedger.Rows.IndexClaims

namespace FvdepLedger.Rows.RegistryClaims

open Lean FvdepCore.Index.Registry FvdepAudit.Registry.Spec

/-- U4 C2 + C8 `RegistryDecodeExact`: the walk reads `e` as `f` (under `let` values `env`, unfolding
`p`) to `v` exactly when the accepted-forms relation, written apart, relates them. -/
def registryDecodeExact : Prop :=
  ∀ (F : Facts) (f : Form) (e : Expr) (env : List Expr) (p : List Name) (v : Val),
    decode F f e env p = .ok v ↔ Denotes F f e env p v

/-- U4 C2: the registry lists as read (`readRaw`), mapped to their records (`Lists.ofRaw`), are `r`
exactly when the four registry list constants denote `r`'s records (their layouts, written apart;
`profiles` = its length). -/
def registryReadExact : Prop :=
  ∀ (F : Facts) (r : Lists), (readRaw F).map Lists.ofRaw = .ok r ↔ RegistryDenotes F r

/-- U4 C2 + C5: `readProofs` returns `pr` exactly when the proof registry constant denotes `pr`'s
layout. -/
def registryProofsExact : Prop :=
  ∀ (F : Facts) (c : Name) (pr : Proofs), readProofs F c = .ok pr ↔ ProofsAt F c pr

/-- U4 C2: the shipped record forms = `Fvdep.Registry.Types.V1`'s field order, written apart. -/
def registryFormsExact : Prop :=
  moduleForm = moduleFormSpec ∧
    noticeForm = noticeFormSpec ∧ removedForm = removedFormSpec ∧ proofsForm = proofsFormSpec

/-- U4 C2 + C8 `ReencodeExact`: a list literal decodes back to the values written, over plain forms
(no `entry`/`any` position: `Plain`) + values of their shape (`Fits`). -/
def registryReencodeExact : Prop :=
  ∀ (F : Facts) (f : Form) (vs : List Val) (env : List Expr) (p : List Name) (_hp : Plain f)
    (_hv : ∀ v ∈ vs, Fits f v), decode F (.list f) (listLiteral f vs) env p = .ok (listVal vs)

/-- U4 C2 + C8 `ReencodeExact` (the certificate): every list `certificate` writes back — `modules`'
records (entry annotations dropped), `profiles` while empty, `notices`, `removed` — decodes from its
literal to exactly the values written. -/
def registryCertificateExact : Prop :=
  ∀ (F : Facts) (r : RawLists) (env : List Expr) (p : List Name) (_h : readRaw F = .ok r) (c : Name)
    (f : Form) (vs : List Val) (_hc : (c, f, vs) ∈ certificate r),
    decode F (.list f) (listLiteral f vs) env p = .ok (listVal vs)

end FvdepLedger.Rows.RegistryClaims

namespace FvdepLedger.Rows.RulesClaims

open Lean FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepAudit.Index.Rules.Spec

/-- U4 C3 + C8 `ValidateExact` (acceptance): `validate` accepts exactly the registries for which
every row of C9's order holds — C3's rules, C4's file check + the load observations, written apart
(`specChecks`). -/
def validateAccepts : Prop := ∀ (F : Facts) (l : Lists), validate F l = none ↔ RegistryValid F l

/-- U4 C9 + C8 `ValidateExact` (order): a refusal is what the first failing row of C9's order may
report (a reason with several offenders: V3, V7 + C4 its least by printed name, V4 its first in
entry order). -/
def validateFirst : Prop :=
  ∀ (F : Facts) (l : Lists) (f : Found) (_h : validate F l = some f), FirstFail (specChecks F l) f

/-- U4 C4 + C8 `ClosureExact`: `closure F M` holds exactly the modules reachable from `M` through
the import edges of `M` + the `Fvdep` modules it reaches (`M` included), each once. -/
def closureExact : Prop :=
  ∀ (F : Facts) (M m : Name), (m ∈ closure F M ↔ ImportReach F M m) ∧ (closure F M).Nodup

/-- U4 C3 V3: `reach` holds exactly the checked constants — the library constants reached from the
roots through library definition values. -/
def reachExact : Prop :=
  ∀ (F : Facts) (roots : List Name) (c : Name),
    c ∈ reach F roots ↔ ConstReach F roots c ∧ libDecl? F c ≠ none

end FvdepLedger.Rows.RulesClaims

namespace FvdepLedger.Rows.StatusesClaims

open Lean FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepAudit.Index.Rules.Spec FvdepAudit.Index.Statuses.Spec

/-- U4 C5 + C9 + C8 `StatusExact`: after `validate` accepted the lists, `statuses` returns exactly
the entries' statuses written apart (`StatusesSpec`: per entry in `modules` order, each obligation's
status + axioms, the compat edge, C9's warnings in order); with no such statuses (a counted theorem
without an observed axiom list) it refuses. -/
def statusesExact : Prop :=
  ∀ (F : Facts) (ax : List (Name × List Name)) (l : Lists) (_h : validate F l = none)
    (rs : List (Entry × EntryStatus)), statuses F ax l = .ok rs ↔ StatusesSpec F ax l rs

/-- U4 C4: `closureFiles F M` holds exactly the closure modules' (canonical path, observed
bytes). -/
def closureFilesExact : Prop :=
  ∀ (F : Facts) (M : Name) (p : String) (b : ByteArray),
    (p, b) ∈ closureFiles F M ↔
      ∃ m, ImportReach F M m ∧ modulePath m = p ∧ ∃ x, modFacts? F m = some x ∧ x.file = some b

/-- U4 C4: `closureFiles`' paths are distinct when every closure module is plain (the frame's path
premise, `FrameDomain`). -/
def closureFilesDistinct : Prop :=
  ∀ (F : Facts) (M : Name) (_h : ∀ m, ImportReach F M m → PlainModule m),
    ((closureFiles F M).map fun x => x.1).Nodup

end FvdepLedger.Rows.StatusesClaims

namespace FvdepLedger.Rows.AssembleClaims

open Lean FvdepCore.Json FvdepCore.Index.Registry FvdepCore.Index.Rules FvdepCore.Index.Statuses
open FvdepCore.Index.Assemble FvdepAudit.Index.Assemble.Spec

/-- U4 C4 + C6 + C9 + C8 `AssembleExact`: after `validate` accepted the lists, `assemble` returns
exactly the index value + warnings written apart (`AssembleSpec`: the entries' statuses, the
operations = those entries strictly ascending in C6's (id, version) order with their digests `h` of
the H3 `fvdep/entry/1` frame, notices + removed records in registry order, the trimmed toolchain,
C9's warnings in `modules` order); with no such statuses it refuses. -/
def assembleExact : Prop :=
  ∀ (F : Facts) (ax : List (Name × List Name)) (l : Lists) (raw : String) (h : ByteArray → String)
    (_h : validate F l = none) (v : Value) (ws : List Warning),
    assemble F ax l raw h = .ok (v, ws) ↔ AssembleSpec F ax l raw h v ws

end FvdepLedger.Rows.AssembleClaims

namespace FvdepLedger.Rows.HistoryClaims

open FvdepCore.Index FvdepCore.Index.History FvdepAudit.Index.History.Spec

/-- U4 C7 + C9 + C8 `HistoryExact`: `history` returns exactly the violations written apart, in C9's
order — the parents' divergence, then HEAD's lines, then each parent's (per baseline: its operations
in index order, ≤ 1 line each by C9's check order with C7's first-removal witness rule, then its
removed records' + notices' extension; an undecodable index = its one line). -/
def historyExact : Prop :=
  ∀ (work : Except String (Option IndexFile)) (head : Baseline) (parents : List Baseline),
    history work head parents = HistorySpec work head parents

end FvdepLedger.Rows.HistoryClaims

namespace FvdepLedger.Rows.SandboxClaims

open FvdepCore.Sandbox FvdepAudit.Sandbox.Spec

/-- R1: bwrap (as `bwrapRead` models its argument reading) reads `bwrapArgs s` as exactly `ops s`,
then the helper + the step's argv verbatim. -/
def argsRead : Prop := ∀ (s : Spec), bwrapRead (bwrapArgs s) = some (ops s, helper :: s.argv)

/-- R1 (f): the storage the sandbox keeps writable = the two sized tmpfs, at `/fvdep/work` + `/tmp`.
-/
def writableExact : Prop :=
  ∀ (s : Spec),
    (ops s).filter writableStorage =
      [.sizedTmpfs s.workBytes "/fvdep/work", .sizedTmpfs s.tmpBytes "/tmp"]

/-- R1 (c): the environment operations = clear, then exactly the spec's variables in order. -/
def envExact : Prop :=
  ∀ (s : Spec), (ops s).filter isEnv = .clearenv :: s.env.map fun e => .setenv e.1 e.2

/-- R1 (f): the operations end with `/` + `/dev` remounted read-only, the cwd + the status
descriptor; no remount before them. -/
def remountLast : Prop :=
  ∀ (s : Spec),
    ∃ pre,
      ops s = pre ++ [.remountRo "/", .remountRo "/dev", .chdir "/fvdep/src", .jsonStatusFd 3] ∧
        ∀ o ∈ pre, ∀ d, o ≠ .remountRo d

/-- R1 (e): every destination an operation names lies in the layout. -/
def destInLayout : Prop := ∀ (s : Spec), ∀ o ∈ ops s, ∀ d, dest? o = some d → d ∈ layout

/-- R6: the outcome precedence: one exit-code line → exited; two or more → protocol; none → timedOut
when killed, else setupFailed with bwrap's first stderr line. -/
def outcomeExact : Prop :=
  ∀ (lines : List StatusLine) (killed : Bool) (e : String),
    (∀ n, classify lines killed e = .exited n ↔ lines.filterMap exitCodeOf = [n]) ∧
      (classify lines killed e = .protocol ↔ 2 ≤ (lines.filterMap exitCodeOf).length) ∧
      (classify lines killed e = .timedOut ↔ lines.filterMap exitCodeOf = [] ∧ killed = true) ∧
      ∀ d,
        classify lines killed e = .setupFailed d ↔
          lines.filterMap exitCodeOf = [] ∧ killed = false ∧ d = e

end FvdepLedger.Rows.SandboxClaims

namespace FvdepLedger.Rows.BuildClaims

open FvdepCore.Build FvdepAudit.Build.Spec

/-- K2: a planned order is a valid build order of the closure (each reached module once, a node,
after all its imports). -/
def planValid : Prop :=
  ∀ (nodes : List Node) (roots order : List String) (_h : plan nodes roots = .ok order),
    ValidOrder nodes roots order

/-- K2: a duplicate refusal names a module two nodes share. -/
def planDuplicate : Prop :=
  ∀ (nodes : List Node) (roots : List String) (n : String)
    (_h : plan nodes roots = .error (.duplicate n)), 2 ≤ (nodes.map (·.name)).count n

/-- K2: a missing refusal names a reached module no node provides + a reached module importing it
(none: a root). -/
def planMissing : Prop :=
  ∀ (nodes : List Node) (roots : List String) (a : Option String) (t : String)
    (_h : plan nodes roots = .error (.missing a t)),
    Reach nodes roots t ∧
      t ∉ nodes.map (·.name) ∧
      (∀ x, a = some x → Reach nodes roots x ∧ Imports nodes x t) ∧ (a = none → t ∈ roots)

/-- K2: a stuck refusal names reached modules, nonempty, each importing another of them. -/
def planStuck : Prop :=
  ∀ (nodes : List Node) (roots ms : List String) (_h : plan nodes roots = .error (.stuck ms)),
    ms ≠ [] ∧ ∀ m ∈ ms, Reach nodes roots m ∧ ∃ i, Imports nodes m i ∧ i ∈ ms

/-- K2: a missing or stuck refusal ⇒ no valid build order exists. -/
def planRefuses : Prop :=
  ∀ (nodes : List Node) (roots : List String) (r : Refusal) (_h : plan nodes roots = .error r)
    (_hr : ∀ n, r ≠ .duplicate n), ¬∃ order, ValidOrder nodes roots order

end FvdepLedger.Rows.BuildClaims

namespace FvdepLedger.Rows.BuildClaims

open FvdepCore.Build FvdepAudit.Build.Spec

/-- K1: within the JSON profile's bounds, distinct key inputs have distinct preimages (keys collide
only through SHA-256). -/
def preimageInjective : Prop :=
  ∀ (a b : KeyInput) (_ha : Bounded a) (_hb : Bounded b) (_h : preimage a = preimage b), a = b

end FvdepLedger.Rows.BuildClaims

namespace FvdepLedger.Rows.BuildClaims

open FvdepCore.Build FvdepAudit.Build.Spec

/-- K5: eviction takes, from the unpinned entries in (used, key) order, the shortest prefix bringing
the charged total to the target or under it — all when none does. -/
def evictExact : Prop :=
  ∀ (entries : List Entry) (target : Nat),
    ∃ cands : List Entry,
      cands.Perm (entries.filter (!·.pinned)) ∧
        cands.Pairwise LruBefore ∧
        ∃ n,
          evictPlan entries target = (cands.take n).map (·.key) ∧
            (n = cands.length ∨ charged entries - charged (cands.take n) ≤ target) ∧
            ∀ j < n, target < charged entries - charged (cands.take j)

/-- K6: `validate` accepts exactly the valid entries. -/
def validateExact : Prop :=
  ∀ (h : ByteArray → String) (dir : String) (m : Manifest) (files : List FileRec),
    validate h dir m files = true ↔ EntryValid h dir m files

end FvdepLedger.Rows.BuildClaims

namespace FvdepLedger.Rows.PhaseClaims

open FvdepCore.Phase FvdepCore.Sandbox FvdepAudit.Phase.Spec

/-- P5: a step passes exactly when bwrap reports exit 0, the frame is complete + records the child
exiting 0, + no size cap was hit. -/
def verdictPass : Prop :=
  ∀ (s : Step) (r : StepResult),
    stepVerdict s r = .pass ↔
      r.outcome = Outcome.exited 0 ∧ r.frame = Frame.ok (Child.exited 0) true ∧ r.exhausted = false

/-- P5: a step fails on its input exactly when bwrap + the frame agree that its child exited with
code `c`, no size cap was hit, + `c` ≠ 0 (Lean refusing the input; never a library root) or `c` = 0
with an incomplete artifact family. -/
def verdictFailed : Prop :=
  ∀ (s : Step) (r : StepResult),
    (∃ reason, stepVerdict s r = .failed reason) ↔
      ∃ c complete,
        r.outcome = Outcome.exited c ∧
          r.frame = Frame.ok (Child.exited c) complete ∧
          r.exhausted = false ∧ ((c ≠ 0 ∧ s ≠ .libraryRoots) ∨ (c = 0 ∧ complete = false))

/-- P8: the driver executes exactly the steps up to + including the first that does not pass, in
order, + returns it with its verdict; every step passing ⇒ all run + none. -/
def driveTrace : Prop :=
  ∀ (answer : Step → StepResult),
    ∀ (steps acc : List Step),
      ((∀ s ∈ steps, stepVerdict s (answer s) = .pass) →
          (drive (record answer) steps).run acc = (none, acc ++ steps)) ∧
        ∀ pre s post,
          steps = pre ++ s :: post →
            (∀ p ∈ pre, stepVerdict p (answer p) = .pass) →
            stepVerdict s (answer s) ≠ .pass →
            (drive (record answer) steps).run acc =
              (some (s, stepVerdict s (answer s)), acc ++ pre ++ [s])

/-- S2: distinct module names without `/` have distinct path stems (U3 T3's names have none). -/
def stemInjective : Prop :=
  ∀ (a b : String) (_ha : '/' ∉ a.toList) (_hb : '/' ∉ b.toList) (_h : stem a = stem b), a = b

end FvdepLedger.Rows.PhaseClaims

namespace FvdepLedger.Rows.StepClaims

open FvdepCore.Step FvdepCore.Phase FvdepCore.Hash FvdepCore.Json FvdepAudit.Step.Spec
  FvdepAudit.Hash.Spec

/-- R8: the supervisor reads back exactly the status + the files the helper framed (files in path
order), when the status fits J's profile, the frame lies in H2's domain + every file path is
safe. -/
def frameRead : Prop :=
  ∀ (s : Status) (files : List (String × ByteArray)) (_hs : StatusFits s)
    (_hdom : FrameDomain Tag.step.spelling (("", print s.toJson) :: files))
    (_hsafe : ∀ f ∈ files, safePath f.1 = true), read (frameOf s files) = some ⟨s, byPath files⟩

/-- R8: the supervisor accepts only the helper's frames: whatever `read` accepts lies in
`frameRead`'s domain + is `frameOf` of the status + files it returns (a status entry in another
JSON spelling of the same value is refused); with `frameRead`, `read` accepts exactly them. -/
def frameExact : Prop :=
  ∀ (b : ByteArray) (o : Output) (_h : read b = some o),
    StatusFits o.status ∧
      FrameDomain Tag.step.spelling (("", print o.status.toJson) :: o.files) ∧
      (∀ f ∈ o.files, safePath f.1 = true) ∧ frameOf o.status o.files = b

end FvdepLedger.Rows.StepClaims

namespace FvdepLedger.Rows.CommandClaims

open FvdepCore FvdepAudit.Index.Command.Spec

/-- U4 C1 + C9 + C8 `IndexExact`: a completed run of `fvdep index [--check]` = exactly a run written
apart (`IndexRun`): the presence probe, the toolchain, the observations + the registry's judgment in
C9's order (build, load, registry form, certificate, entry rules), the replay, statuses + warnings +
the schema, then `--check`'s read + comparison or the replace of `index.json` by the decided bytes,
then the result line; each refusal = its messages on stderr + exit 2. -/
def indexExact : Prop :=
  ∀ (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response)) (code : UInt32),
    Plan.Runs (Index.Command.plan h check) evs (some code) ↔ IndexRun h check evs code

/-- U2 X5 for `fvdep index`: an interrupted run performed a prefix of a completed run written
apart. -/
def indexPrefix : Prop :=
  ∀ (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response)),
    Plan.Runs (Index.Command.plan h check) evs none →
      ∃ rest code, IndexRun h check (evs ++ rest) code

/-- U4 C1: every run, completed or interrupted, reads `index.json` alone + only with `--check`, and
replaces `index.json` alone + only without it. -/
def indexFiles : Prop :=
  ∀ (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response)) (r : Option UInt32),
    Plan.Runs (Index.Command.plan h check) evs r →
      ∀ x ∈ evs,
        (∀ f, x.1 = .read f → f = .index ∧ check = true) ∧
          ∀ f b, x.1 = .replace f b → f = .index ∧ check = false

/-- Interface §1's line rule for `fvdep index`: every output write of every run = one or more
lines, each ending in LF, with no Unicode `Cc` character inside a line. -/
def indexLines : Prop :=
  ∀ (h : ByteArray → String) (check : Bool) (evs : List (Eff × Response)) (r : Option UInt32),
    Plan.Runs (Index.Command.plan h check) evs r →
      ∀ x ∈ evs,
        ∀ s,
          (x.1 = .out s ∨ x.1 = .err s) →
            ∃ ls : List String,
              ls ≠ [] ∧
                s = String.join (ls.map (· ++ "\n")) ∧
                ∀ l ∈ ls, ∀ c ∈ l.toList, ¬(c.toNat < 32 ∨ 127 ≤ c.toNat ∧ c.toNat ≤ 159)

/-- `fvdep index [--check]` runs the index plan with SHA-256 hex digests. -/
def indexCli : Prop :=
  Cli.plan ["index"] = Index.Command.plan Cli.sha false ∧
    Cli.plan ["index", "--check"] = Index.Command.plan Cli.sha true

end FvdepLedger.Rows.CommandClaims

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
    { id := "hacl-sha256"
      what :=
        "SHA-256: HACL*'s C (verified upstream in F*/Low*: memory safety + functional " ++
          "correctness vs FIPS 180-4) + fvdep's FFI shim, chunk + streaming orchestration " ++
          "(`c/fvdep_sha256*.c`, `FvdepIO.Hash`)"
      reason :=
        "C has no Lean semantics: HACL*'s proof = upstream evidence (no collision-resistance " ++
          "claim); the shim + orchestration are small, reviewed + tested: `lake test` (FIPS " ++
          "180-4 examples incl. 10^6 × `a`, chunked `update` = one-shot, shared-state " ++
          "branching) + S5's blind suite (stage `codec-suite`, 1,212 cases: NIST CAVP short, " ++
          "long + Monte vectors, `sha256sum` differentials, update splits, chunk arithmetic + " ++
          "the total limit at lowered ceilings, `ofReader`, `sha256File`, concurrent Tasks; the " ++
          "C core under gcc ASan + UBSan, zero leaks)"
      ruling := "HACL* (verified upstream) + FFI wrapper (tested)"
      boundary :=
        [``FvdepIO.Hash.sha256, ``FvdepIO.Hash.Sha256.initState, ``FvdepIO.Hash.Sha256.absorb,
          ``FvdepIO.Hash.Sha256.squeeze] },
    { id := "toml-parse"
      what :=
        "Lake's TOML parser + elaborator (`Lake.Toml.loadToml`): text → table, repeated + " ++
          "redefined keys refused, the first error's position + message"
      reason :=
        "toolchain code (Decisions: trusted); `ofLake` names any key of another shape; " ++
          "`fvdep.toml` ≤ 64 KiB bounds its recursion depth (T1); tested by `lake test` " ++
          "(a printed manifest reads back, syntax + repeated keys refuse with Lake's line, a " ++
          "BOM refuses first) + T6's blind suite (stage `manifest-suite`: 1,850 credited " ++
          "cases through Lake's parser, `ofLake` + `validate`; the 4 `T.worst.*` cap cases = " ++
          "uncredited evidence of the parser at the cap: no fvdep mutant reaches them + a " ++
          "driver stack down to 256 KiB leaves them green)"
      ruling := "Lake.Toml + Lake comparison code (toolchain)"
      boundary := [``Lake.Toml.loadToml] },
    { id := "sys-shim"
      what :=
        "the persistence syscall shim `c/fvdep_sys.c` (one libc call per export, errno at once: " ++
          "the open variants, read, write, fsync, close, rename, unlink, flock) + its native " ++
          "writer guard (closed flag, mutex, finalizer close-if-open) + `FvdepIO.Sys`'s " ++
          "instantiation of the proven policy (`syscalls`: each request → its export, run once " ++
          "in the policy's order with its answer returned; the read buffer; the guard's closed " ++
          "mark; `withWriterLock` re-raising the act's exception after the close)"
      reason :=
        "C + the OS have no Lean semantics: each export is one reviewed syscall; the policy " ++
          "over them is proven (rows `FvdepIO.Sys.Policy`); the mapping is tested by `lake " ++
          "test` (replace over absent, present, symlink + directory targets, missing directory, " ++
          "read back, absent + empty reads, the caller's read cap, writer lock contention + " ++
          "exception, Writer lifecycle) + F6's blind suite (stage `sys-suite`, 2,819 credited " ++
          "cases through the dev driver `fvdep-dev`: an LD_PRELOAD fault injector scripting " ++
          "each syscall (every op × errno, `EINTR` budgets, short + zero reads and writes), a " ++
          "crash cut at every syscall of a `replace`, lock contention between processes, ZFS " ++
          "+ the gate host's filesystem, the shim + guard under gcc ASan + UBSan) + fuzz " ++
          "target `sys-actions` (action sequences over the shim + guard; corpus replayed " ++
          "under gcc ASan + UBSan by stage `fuzz-replay`)"
      ruling := "the persistence syscall shim + writer guard (tested)"
      boundary :=
        [``FvdepIO.Sys.Native.openFile, ``FvdepIO.Sys.Native.openDir, ``FvdepIO.Sys.Native.openRead,
          ``FvdepIO.Sys.Native.openLock, ``FvdepIO.Sys.Native.write, ``FvdepIO.Sys.Native.read,
          ``FvdepIO.Sys.Native.sync, ``FvdepIO.Sys.Native.close, ``FvdepIO.Sys.Native.rename,
          ``FvdepIO.Sys.Native.unlink, ``FvdepIO.Sys.Native.lock, ``FvdepIO.Sys.Native.writerNew,
          ``FvdepIO.Sys.Native.writerAcquire, ``FvdepIO.Sys.Native.writerMarkClosed,
          ``FvdepIO.Sys.Native.writerRelease] },
    { id := "lean-env"
      what :=
        "`fvdep index`'s observation filler (`FvdepIO.Index`): the presence probe + " ++
          "`lean-toolchain`'s bytes; the snapshot (the three root modules + the `.lean` files " ++
          "of `Fvdep`, `FvdepPreview` + `FvdepProofs` copied into a per-process run directory " ++
          "`.lake/fvdep-index/<pid>/`, removed at the end; a link followed for its content + " ++
          "marked irregular, a special file never opened); the build (Lake from fvdep's " ++
          "toolchain in a clean environment: PATH, HOME, ELAN_HOME, Lake's artifact cache off) " ++
          "+ its first `error:` line, Lake's progress relayed through the line rule; the load " ++
          "(`importModules` over the built oleans) + the facts read from that environment " ++
          "(declarations, marks, module imports + files, entry files, ABI application types, " ++
          "spec-type comparisons), `collectAxioms` per `FvdepProofs` theorem, the registry " ++
          "record fields, the kernel's verdict on each certificate literal (`Kernel.check` + " ++
          "`isDefEq`, synchronous); `leanchecker` over the built modules + its first " ++
          "rejection; `index.json`'s read + replace (`FvdepIO.Sys`)"
      reason :=
        "the toolchain's environment + Lake and `leanchecker` as processes have no Lean " ++
          "semantics to prove against: the observations are the plan claims' premise " ++
          "(Decisions U4 C-rules: `Facts`); tested by tester-5's blind suite (stage " ++
          "`index-suite`, 701 cases through the built `fvdep`: each C9 refusal class with its " ++
          "message, the schema-1 bytes + the entry count, identity (digest inputs: comments, " ++
          "proofs + unrelated entries), purity (planted artifacts, environment + an absolute " ++
          "path leave the bytes unchanged; `--check` + drift leave `index.json` untouched), two " ++
          "concurrent runs, load + write faults injected by an `LD_PRELOAD` library, Lake's " ++
          "progress through the line rule) + `tests/cli/smoke.sh` (`index --help`, `help " ++
          "index`, usage)"
      ruling := "`fvdep index`'s observation filler (tested)"
      boundary := [] },
    { id := "literal"
      what := "literal data (the version string `Fvdep.version`)"
      reason :=
        "a constant has no behaviour to prove; the gate's `meta` stage holds it equal to both " ++
          "lakefiles"
      ruling := "Literal data (the version string) is checked by the gate's `meta` stage"
      boundary := [] },
    { id := "bwrap"
      what :=
        "bubblewrap (≥ 0.8.0): how it reads the arguments fvdep emits (`bwrapRead`: each option " ++
          "by its name + arity, `--` ends the options) + what each operation does (namespaces, " ++
          "read-only binds, sized tmpfs, read-only remounts, the status lines on descriptor 3)"
      reason :=
        "an OS tool with no Lean semantics; the claims hold the arguments fvdep builds against " ++
          "a model of bwrap's reading, written from its manual (bubblewrap 0.11.1); the CI " ++
          "smoke + U5-B's isolation tests (G1) check the real tool on vflab + the CI runner"
      ruling := "bwrap"
      boundary := [] },
    { id := "lean-toolchain"
      what :=
        "`lean` + `leanexport` as processes: a compile's exit code (Lean refusing its input " ++
          "exits 1), its outputs + diagnostics, the export's bytes"
      reason :=
        "the toolchain is trusted (Decisions `Self-verification scope`: Lean parser, " ++
          "elaborator + exporter); P5's verdicts map its exit codes, tested by tester-6's blind " ++
          "suite through `fvdep-dev` (U5-D)"
      ruling := "Lean parser, elaborator + exporter"
      boundary := [] },
    { id := "cache-fs"
      what :=
        "the build cache's filesystem effects: publication (temp, fsync, rename, directory " ++
          "fsync), per-key locks + pins, the observed entry listings + use stamps eviction + " ++
          "validation decide over"
      reason :=
        "filesystem semantics have no Lean model here; the pure policies decide over observed " ++
          "state (K5, K6), the effects are tested by K7's work counts + tester-6's cache cases " ++
          "(U5-C)"
      ruling := "the build cache's filesystem effects"
      boundary := [] },
    { id := "sandbox-spawn"
      what :=
        "the sandbox runner's IO: `c/fvdep_spawn.c`'s supervisor exports (bwrap by " ++
          "`posix_spawn` with four pipes above descriptor 4, every descriptor ≥ 5 closed " ++
          "(`closefrom`, resolved at run time: absent → `ENOSYS`, never a spawn), an empty " ++
          "environment, every signal at its default + unmasked; poll, kill, waitpid) + " ++
          "`FvdepIO.Sandbox` (the pumps, the deadline's SIGKILL + a 5 s drain bound, the " ++
          "observation handed to the proven `classify` + `read`)"
      reason :=
        "C + the OS have no Lean semantics: each export is one reviewed call; the outcome + " ++
          "frame reading over the runner's observations are proven (rows `FvdepCore.Sandbox`, " ++
          "`FvdepCore.Step`); the IO is tested by tester-6's blind D2 cases (stage " ++
          "`sandbox-suite`) + the isolation cases (stage `isolation`, each killed by a mutant " ++
          "of `tests/isolation/mutants.py`)"
      ruling := "the sandbox spawn shim"
      boundary :=
        [``FvdepIO.Spawn.bwrap, ``FvdepIO.Spawn.poll, ``FvdepIO.Spawn.kill, ``FvdepIO.Spawn.wait] },
    { id := "step-helper"
      what :=
        "`fvdep-step`, PID 2 of every step: its arguments, non-dumpable, descriptor 4 taken " ++
          "only as an inherited pipe, `RLIMIT_CORE` = 1 + `RLIMIT_FSIZE`, the output " ++
          "directories, its child (`posix_spawnp`), the kill-all (refused in C unless PID 2), " ++
          "the `statvfs` samples, the regular files under `/fvdep/work/out` read without " ++
          "following a link, the frame written on descriptor 4"
      reason :=
        "C + the OS have no Lean semantics: the frame it writes reads back exactly (row " ++
          "`FvdepCore.Step`, `frameRead`); its IO is tested by the isolation cases (stage " ++
          "`isolation`: G1.helper, G1.grandchild, G1.core, G4.file-cap, R8.channel, " ++
          "G1.killall-guard, each killed by a mutant) + tester-6's D2 frame cases"
      ruling := "the step helper's IO"
      boundary :=
        [``FvdepIO.Spawn.nodump, ``FvdepIO.Spawn.channel, ``FvdepIO.Spawn.coreLimit,
          ``FvdepIO.Spawn.fileLimit, ``FvdepIO.Spawn.spawn, ``FvdepIO.Spawn.killAll,
          ``FvdepIO.Spawn.available, ``FvdepIO.Spawn.openRegular] }]

def cliRow : Row :=
  { component := `FvdepCore.Cli
    contract := "U1 K2; docs/interface.md §1–§2; U2 X5"
    claim :=
      "Outside `fvdep index [--check]` (row `FvdepCore.Index.Command`), every invocation " ++
        "writes one stream alone: exit 0 with stderr empty, or exit 2 with the usage on stderr " ++
        "+ stdout empty. The plan performs exactly the outcome's outputs (stdout, then " ++
        "stderr), an interrupted run a prefix of them; it never reads or replaces a file."
    claims :=
      [(``cliStreams, ``Cli.run_streams), (``cliPlanComplete, ``Cli.plan_complete),
        (``cliPlanInterrupted, ``Cli.plan_interrupted)]
    subject := ``Cli.plan
    path := [``main, ``Cli.plan]
    noCaller := ""
    residue := ["interpreter", "hacl-sha256", "runtime"]
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
    noCaller := "support"
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
    noCaller := "support"
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
        "`Receipt.wellFormed` decides well-formedness; each field's general type in the schema " ++
        "data = interface §6's."
    claims :=
      [(``DocClaims.receiptEncodeExact, ``FvdepAudit.Doc.Proof.receipt_encode),
        (``DocClaims.receiptSchemaExact, ``FvdepAudit.Doc.Proof.receipt_schema_exact),
        (``DocClaims.receiptDecodeOk, ``FvdepAudit.Doc.Proof.receipt_ok),
        (``DocClaims.receiptDecodeError, ``FvdepAudit.Doc.Proof.receipt_error),
        (``DocClaims.receiptValid, ``FvdepAudit.Doc.Proof.receipt_valid),
        (``DocClaims.receiptCheck, ``FvdepAudit.Doc.Proof.receipt_check),
        (``DocClaims.receiptKindsExact, ``FvdepAudit.Doc.Proof.receipt_kinds)]
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
        "well-formedness; each field's general type in the schema data = interface §6's."
    claims :=
      [(``DocClaims.lockEncodeExact, ``FvdepAudit.Doc.Proof.lock_encode),
        (``DocClaims.lockSchemaExact, ``FvdepAudit.Doc.Proof.lock_schema_exact),
        (``DocClaims.lockDecodeOk, ``FvdepAudit.Doc.Proof.lock_ok),
        (``DocClaims.lockDecodeError, ``FvdepAudit.Doc.Proof.lock_error),
        (``DocClaims.lockValid, ``FvdepAudit.Doc.Proof.lock_valid),
        (``DocClaims.lockCheck, ``FvdepAudit.Doc.Proof.lock_check),
        (``DocClaims.lockKindsExact, ``FvdepAudit.Doc.Proof.lock_kinds),
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

/-- U3 H: hex + framing (pure). -/
def hashFrameRow : Row :=
  { component := `FvdepCore.Hash.Frame
    contract := "U3 H1–H4"
    claim :=
      "`hex` writes each byte as two lowercase hex digits, high nibble first; `frame` emits " ++
        "exactly H2's layout (tag, count, then the files in path order; UTF-8 lengths as 8-byte " ++
        "big-endian numbers); inside H2's domain `unframe` returns the tag + the files in path " ++
        "order, so equal frames have equal tags + the same files; `unframe` accepts exactly " ++
        "frames (domain, strictly ascending paths, every byte consumed)."
    claims :=
      [(``HashClaims.hexExact, ``FvdepAudit.Hash.Proof.hex_exact),
        (``HashClaims.frameLayout, ``FvdepAudit.Hash.Proof.frame_layout),
        (``HashClaims.frameDecode, ``FvdepAudit.Hash.Proof.frame_decode),
        (``HashClaims.frameInjective, ``FvdepAudit.Hash.Proof.frame_injective),
        (``HashClaims.unframeExact, ``FvdepAudit.Hash.Proof.unframe_exact)]
    subject := ``FvdepCore.Hash.frame
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

/-- U3 S + H3: the digest producers call (tested residue `hacl-sha256`). -/
def sha256DigestRow : Row :=
  { component := `FvdepIO.Sha256
    contract := "U3 S1–S4 + H3"
    claim :=
      "`digest t files` = lowercase hex of SHA-256 over `frame t.spelling files`; SHA-256 = " ++
        "HACL*'s verified C behind the FFI (tested residue `hacl-sha256`; `digest` itself: S5's " ++
        "blind suite, stage `codec-suite`, against an independent frame encoder). Its hash step " ++
        "`sha256Hex` = `fvdep index`'s (`Cli.sha` over `entryFrame` = `digest .entry` of the " ++
        "closure files, by `rfl` in `tool/Tests.lean`)."
    claims := []
    subject := ``FvdepIO.Hash.digest
    path := []
    noCaller := "U5"
    residue := ["runtime"]
    unproven := ["hacl-sha256"] }

/-- U3 S3: streaming SHA-256; the byte count saturates (never wraps) on its way to the C check. -/
def sha256StreamRow : Row :=
  { component := `FvdepIO.Sha256
    contract := "U3 S3"
    claim :=
      "`saturate`, the byte count `finish` passes to the C limit check (2^61 bytes; residue " ++
        "`hacl-sha256`), = min n (2^64 − 1), never wrapped. `update`, `finish`, `ofReader` + " ++
        "`sha256File` join a row's subject closure when U8 wires them."
    claims := [(``HashClaims.saturateLaw, ``FvdepAudit.Hash.Proof.saturate_toNat)]
    subject := ``FvdepIO.Hash.Sha256.saturate
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := ["hacl-sha256"] }

/-- U3 T1 + T5: the text stage before Lake's parser. -/
def manifestTextRow : Row :=
  { component := `FvdepCore.Manifest
    contract := "U3 T1 + T5"
    claim :=
      "`utf8ErrorOffset` is `none` exactly on valid UTF-8, else the length of the longest valid " ++
        "prefix; `textStage` refuses more than 65,536 bytes first, then a leading BOM, then the " ++
        "first invalid UTF-8 offset, else returns the text whose bytes are the input."
    claims :=
      [(``ManifestClaims.utf8Offset, ``FvdepAudit.Manifest.Proof.utf8Offset),
        (``ManifestClaims.textStageExact, ``FvdepAudit.Manifest.Proof.textStage_spec)]
    subject := ``FvdepCore.Manifest.textStage
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := [] }

/-- U3 T2–T3 + T5: validation + extraction of the typed manifest. -/
def manifestValidateRow : Row :=
  { component := `FvdepCore.Manifest
    contract := "U3 T2–T3 + T5"
    claim :=
      "`validate` accepts exactly the trees that spell a well-formed manifest (member order " ++
        "free) + returns that manifest, else refuses with the first of T3 + D5's ordered " ++
        "violations (repeated keys, discriminators, unknown, forbidden + missing keys, values " ++
        "in key byte order, list overlap); the tree a well-formed manifest prints to validates " ++
        "back to it."
    claims :=
      [(``ManifestClaims.validateOk, ``FvdepAudit.Manifest.Proof.validate_ok),
        (``ManifestClaims.validateError, ``FvdepAudit.Manifest.Proof.validate_error),
        (``ManifestClaims.validateWellFormed, ``FvdepAudit.Manifest.Proof.validate_wellFormed),
        (``ManifestClaims.treeRoundTrip, ``FvdepAudit.Manifest.Proof.tree_roundtrip)]
    subject := ``FvdepCore.Manifest.validate
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := [] }

/-- U3 T4 + T5: the canonical printer `init` + `upgrade` write with. -/
def manifestPrintRow : Row :=
  { component := `FvdepCore.Manifest
    contract := "U3 T4 + T5"
    claim :=
      "`printManifest` emits exactly T4's canonical bytes for a well-formed manifest, a " ++
        "document of T4's TOML 1.0 subset (keyvals, one- + two-key headers, basic strings, " ++
        "decimal integers, inline string arrays) denoting `toTree m`; Lake's agreement with " ++
        "that subset = residue `toml-parse` (tested by `lake test`: a printed manifest reads " ++
        "back), never claimed."
    claims :=
      [(``ManifestClaims.printExact, ``FvdepAudit.Manifest.Proof.print_exact),
        (``ManifestClaims.printDenotes, ``FvdepAudit.Manifest.Proof.print_denotes)]
    subject := ``FvdepCore.Manifest.printManifest
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := [] }

/-- U3 T1 + T5: Lake's table → `Tree` (the read path's step after Lake's parser). -/
def tomlReadRow : Row :=
  { component := `FvdepIO.Toml
    contract := "U3 T1 + T5"
    claim :=
      "`ofLake` rebuilds Lake's table exactly (keys = their one string component, scalars, " ++
        "element + member order, float/date-time tags) or names a key of another shape. " ++
        "`parseTree` (Lake's parser, residue `toml-parse`), `readManifest` (text stage → " ++
        "`parseTree` → `validate`) + `ReadError.code` (`internal` for that key) join a row's " ++
        "subject closure when U8 wires the read path as a plan effect."
    claims := [(``ManifestClaims.ofLakeExact, ``FvdepAudit.Manifest.Proof.ofLake_exact)]
    subject := ``FvdepIO.Toml.ofLake
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := ["toml-parse"] }

/-- U3 F2: the names the protocol claims spell as text. -/
def sysNamesRow : Row :=
  { component := `FvdepIO.Sys.Types
    contract := "U3 F2 + F4"
    claim :=
      "`tempPath`, `Path.at` + `lockPath` spell F2's names: `<dir>/.<name>.tmp-<pid>-<n>`, " ++
        "`<dir>/<name>`, `<dir>/.fvdep-writer.lock` (the texts the protocol claims name)."
    claims :=
      [(``SysClaims.tempPathText, ``FvdepAudit.Sys.Proof.tempPath_text),
        (``SysClaims.atText, ``FvdepAudit.Sys.Proof.at_text),
        (``SysClaims.lockPathText, ``FvdepAudit.Sys.Proof.lockPath_text)]
    subject := ``FvdepIO.Sys.tempPath
    path := []
    noCaller := "support"
    residue := ["runtime"]
    unproven := [] }

/-- U3 F3 + F4 (fvapi's port): create-exclusive over every syscall script. -/
def sysCreateRow : Row :=
  { component := `FvdepIO.Sys.Policy
    contract := "U3 F3 + F4"
    claim :=
      "`create` (create-exclusive, one F3 step): its result is exactly the one `Create` assigns " ++
        "to its calls, ok + error alike; one F3 step is at most `budget + 1` calls of one " ++
        "request, the 65th EINTR ending it as `retryExhausted`."
    claims :=
      [(``SysClaims.createExact, ``FvdepAudit.Sys.Proof.create_exact),
        (``SysClaims.retryBounded, ``FvdepAudit.Sys.Proof.retry_bounded)]
    subject := ``FvdepIO.Sys.Policy.create
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := [] }

/-- U3 F3 + F4 (fvapi's port): a writer's calls. -/
def sysWriterRow : Row :=
  { component := `FvdepIO.Sys.Policy
    contract := "U3 F3 + F4"
    claim :=
      "`writer` (write all, fsync, one close, finalizer): its result is exactly the one " ++
        "`WriterOperation` assigns to its calls; a success acknowledged every byte; it uses " ++
        "only its descriptor, none once closed; a writer's calls (`actions`) attempt close at " ++
        "most once."
    claims :=
      [(``SysClaims.writerExact, ``FvdepAudit.Sys.Proof.writer_exact),
        (``SysClaims.writeAcknowledged, ``FvdepAudit.Sys.Proof.write_acknowledged),
        (``SysClaims.sameDescription, ``FvdepAudit.Sys.Proof.same_description),
        (``SysClaims.closeOnceActions, ``FvdepAudit.Sys.Proof.close_once_actions)]
    subject := ``FvdepIO.Sys.Policy.writer
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := [] }

/-- U3 F3 + F4 (fvapi's port): `syncDir`. -/
def sysDirectoryRow : Row :=
  { component := `FvdepIO.Sys.Policy
    contract := "U3 F3 + F4"
    claim :=
      "`directory` (`syncDir`: open, fsync, one close): its result is exactly the one " ++
        "`Directory` assigns to its calls; it closes the directory it opened exactly once."
    claims :=
      [(``SysClaims.directoryExact, ``FvdepAudit.Sys.Proof.directory_exact),
        (``SysClaims.closeOnceDirectory, ``FvdepAudit.Sys.Proof.close_once_directory)]
    subject := ``FvdepIO.Sys.Policy.directory
    path := []
    noCaller := "support"
    residue := ["runtime"]
    unproven := [] }

/-- U3 F2 + F4: the durable replace (U8 wires it for every project write). -/
def sysReplaceRow : Row :=
  { component := `FvdepIO.Sys.Policy
    contract := "U3 F2 + F4"
    claim :=
      "`replace`'s calls + result follow F2's protocol written apart (temp walk, all bytes, " ++
        "fsync, one close, one rename step, `syncDir`; cleanup closes once, then unlinks only " ++
        "its own temp; causes in order; `durability`), which fixes the result; one rename step " ++
        "is the only call naming the target; over the directory model the target holds its " ++
        "old state or the new bytes after any run or interruption (new on success), which is " ++
        "U2 X4's `Holds` step for a present target; a run reads its answers in order (call k " ++
        "+ whether it is issued depend on answers 0…k−1 alone). Assumed (F4; residues `os` + " ++
        "`sys-shim`): a stable directory, cooperative writers (fvdep processes under the " ++
        "writer lock), an atomic rename, Linux `close` (the descriptor released on every " ++
        "return; POSIX.1-2024 lets `EINTR` keep it open), the native run issuing the policy's " ++
        "requests in order, each answered once (row `sysNative`); with these, a process " ++
        "stopped after k calls issued the first k calls of a complete run on the same answers " ++
        "(F4's model step)."
    claims :=
      [(``SysClaims.replaceExact, ``FvdepAudit.Sys.Proof.replace_exact),
        (``SysClaims.replaceSingleTouch, ``FvdepAudit.Sys.Proof.replace_single_touch),
        (``SysClaims.replaceOldOrNew, ``FvdepAudit.Sys.Proof.replace_old_or_new),
        (``SysClaims.replaceHolds, ``FvdepAudit.Sys.Proof.replace_holds),
        (``SysClaims.replaceCausal, ``FvdepAudit.Sys.Proof.replace_causal)]
    subject := ``FvdepIO.Sys.Policy.replace
    path := []
    noCaller := "support"
    residue := ["os", "runtime", "sys-shim"]
    unproven := [] }

/-- U3 F2: the project read (U8 wires it). -/
def sysReadRow : Row :=
  { component := `FvdepIO.Sys.Policy
    contract := "U3 F2"
    claim :=
      "`readFile`'s calls + result follow the protocol written apart (ENOENT = absent, reads " ++
        "of ≤ 2^20 bytes until 0, the caller's byte cap (`FvdepIO.Sys.readFile`'s default " ++
        "2^30), one close, the close's failure as primary or secondary cause), which fixes the " ++
        "result."
    claims := [(``SysClaims.readExact, ``FvdepAudit.Sys.Proof.read_exact)]
    subject := ``FvdepIO.Sys.Policy.readFile
    path := []
    noCaller := "support"
    residue := ["runtime"]
    unproven := [] }

/-- U3 F2 + F4: the writer lock (U8 decides which commands hold it). -/
def sysLockRow : Row :=
  { component := `FvdepIO.Sys.Policy
    contract := "U3 F2 + F4"
    claim :=
      "`withLock` runs `act` exactly when the lock file's open + `flock` succeed, once, and " ++
        "returns its result; the description is closed on every exit after its open; a refusal " ++
        "(EWOULDBLOCK = `busy`) or an open failure runs nothing."
    claims := [(``SysClaims.lockExact, ``FvdepAudit.Sys.Proof.lock_exact)]
    subject := ``FvdepIO.Sys.Policy.withLock
    path := []
    noCaller := "U8"
    residue := ["runtime"]
    unproven := [] }

/-- U3 F1–F2: the policy in `IO` over the shim (tested residue `sys-shim`). -/
def sysNativeRow : Row :=
  { component := `FvdepIO.Sys
    contract := "U3 F1–F2"
    claim :=
      "`replace`, `readFile`, `withWriterLock`, `Writer` + `syncDir` run the proven policy over " ++
        "`syscalls` (each request → its one syscall export, run in the policy's order + " ++
        "answered once; the native writer guard: `Writer.create` registers the created " ++
        "descriptor (`writerNew`), each later `Writer` operation runs between `writerAcquire` " ++
        "+ `writerRelease`, a guarded close marks the guard closed (`writerMarkClosed`) before " ++
        "its one close, the guard's finalizer closes a descriptor still open; residue " ++
        "`sys-shim`)."
    claims := []
    subject := ``FvdepIO.Sys.replace
    path := []
    noCaller := "support"
    residue := ["os", "runtime"]
    unproven := ["sys-shim"] }

def protocolRow : Row :=
  { component := `FvdepCore.Protocol
    contract := "U4 B2–B4; docs/interface.md §8"
    claim :=
      "Each value encodes to its §8 layout; decoding at a type returns exactly the value whose " ++
        "layout it is, refusing every other value; a value whose strings fit encodes to a valid " ++
        "value; a request line decodes exactly when J decodes it to the target op's request " ++
        "object with typed arguments; a reply line = its reply object's canonical text + LF; " ++
        "the request lines = the LF-separated segments."
    claims :=
      [(``ProtocolClaims.valLayout, ``FvdepAudit.Protocol.Proof.val_layout),
        (``ProtocolClaims.valExact, ``FvdepAudit.Protocol.Proof.val_exact),
        (``ProtocolClaims.valValid, ``FvdepAudit.Protocol.Proof.val_valid),
        (``ProtocolClaims.requestExact, ``FvdepAudit.Protocol.Proof.request_exact),
        (``ProtocolClaims.replyExact, ``FvdepAudit.Protocol.Proof.reply_layout),
        (``ProtocolClaims.linesExact, ``FvdepAudit.Protocol.Proof.lines_exact)]
    subject := ``FvdepCore.Protocol.decodeRequest
    path := []
    noCaller := "U5b"
    residue := []
    unproven := [] }

def protocolSigRow : Row :=
  { component := `FvdepCore.Protocol.Sig
    contract := "U4 B1 (C's encodability rule V3)"
    claim :=
      "`sigOf` returns a spec type's argument + result types exactly when the type is " ++
        "non-dependent arrows over §8's types (`Option X` result = `option`), read as `Expr` " ++
        "shapes without reduction, metadata transparent; else `none`."
    claims := [(``ProtocolClaims.sigExact, ``FvdepAudit.Protocol.Proof.sigOf_iff)]
    subject := ``FvdepCore.Protocol.sigOf
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def indexDecodeRow : Row :=
  { component := `FvdepCore.Index.Doc
    contract := "U4 C6 + C8; Decisions Data formats"
    claim :=
      "`index.json` schema 1: on a J1-valid value the D5 walk accepts exactly the layouts of " ++
        "indexes whose nodes are well formed; `IndexFile.ofJson` accepts exactly the layouts of " ++
        "well-formed indexes (the relational clauses V8 + V9 included) and refuses with the " ++
        "walk's first violation, else the first relational one; `decodeIndex` = J's decode of " ++
        "the bytes with one final LF removed, then `IndexFile.ofJson`: it accepts exactly the " ++
        "bytes J decodes to a well-formed index's layout, a text refusal is J's, a document " ++
        "refusal is that value's first violation; a well-formed index's canonical bytes decode " ++
        "back to it."
    claims :=
      [(``IndexClaims.indexSchemaExact, ``FvdepAudit.Index.Proof.index_schema_exact),
        (``IndexClaims.indexDecodeOk, ``FvdepAudit.Index.Proof.index_ok),
        (``IndexClaims.indexDecodeError, ``FvdepAudit.Index.Proof.index_error),
        (``IndexClaims.indexBytesEncode, ``FvdepAudit.Index.Proof.index_bytes_encode),
        (``IndexClaims.indexBytesOk, ``FvdepAudit.Index.Proof.index_bytes_ok),
        (``IndexClaims.indexBytesDoc, ``FvdepAudit.Index.Proof.index_bytes_doc),
        (``IndexClaims.indexBytesText, ``FvdepAudit.Index.Proof.index_bytes_text)]
    subject := ``FvdepCore.Index.decodeIndex
    path := []
    noCaller := "U5b"
    residue := []
    unproven := [] }

def indexEncodeRow : Row :=
  { component := `FvdepCore.Index.Doc
    contract := "U4 C6 + C8; Decisions Data formats"
    claim :=
      "`encodeIndex` refuses an index outside schema 1 with the first violation of its layout " ++
        "(the walk's, else the first relational one), else returns its canonical text + LF; " ++
        "an index's JSON is exactly its C6 layout; a well-formed index's JSON is J1-valid; " ++
        "`IndexFile.wellFormed` decides `IndexWellFormed`; each field's general type in the " ++
        "schema data = C6's."
    claims :=
      [(``IndexClaims.indexEncodeBytes, ``FvdepAudit.Index.Proof.encode_index_iff),
        (``IndexClaims.indexEncodeError, ``FvdepAudit.Index.Proof.encode_index_error),
        (``IndexClaims.indexEncodeExact, ``FvdepAudit.Index.Proof.index_encode),
        (``IndexClaims.indexValid, ``FvdepAudit.Index.Proof.index_valid),
        (``IndexClaims.indexCheck, ``FvdepAudit.Index.Proof.index_check),
        (``IndexClaims.indexKindsExact, ``FvdepAudit.Index.Proof.index_kinds)]
    subject := ``FvdepCore.Index.encodeIndex
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def registryReadRow : Row :=
  { component := `FvdepCore.Index.Registry
    contract := "U4 C2 + C8"
    claim :=
      "Registry reading: the walk (`decode` + its list loop `spine`) reads an `Expr` exactly as " ++
        "the accepted-forms relation, written apart, relates it (metadata, `let`/`have`, root " ++
        "registry module constants, `<M>.entry` references, `List.nil`/`List.cons`/the standard " ++
        "`++`, constructor applications over string + name literals, `Option`, enumerations); " ++
        "`readRaw` then `Lists.ofRaw` (as `fvdep index`'s `judge` calls them) return exactly " ++
        "the records the four list constants denote; the shipped record forms = the registry " ++
        "types' field order."
    claims :=
      [(``RegistryClaims.registryDecodeExact, ``FvdepAudit.Registry.Proof.registry_decode),
        (``RegistryClaims.registryReadExact, ``FvdepAudit.Registry.Proof.registry_read),
        (``RegistryClaims.registryFormsExact, ``FvdepAudit.Registry.Proof.registry_forms)]
    subject := ``FvdepCore.Index.Registry.readRaw
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def registryProofsRow : Row :=
  { component := `FvdepCore.Index.Registry
    contract := "U4 C2 + C5"
    claim :=
      "`readProofs` returns exactly the obligation → theorem map (+ compat theorem) the proof " ++
        "registry constant denotes."
    claims := [(``RegistryClaims.registryProofsExact, ``FvdepAudit.Registry.Proof.registry_proofs)]
    subject := ``FvdepCore.Index.Registry.readProofs
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def registryLiteralRow : Row :=
  { component := `FvdepCore.Index.Registry
    contract := "U4 C2 + C8"
    claim :=
      "`listLiteral` (a registry list's literal: constructor applications in field order) " ++
        "decodes back to exactly the values written, for plain forms (no `entry` or `any` " ++
        "position) + values of their shape — the certificate's lists among them."
    claims :=
      [(``RegistryClaims.registryReencodeExact, ``FvdepAudit.Registry.Proof.registry_reencode),
        (``RegistryClaims.registryCertificateExact,
          ``FvdepAudit.Registry.Proof.registry_certificate)]
    subject := ``FvdepCore.Index.Registry.listLiteral
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def registryCertificateRow : Row :=
  { component := `FvdepCore.Index.Registry
    contract := "U4 C2 + C8"
    claim :=
      "`certificate` (the lists C-command's kernel check compares with the registry constants: " ++
        "`modules`' records with their entry annotations dropped, `profiles` while empty, " ++
        "`notices`, `removed`) writes values whose literals decode back to exactly those values."
    claims :=
      [(``RegistryClaims.registryCertificateExact,
          ``FvdepAudit.Registry.Proof.registry_certificate)]
    subject := ``FvdepCore.Index.Registry.certificate
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def validateRow : Row :=
  { component := `FvdepCore.Index.Rules
    contract := "U4 C3 + C4 + C9 + C8"
    claim :=
      "Entry rules: `validate` accepts exactly the registries for which every row of C9's " ++
        "order holds — each listed entry's own file observed; per entry (in `modules` order) " ++
        "V1–V7 + C4's file check, V3's flags over `reach`'s checked constants; the unlisted " ++
        "entry files; V8 notices; V9 removed records; V10 profiles — the rows written apart; " ++
        "a refusal is what the first failing row may report; `reach` holds exactly the library " ++
        "constants reached from an entry's roots through definition values."
    claims :=
      [(``RulesClaims.validateAccepts, ``FvdepAudit.Index.Rules.Proof.validate_accepts),
        (``RulesClaims.validateFirst, ``FvdepAudit.Index.Rules.Proof.validate_first),
        (``RulesClaims.reachExact, ``FvdepAudit.Index.Rules.Proof.reach_exact)]
    subject := ``FvdepCore.Index.Rules.validate
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def closureRow : Row :=
  { component := `FvdepCore.Index.Rules
    contract := "U4 C4 + C8"
    claim :=
      "`closure F M` holds exactly the modules reachable from `M` through the import edges of " ++
        "`M` + the `Fvdep` modules it reaches, each once."
    claims := [(``RulesClaims.closureExact, ``FvdepAudit.Index.Rules.Proof.closure_exact)]
    subject := ``FvdepCore.Index.Rules.closure
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def statusesRow : Row :=
  { component := `FvdepCore.Index.Statuses
    contract := "U4 C5 + C9 + C8"
    claim :=
      "Statuses: after `validate` accepted the lists, `statuses` returns exactly each entry's " ++
        "obligation statuses + axioms (C5's first failing condition → open with no axioms + its " ++
        "warning; else proven, trusts or open from the observed axioms outside the standard " ++
        "three, strictly ascending), its compat edge, and C9's warnings in order, written " ++
        "apart; " ++
        "with no such statuses (a counted theorem without an observed axiom list) it refuses."
    claims := [(``StatusesClaims.statusesExact, ``FvdepAudit.Index.Statuses.Proof.statuses_exact)]
    subject := ``FvdepCore.Index.Statuses.statuses
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def closureFilesRow : Row :=
  { component := `FvdepCore.Index.Statuses
    contract := "U4 C4"
    claim :=
      "Digest input: `closureFiles` (the files an entry's digest frames) holds exactly the " ++
        "closure modules' (canonical path, observed bytes); its paths are distinct when every " ++
        "closure module is plain (string components without `/`), the frame's path premise."
    claims :=
      [(``StatusesClaims.closureFilesExact, ``FvdepAudit.Index.Statuses.Proof.closureFiles_exact),
        (``StatusesClaims.closureFilesDistinct,
          ``FvdepAudit.Index.Statuses.Proof.closureFiles_distinct)]
    subject := ``FvdepCore.Index.Statuses.closureFiles
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def assembleRow : Row :=
  { component := `FvdepCore.Index.Assemble
    contract := "U4 C4 + C6 + C9 + C8"
    claim :=
      "Index value: after `validate` accepted the lists, `assemble` returns exactly the index " ++
        "value written apart — the entries' statuses, the operations = those entries strictly " ++
        "ascending in C6's (id, version) order, each with its digest `h` of the H3 " ++
        "`fvdep/entry/1` frame of its closure files, notices + removed records in registry " ++
        "order, the `lean-toolchain` text without surrounding whitespace — + C9's warnings in " ++
        "`modules` order; with no such statuses it refuses."
    claims := [(``AssembleClaims.assembleExact, ``FvdepAudit.Index.Assemble.Proof.assemble_exact)]
    subject := ``FvdepCore.Index.Assemble.assemble
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

def historyRow : Row :=
  { component := `FvdepCore.Index.History
    contract := "U4 C7 + C9 + C8"
    claim :=
      "History: `history` returns exactly the violations written apart, in C9's order — the " ++
        "parents' divergence, then HEAD's lines, then each parent's: per baseline its " ++
        "operations in index order (≤ 1 line each: changed digest, vanished, removed without a " ++
        "toolchain change, the first removal's witness — lastCommit + toolchain), then its " ++
        "removed records' + notices' extension; an undecodable index = its one line."
    claims := [(``HistoryClaims.historyExact, ``FvdepAudit.Index.History.Proof.history_exact)]
    subject := ``FvdepCore.Index.History.history
    path := []
    noCaller := "U7"
    residue := []
    unproven := [] }

def indexCommandRow : Row :=
  { component := `FvdepCore.Index.Command
    contract := "U4 C1 + C9 + C8; docs/interface.md §1"
    claim :=
      "`fvdep index [--check]`: a completed run of the plan = exactly a run written apart — " ++
        "C9's stages in order (library presence, toolchain, build, load, registry form, " ++
        "certificate, entry rules, replay, statuses + warnings, schema), each refusal its " ++
        "messages on stderr + exit 2, then `--check`'s read + comparison (`index.json is " ++
        "current` 0, `differs` 1) or the replace of `index.json` by the decided bytes; an " ++
        "interrupted run = a prefix of a completed one; every run reads `index.json` alone + " ++
        "only with `--check`, replaces it alone + only without; every output write = whole " ++
        "lines, no Unicode `Cc` character inside a line; `fvdep index [--check]` runs this " ++
        "plan with SHA-256 hex digests."
    claims :=
      [(``CommandClaims.indexExact, ``FvdepAudit.Index.Command.Proof.index_exact),
        (``CommandClaims.indexPrefix, ``FvdepAudit.Index.Command.Proof.index_prefix),
        (``CommandClaims.indexFiles, ``FvdepAudit.Index.Command.Proof.index_files),
        (``CommandClaims.indexLines, ``FvdepAudit.Index.Command.Proof.index_lines),
        (``CommandClaims.indexCli, ``Cli.plan_index)]
    subject := ``FvdepCore.Index.Command.plan
    path := [``main, ``Cli.plan, ``FvdepCore.Index.Command.plan]
    noCaller := ""
    residue := ["interpreter", "lean-env", "hacl-sha256", "runtime"]
    unproven := [] }

def indexFillerRow : Row :=
  { component := `FvdepIO.Index
    contract := "U4 C1 + C2 + C8 + C9"
    claim :=
      "`fvdep index`'s observations: the presence probe; a fresh build of the working copy's " ++
        "snapshot, its load + the facts, axiom lists, record fields + the kernel's verdict on " ++
        "each certificate literal; the toolchain's `leanchecker` over the built modules; " ++
        "`index.json`'s read + replace."
    claims := []
    subject := ``FvdepIO.Index.libraryFacts
    path := []
    noCaller := "support"
    residue := ["os", "runtime"]
    unproven := ["lean-env"] }

/-- U5 R1: the bwrap arguments of a sandbox step (no caller before U8's `check`). -/
def sandboxArgsRow : Row :=
  { component := `FvdepCore.Sandbox
    contract := "U5 R1"
    claim :=
      "`bwrapArgs s`: bwrap reads exactly `ops s`, then the helper + the step's argv verbatim; " ++
        "the writable storage = two sized tmpfs (`/fvdep/work`, `/tmp`); the environment = " ++
        "cleared + exactly the spec's variables; `/` + `/dev` remounted read-only after every " ++
        "mount; every destination in the layout. Every host path is bound read-only: `Op` has " ++
        "no writable bind, network or namespace-sharing constructor."
    claims :=
      [(``SandboxClaims.argsRead, ``FvdepAudit.Sandbox.Proof.bwrapArgs_read),
        (``SandboxClaims.writableExact, ``FvdepAudit.Sandbox.Proof.ops_writable),
        (``SandboxClaims.envExact, ``FvdepAudit.Sandbox.Proof.ops_env),
        (``SandboxClaims.remountLast, ``FvdepAudit.Sandbox.Proof.ops_finish),
        (``SandboxClaims.destInLayout, ``FvdepAudit.Sandbox.Proof.ops_dest)]
    subject := ``FvdepCore.Sandbox.bwrapArgs
    path := []
    noCaller := "U8"
    residue := ["bwrap"]
    unproven := [] }

/-- U5 R6: a step's outcome from bwrap's status lines. -/
def sandboxOutcomeRow : Row :=
  { component := `FvdepCore.Sandbox
    contract := "U5 R5 + R6"
    claim :=
      "`classify`: one exit-code line → `exited` (a later deadline kill changes nothing); two " ++
        "or more → `protocol`; none → `timedOut` when the supervisor killed the step, else " ++
        "`setupFailed` with bwrap's first stderr line."
    claims := [(``SandboxClaims.outcomeExact, ``FvdepAudit.Sandbox.Proof.classify_exact)]
    subject := ``FvdepCore.Sandbox.classify
    path := []
    noCaller := "U8"
    residue := ["bwrap"]
    unproven := [] }

/-- U5 K2: the build plan over a module graph. -/
def buildPlanRow : Row :=
  { component := `FvdepCore.Build
    contract := "U5 K2"
    claim :=
      "`plan nodes roots`: an order = a valid build order of the closure (each reached module " ++
        "once, a node, after all its imports); a refusal names a duplicate, a reached module " ++
        "no node provides (+ who imports it) or a nonempty set of reached modules each " ++
        "importing another of them; a missing or stuck refusal ⇒ no valid order exists."
    claims :=
      [(``BuildClaims.planValid, ``FvdepAudit.Build.Proof.plan_ok),
        (``BuildClaims.planDuplicate, ``FvdepAudit.Build.Proof.plan_duplicate),
        (``BuildClaims.planMissing, ``FvdepAudit.Build.Proof.plan_missing),
        (``BuildClaims.planStuck, ``FvdepAudit.Build.Proof.plan_stuck),
        (``BuildClaims.planRefuses, ``FvdepAudit.Build.Proof.plan_refuses)]
    subject := ``FvdepCore.Build.plan
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U5 K1: a cached module's key preimage. -/
def buildKeyRow : Row :=
  { component := `FvdepCore.Build
    contract := "U5 K1 + T2"
    claim :=
      "`preimage k` = the canonical JSON of `keyValue k` (recipe incl. the toolchain " ++
        "fingerprint, module, path, the source's SHA-256, the ordered imports with their " ++
        "keys): within the JSON profile's bounds distinct inputs have distinct preimages, so " ++
        "two inputs share a key (`keyOf h` = SHA-256 of the preimage) only through a SHA-256 " ++
        "collision (a stated premise, never a theorem)."
    claims := [(``BuildClaims.preimageInjective, ``FvdepAudit.Build.Proof.preimage_injective)]
    subject := ``FvdepCore.Build.preimage
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U5 K5: the eviction policy over the observed entries. -/
def buildEvictRow : Row :=
  { component := `FvdepCore.Build
    contract := "U5 K5"
    claim :=
      "`evictPlan entries target`: from the unpinned entries in (used, key) order, the " ++
        "shortest prefix bringing the charged total to the target or under it — all of them " ++
        "when none does; a pinned entry is never named."
    claims := [(``BuildClaims.evictExact, ``FvdepAudit.Build.Proof.evict_exact)]
    subject := ``FvdepCore.Build.evictPlan
    path := []
    noCaller := "U8"
    residue := ["cache-fs"]
    unproven := [] }

/-- U5 K6: a cache entry's validation over its observed files. -/
def buildValidateRow : Row :=
  { component := `FvdepCore.Build
    contract := "U5 K6"
    claim :=
      "`validate h dir m files` ⇔ the manifest is schema 1, its key inputs hash to the " ++
        "directory's name, no artifact takes a metadata file's name, both metadata files are " ++
        "present, every listed artifact is present with its size + digest, every file present " ++
        "is an artifact or one of the two metadata files."
    claims := [(``BuildClaims.validateExact, ``FvdepAudit.Build.Proof.validate_exact)]
    subject := ``FvdepCore.Build.validate
    path := []
    noCaller := "U8"
    residue := ["cache-fs"]
    unproven := [] }

/-- U5 P5: a step's verdict. -/
def phaseVerdictRow : Row :=
  { component := `FvdepCore.Phase
    contract := "U5 P5"
    claim :=
      "`stepVerdict`: a step passes exactly on bwrap exit 0 + a complete frame recording the " ++
        "child's exit 0 + no size cap hit; it fails on its input exactly when bwrap + the " ++
        "frame agree on the child's exit code, no size cap was hit, + that code is nonzero " ++
        "(Lean refusing it; never a library root) or 0 with an incomplete artifact family; " ++
        "every other step gets `infra` (`Verdict`'s third case)."
    claims :=
      [(``PhaseClaims.verdictPass, ``FvdepAudit.Phase.Proof.verdict_pass),
        (``PhaseClaims.verdictFailed, ``FvdepAudit.Phase.Proof.verdict_failed)]
    subject := ``FvdepCore.Phase.stepVerdict
    path := []
    noCaller := "U8"
    residue := ["lean-toolchain"]
    unproven := [] }

/-- U5 P8: the phase driver. -/
def phaseDriveRow : Row :=
  { component := `FvdepCore.Phase
    contract := "U5 P8"
    claim :=
      "`drive exec steps` runs exactly the steps up to + including the first that does not " ++
        "pass, in order, + returns it with its verdict; every step passing ⇒ all run + `none`."
    claims := [(``PhaseClaims.driveTrace, ``FvdepAudit.Phase.Proof.drive_trace)]
    subject := ``FvdepCore.Phase.drive
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U5 S2: a module's source path. -/
def phaseStemRow : Row :=
  { component := `FvdepCore.Phase
    contract := "U5 S2"
    claim :=
      "`stem` (`A.B` → `A/B`): distinct module names without `/` (U3 T3's) have distinct " ++
        "stems, so the frames of `implSources` + `proofSources` name distinct files."
    claims := [(``PhaseClaims.stemInjective, ``FvdepAudit.Phase.Proof.stem_injective)]
    subject := ``FvdepCore.Phase.stem
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U5 R8: the supervisor's reading of the step helper's frame (the encoder: `stepFrameOfRow`). -/
def stepFrameRow : Row :=
  { component := `FvdepCore.Step
    contract := "U5 R8"
    claim :=
      "The supervisor reads back exactly what the step helper framed: the status record + the " ++
        "files in path order, when the status fits J's profile, the frame lies in H2's domain " ++
        "+ every file path is safe (nonempty, `/`-separated components, each nonempty, never " ++
        "`.` or `..`, no NUL); whatever it accepts lies in that domain + is the helper's " ++
        "frame of the status + files it returns (the status entry = that status's canonical " ++
        "JSON: another spelling of the same value is refused), so it accepts exactly the " ++
        "helper's frames."
    claims :=
      [(``StepClaims.frameRead, ``FvdepAudit.Step.Proof.frame_read),
        (``StepClaims.frameExact, ``FvdepAudit.Step.Proof.frame_exact)]
    subject := ``FvdepCore.Step.read
    path := []
    noCaller := "U8"
    residue := []
    unproven := [] }

/-- U5 R8: the frame the step helper writes (`fvdep-step`'s root reaches it through its IO). -/
def stepFrameOfRow : Row :=
  { component := `FvdepCore.Step
    contract := "U5 R8"
    claim :=
      "The step helper's frame of its status + files reads back exactly (`read` returns that " ++
        "status + the files in path order) whenever the status fits J's profile, the frame " ++
        "lies in H2's domain + every file path is safe."
    claims := [(``StepClaims.frameRead, ``FvdepAudit.Step.Proof.frame_read)]
    subject := ``FvdepCore.Step.frameOf
    path := []
    noCaller := "support"
    residue := []
    unproven := [] }

/-- U5 R8: `fvdep-step`'s IO (the helper's root = `FvdepIO.Step.main`). -/
def stepExecuteRow : Row :=
  { component := `FvdepIO.Step
    contract := "U5 R8"
    claim :=
      "The step helper performs R8 on the real step: non-dumpable, descriptor 4 = the inherited " ++
        "pipe alone, `RLIMIT_CORE` = 1 + `RLIMIT_FSIZE` = the per-file cap, its child, every " ++
        "other process of the step killed (refused unless it is PID 2), the frame of its " ++
        "child's status + the regular files under `/fvdep/work/out`, its child's code."
    claims := []
    subject := ``FvdepIO.Step.execute
    path := [``FvdepIO.Step.main, ``FvdepIO.Step.execute]
    noCaller := ""
    residue := ["os", "runtime"]
    unproven := ["step-helper"] }

/-- U5 R8: `fvdep-step`'s arguments. -/
def stepPlanRow : Row :=
  { component := `FvdepIO.Step
    contract := "U5 R8"
    claim :=
      "`fvdep-step` reads `[--mkdir <dir>]… [--stdout <path>] [--file-bytes <n>] -- <argv>`, " ++
        "every path safe, `n` ≥ 1; anything else = a usage error (exit 125)."
    claims := []
    subject := ``FvdepIO.Step.plan
    path := [``FvdepIO.Step.main, ``FvdepIO.Step.plan]
    noCaller := ""
    residue := []
    unproven := ["step-helper"] }

/-- U5 R2 + R8: the spawn shim's Lean side (its externs = the `sandbox-spawn` + `step-helper`
boundaries). -/
def spawnRow : Row :=
  { component := `FvdepIO.Spawn
    contract := "U5 R2 + R8"
    claim := "The shim's errno numbers read as their names in fvdep's messages."
    claims := []
    subject := ``FvdepIO.Spawn.errnoText
    path := []
    noCaller := "support"
    residue := []
    unproven := ["sandbox-spawn"] }

/-- U5 R2–R7: the sandbox runner (`check` calls it from U8; today the dev driver's D2). -/
def runnerRow : Row :=
  { component := `FvdepIO.Sandbox
    contract := "U5 R2–R7"
    claim :=
      "One step = bwrap with `bwrapArgs`, stdout + stderr + the status descriptor + " ++
        "descriptor 4 pumped together (first + last `diagnosticBytes / 2` kept, the frame up to " ++
        "`frameBytes`), the deadline's SIGKILL + a bounded drain, then `classify` + `read` " ++
        "over what arrived."
    claims := []
    subject := ``FvdepIO.Sandbox.run
    path := []
    noCaller := "U8"
    residue := ["bwrap", "os", "runtime"]
    unproven := ["sandbox-spawn"] }

def ledger : Ledger :=
  { main := ``main
    interpreter := ``FvdepIO.execute
    plan := ``Cli.plan
    libs := [`FvdepCore, `FvdepIO]
    rows :=
      [cliRow, planRow, interpreterRow, versionRow, idsRow, evidenceRow, statusRow, jsonValueRow,
        jsonDecodeRow, jsonPrintRow, docReceiptRow, docLockRow, docEnvelopeRow, docClipRow,
        hashFrameRow, sha256DigestRow, sha256StreamRow, manifestTextRow, manifestValidateRow,
        manifestPrintRow, tomlReadRow, sysNamesRow, sysCreateRow, sysWriterRow, sysDirectoryRow,
        sysReplaceRow, sysReadRow, sysLockRow, sysNativeRow, protocolRow, protocolSigRow,
        indexDecodeRow, indexEncodeRow, registryReadRow, registryProofsRow, registryLiteralRow,
        registryCertificateRow, validateRow, closureRow, statusesRow, closureFilesRow, assembleRow,
        historyRow, indexCommandRow, indexFillerRow, sandboxArgsRow, sandboxOutcomeRow,
        buildPlanRow, buildKeyRow, buildEvictRow, buildValidateRow, phaseVerdictRow, phaseDriveRow,
        phaseStemRow, stepFrameRow, stepFrameOfRow, stepExecuteRow, stepPlanRow, spawnRow,
        runnerRow]
    residue := residue
    extraRoots :=
      [{  main := ``FvdepIO.Step.main
          interpreter := ``FvdepIO.Step.execute
          plan := ``FvdepIO.Step.plan }] }

end FvdepLedger.Rows
