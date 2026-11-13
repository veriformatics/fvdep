import FvdepCore.Evidence
import FvdepCore.Plan

/-! Policy, receipts, delivery, retraction + lock decisions (contract `docs/contracts/U2-core.md`
P1–P9; Decisions `Proof policy`, `Lifecycle`, `Data formats`; `docs/interface.md` §2–§6). Pure: the
commands that read + write `fvdep.toml`/`fvdep.lock` (U8) call these. -/

namespace FvdepCore.Status

open Ids Evidence

inductive Policy where
  | required
  | development
  deriving DecidableEq, Repr

structure Retraction where
  reason : String
  replacement : Option EntryVersion
  deriving DecidableEq, Repr

/-- P1: does a fresh result meet the saved policy? -/
def meets : Policy → Result → Option Retraction → Bool
  | _, .infra .., _ => false
  | .required, .verdict .proven _, none => true
  | .required, _, _ => false
  | .development, .verdict .proven _, _ => true
  | .development, .verdict .matched _, _ => true
  | .development, _, _ => false

theorem meets_required (r : Result) (ret : Option Retraction) :
    meets .required r ret = true ↔ (∃ rs, r = .verdict .proven rs) ∧ ret = none := by
  cases r with
  | infra c n => simp [meets]
  | verdict v rs => cases v <;> cases ret <;> simp [meets]

theorem meets_development (r : Result) (ret : Option Retraction) :
    meets .development r ret = true ↔ ∃ rs, r = .verdict .proven rs ∨ r = .verdict .matched rs := by
  cases r with
  | infra c n => simp [meets]
  | verdict v rs => cases v <;> simp [meets]

/-- `docs/interface.md` §2: 0 / 1 / 2. -/
inductive Exit where
  | ok
  | negative
  | failure
  deriving DecidableEq, Repr

def Exit.code : Exit → UInt32
  | .ok => 0
  | .negative => 1
  | .failure => 2

/-- The higher code wins (2 > 1 > 0). -/
def Exit.max : Exit → Exit → Exit
  | .failure, _ | _, .failure => .failure
  | .negative, _ | _, .negative => .negative
  | .ok, .ok => .ok

/-- P2. -/
def moduleExit (p : Policy) (r : Result) (ret : Option Retraction) : Exit :=
  match r with
  | .infra .. => .failure
  | _ => if meets p r ret then .ok else .negative

def commandExit (es : List Exit) : Exit := es.foldr Exit.max .ok

/-- P2: the numeric codes (`docs/interface.md` §2). -/
theorem exit_codes : Exit.code .ok = 0 ∧ Exit.code .negative = 1 ∧ Exit.code .failure = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- P2: a module exits 2 ⇔ its result is infrastructure. -/
theorem moduleExit_failure (p : Policy) (r : Result) (ret : Option Retraction) :
    moduleExit p r ret = .failure ↔ ∃ c ns, r = .infra c ns := by
  cases r with
  | infra c ns => simp [moduleExit]
  | verdict v rs =>
    simp only [moduleExit]
    split <;> simp

/-- P2: a module exits 0 ⇔ its result meets the policy. -/
theorem moduleExit_ok (p : Policy) (r : Result) (ret : Option Retraction) :
    moduleExit p r ret = .ok ↔ meets p r ret = true := by
  cases r with
  | infra c ns => simp [moduleExit, meets]
  | verdict v rs =>
    simp only [moduleExit]
    split <;> simp_all

theorem max_ok (a b : Exit) : Exit.max a b = .ok ↔ a = .ok ∧ b = .ok := by
  cases a <;> cases b <;> simp [Exit.max]

theorem max_failure (a b : Exit) : Exit.max a b = .failure ↔ a = .failure ∨ b = .failure := by
  cases a <;> cases b <;> simp [Exit.max]

theorem commandExit_cons (e : Exit) (es : List Exit) :
    commandExit (e :: es) = Exit.max e (commandExit es) := rfl

theorem commandExit_ok (es : List Exit) : commandExit es = .ok ↔ ∀ e ∈ es, e = .ok := by
  induction es with
  | nil => simp [commandExit]
  | cons e es ih =>
    rw [commandExit_cons, max_ok, ih]
    simp

theorem commandExit_failure (es : List Exit) : commandExit es = .failure ↔ .failure ∈ es := by
  induction es with
  | nil => simp [commandExit]
  | cons e es ih =>
    rw [commandExit_cons, max_failure, ih]
    simp [eq_comm]

/-! ## Receipts (P3) -/

/-- The fields every receipt carries (`docs/interface.md` §6 `<receipt>`). -/
structure Common where
  request : RequestKey
  library : Commit
  profile : String
  policy : Policy
  checked : String
  deriving DecidableEq

/-- A lock receipt: proof evidence (+ both exports) or differential evidence; its verdict is the
constructor's (PROVEN, MATCHED): schema 1 stores no verdict. -/
inductive Receipt where
  | proof (common : Common) (phase1 solution : Digest)
  | differential (common : Common)
  deriving DecidableEq

def Receipt.common : Receipt → Common
  | .proof c .. => c
  | .differential c => c

/-- P3: the digests + names a request of its kind carries (`docs/interface.md` §6–§7): proof =
shape, implementation + proof constants, both source digests, no adapter; differential = the
adapter digest, none of the proof fields. -/
def shaped (r : RequestKey) : Bool :=
  match r.decl.kind with
  | .proof =>
    r.decl.shape.isSome && r.decl.impl.isSome && r.decl.proof.isSome && r.implSources.isSome &&
      r.proofSources.isSome &&
      r.adapter.isNone
  | .differential =>
    r.decl.shape.isNone && r.decl.impl.isNone && r.decl.proof.isNone && r.implSources.isNone &&
      r.proofSources.isNone &&
      r.adapter.isSome

/-- The receipt of a fresh result for a well-shaped request: PROVEN (with its exports) on a proof
request → proof, MATCHED on a differential request → differential. -/
def receiptOf (c : Common) (r : Result) (exports : Option (Digest × Digest)) : Option Receipt :=
  if shaped c.request then
    match c.request.decl.kind, r, exports with
    | .proof, .verdict .proven _, some (e1, e2) => some (.proof c e1 e2)
    | .differential, .verdict .matched _, _ => some (.differential c)
    | _, _, _ => none
  else none

theorem receiptOf_proof (c : Common) (r : Result) (ex : Option (Digest × Digest)) (c' : Common)
    (e1 e2 : Digest) :
    receiptOf c r ex = some (.proof c' e1 e2) ↔
      shaped c.request = true ∧
        c.request.decl.kind = .proof ∧
        (∃ rs, r = .verdict .proven rs) ∧ ex = some (e1, e2) ∧ c' = c := by
  unfold receiptOf
  by_cases hs : shaped c.request = true
  · simp only [hs, ↓reduceIte, true_and]
    cases hk : c.request.decl.kind <;>
      cases r with
      | infra x n => simp
      | verdict v rs =>
        cases v <;> rcases ex with _ | ⟨a, b⟩ <;> simp <;>
          exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h2, h3⟩, h1.symm⟩, fun ⟨⟨h2, h3⟩, h1⟩ => ⟨h1.symm, h2, h3⟩⟩
  · simp [hs]

theorem receiptOf_differential (c : Common) (r : Result) (ex : Option (Digest × Digest))
    (c' : Common) :
    receiptOf c r ex = some (.differential c') ↔
      shaped c.request = true ∧
        c.request.decl.kind = .differential ∧ (∃ rs, r = .verdict .matched rs) ∧ c' = c := by
  unfold receiptOf
  by_cases hs : shaped c.request = true
  · simp only [hs, ↓reduceIte, true_and]
    cases hk : c.request.decl.kind <;>
      cases r with
      | infra x n => simp
      | verdict v rs => cases v <;> rcases ex with _ | ⟨a, b⟩ <;> simp <;> exact ⟨Eq.symm, Eq.symm⟩
  · simp [hs]

/-! ## Staleness (P4) -/

/-- What fvdep would check now for one manifest module. -/
structure Inputs where
  request : RequestKey
  library : Commit
  profile : String
  deriving DecidableEq

inductive Change where
  | declaration
  | specClosure
  | implSources
  | proofSources
  | adapter
  | library
  | profile
  | policy
  | exports
  deriving DecidableEq, Repr

/-- P4: the fields `status` compares, in report order (checked time + exports never). -/
def inputFields : List Change :=
  [.declaration, .specClosure, .implSources, .proofSources, .adapter, .library, .profile]

/-- P4: does field `ch` differ between a receipt + the current inputs? -/
def inputDiffers (rc : Receipt) (i : Inputs) : Change → Bool
  | .declaration => rc.common.request.decl != i.request.decl
  | .specClosure => rc.common.request.specClosure != i.request.specClosure
  | .implSources => rc.common.request.implSources != i.request.implSources
  | .proofSources => rc.common.request.proofSources != i.request.proofSources
  | .adapter => rc.common.request.adapter != i.request.adapter
  | .library => rc.common.library != i.library
  | .profile => rc.common.profile != i.profile
  | .policy | .exports => false

/-- P4: the compared fields that differ, in report order. -/
def changes (rc : Receipt) (i : Inputs) : List Change := inputFields.filter (inputDiffers rc i)

/-- P4: the changes = exactly the differing fields, in report order. -/
theorem changes_exact (rc : Receipt) (i : Inputs) :
    changes rc i = inputFields.filter (inputDiffers rc i) := rfl

theorem changes_nil (rc : Receipt) (i : Inputs) :
    changes rc i = [] ↔
      rc.common.request = i.request ∧
        rc.common.library = i.library ∧ rc.common.profile = i.profile := by
  have hreq :
    ∀ a b : RequestKey,
      a = b ↔
        a.decl = b.decl ∧
          a.specClosure = b.specClosure ∧
          a.implSources = b.implSources ∧
          a.proofSources = b.proofSources ∧ a.adapter = b.adapter := by
    intro a b
    cases a
    cases b
    simp
  simp [changes, inputFields, inputDiffers, hreq, and_assoc]

/-! ## Agreement, delivery, status (P5–P8) -/

structure Manifest where
  library : Commit
  decls : List Decl

structure Lock where
  library : Commit
  entries : List Receipt

inductive Disagreement where
  | library
  | missing (m : ModuleId)
  | duplicate (m : ModuleId)
  | declaration (m : ModuleId)
  | extra (m : ModuleId)
  deriving DecidableEq, Repr

def entriesFor (lk : Lock) (m : ModuleId) : List Receipt :=
  lk.entries.filter fun rc => rc.common.request.decl.module = m

/-- P5: how one manifest module disagrees with the lock, if it does. -/
def moduleDisagreement (lk : Lock) (d : Decl) : Option Disagreement :=
  match entriesFor lk d.module with
  | [rc] => if rc.common.request.decl = d then none else some (.declaration d.module)
  | [] => some (.missing d.module)
  | _ => some (.duplicate d.module)

/-- A lock entry for a module the manifest does not list. -/
def unlisted (mf : Manifest) (rc : Receipt) : Bool :=
  !mf.decls.any fun d => d.module = rc.common.request.decl.module

/-- P5: every way `fvdep.lock` + `fvdep.toml` disagree. -/
def agreement (mf : Manifest) (lk : Lock) : List Disagreement :=
  (if lk.library = mf.library then [] else [.library]) ++
    mf.decls.filterMap (moduleDisagreement lk) ++
    (lk.entries.filter (unlisted mf)).map fun rc => .extra rc.common.request.decl.module

theorem moduleDisagreement_some (lk : Lock) (x : Decl) (d : Disagreement) :
    moduleDisagreement lk x = some d ↔
      entriesFor lk x.module = [] ∧ d = .missing x.module ∨
        2 ≤ (entriesFor lk x.module).length ∧ d = .duplicate x.module ∨
        ∃ rc,
          entriesFor lk x.module = [rc] ∧
            rc.common.request.decl ≠ x ∧ d = .declaration x.module := by
  unfold moduleDisagreement
  cases h : entriesFor lk x.module with
  | nil => simp [eq_comm]
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases hd : a.common.request.decl = x
      · simp [hd]
      · simp only [hd, ↓reduceIte]
        constructor
        · intro h
          cases h
          exact .inr (.inr ⟨a, rfl, hd, rfl⟩)
        · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨rc, _, _, rfl⟩)
          · cases h
          · simp at h
          · rfl
    | cons b rest' => simp [eq_comm]

/-- P5: exactly the disagreements: the library pins differ; a manifest module without a lock entry,
with several, or with one for another declaration; a lock entry for a module the manifest does not
list. -/
theorem agreement_mem (mf : Manifest) (lk : Lock) (d : Disagreement) :
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
            d = .extra rc.common.request.decl.module := by
  have h1 :
    d ∈ (if lk.library = mf.library then [] else [Disagreement.library]) ↔
      d = .library ∧ lk.library ≠ mf.library := by
    split <;> simp_all
  have h3 :
    d ∈
        (lk.entries.filter (unlisted mf)).map
          (fun rc => Disagreement.extra rc.common.request.decl.module) ↔
      ∃ rc ∈ lk.entries,
        (∀ x ∈ mf.decls, x.module ≠ rc.common.request.decl.module) ∧
          d = .extra rc.common.request.decl.module := by
    simp only [List.mem_map, List.mem_filter, unlisted, Bool.not_eq_true', List.any_eq_false,
      decide_eq_true_eq]
    constructor
    · rintro ⟨rc, ⟨hrc, hall⟩, rfl⟩
      exact ⟨rc, hrc, hall, rfl⟩
    · rintro ⟨rc, hrc, hall, rfl⟩
      exact ⟨rc, ⟨hrc, hall⟩, rfl⟩
  simp only [agreement, List.mem_append, h1, h3, List.mem_filterMap, moduleDisagreement_some,
    or_assoc]

structure Notice where
  module : ModuleId
  version : EntryVersion
  reason : String
  replacement : Option EntryVersion
  deriving DecidableEq, Repr

/-- The lifecycle status snapshot (≠ the source pin; Decisions `Lifecycle`). -/
structure Snapshot where
  notices : List Notice

/-- P8: the first notice naming (id, version). -/
def retraction (s : Snapshot) (m : ModuleId) (v : EntryVersion) : Option Retraction :=
  (s.notices.find? fun n => n.module = m ∧ n.version = v).map fun n => ⟨n.reason, n.replacement⟩

/-- P8: a retraction = the first notice naming (id, version), its reason + replacement. -/
theorem retraction_some (s : Snapshot) (m : ModuleId) (v : EntryVersion) (r : Retraction) :
    retraction s m v = some r ↔
      ∃ pre n post,
        s.notices = pre ++ n :: post ∧
          (n.module = m ∧ n.version = v) ∧
          (∀ x ∈ pre, ¬(x.module = m ∧ x.version = v)) ∧ r = ⟨n.reason, n.replacement⟩ := by
  unfold retraction
  rw [Option.map_eq_some_iff]
  simp only [List.find?_eq_some_iff_append, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨n, ⟨hn, pre, post, hs, hpre⟩, rfl⟩
    exact ⟨pre, n, post, hs, hn, hpre, rfl⟩
  · rintro ⟨pre, n, post, hs, hn, hpre, rfl⟩
    exact ⟨n, ⟨hn, pre, post, hs, hpre⟩, rfl⟩

/-- P8: no notice names (id, version) ⇒ no retraction. -/
theorem retraction_none (s : Snapshot) (m : ModuleId) (v : EntryVersion) :
    retraction s m v = none ↔ ∀ n ∈ s.notices, ¬(n.module = m ∧ n.version = v) := by
  simp [retraction, List.find?_eq_none]

/-- P8: appending notices never removes a retraction. -/
theorem retraction_append (s : Snapshot) (more : List Notice) (m : ModuleId) (v : EntryVersion)
    (r : Retraction) (h : retraction s m v = some r) :
    retraction ⟨s.notices ++ more⟩ m v = some r := by
  unfold retraction at h ⊢
  cases hf : s.notices.find? (fun n => decide (n.module = m ∧ n.version = v)) with
  | none =>
    rw [hf] at h
    simp at h
  | some n =>
    rw [hf] at h
    simp only [List.find?_append, hf, Option.some_or]
    exact h

theorem retraction_listed (s : Snapshot) (n : Notice) (h : n ∈ s.notices) :
    retraction s n.module n.version ≠ none := by
  unfold retraction
  intro hr
  simp only [Option.map_eq_none_iff, List.find?_eq_none] at hr
  exact hr n h (by simp)

inductive StatusReason where
  | disagree (ds : List Disagreement)
  | noEntry
  | olderProfile
  | stale (cs : List Change)
  | testEvidenceOnly
  | retracted (r : Retraction)
  deriving DecidableEq, Repr

/-- P6: why a module is not delivered — the first that applies, in `docs/interface.md` §3's
order. -/
def statusReason (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) : Option StatusReason :=
  let m := i.request.decl.module
  if agreement mf lk ≠ [] then some (.disagree (agreement mf lk))
  else
    match (entriesFor lk m).head? with
    | none => some .noEntry
    | some rc =>
      if rc.common.profile ≠ i.profile then some .olderProfile
      else
        if changes rc i ≠ [] then some (.stale (changes rc i))
        else
          match rc with
          | .differential _ => some .testEvidenceOnly
          | .proof .. =>
            match retraction s m i.request.decl.version with
            | some r => some (.retracted r)
            | none => none

/-- P6: delivered = the files agree ∧ a proof receipt for the module ∧ no input changed ∧ not
retracted in the status snapshot. -/
def Delivered (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) : Prop :=
  agreement mf lk = [] ∧
    ∃ c e1 e2,
      (entriesFor lk i.request.decl.module).head? = some (.proof c e1 e2) ∧
        changes (.proof c e1 e2) i = [] ∧
        retraction s i.request.decl.module i.request.decl.version = none

theorem statusReason_none (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) :
    statusReason mf lk s i = none ↔ Delivered mf lk s i := by
  unfold statusReason Delivered
  by_cases ha : agreement mf lk = []
  · simp only [ha, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
    cases hh : (entriesFor lk i.request.decl.module).head? with
    | none => simp
    | some rc =>
      cases rc with
      | differential c =>
        by_cases hp : c.profile = i.profile <;> by_cases hc : changes (.differential c) i = [] <;>
          simp_all [Receipt.common]
      | proof c e1
        e2 =>
        have hcp : changes (.proof c e1 e2) i = [] → c.profile = i.profile := by
          intro h
          exact ((changes_nil _ _).mp h).2.2
        by_cases hp : c.profile = i.profile <;> by_cases hc : changes (.proof c e1 e2) i = [] <;>
          cases hr : retraction s i.request.decl.module i.request.decl.version <;>
          simp_all [Receipt.common]
        exact ⟨c, e1, e2, ⟨rfl, rfl, rfl⟩, hc⟩
  · simp [ha]

/-- P6: the status reason = the first that applies, with its payload: the disagreement; no lock
entry; an older verification profile; the changed inputs; test evidence only; the retraction. -/
theorem statusReason_some (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs)
    (r : StatusReason) :
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
                              r = .retracted rt)))) := by
  have flip : ∀ a b : StatusReason, some a = some b ↔ b = a := fun a b => by
    simp only [Option.some.injEq]
    exact eq_comm
  unfold statusReason
  by_cases ha : agreement mf lk = []
  · simp only [ha, ne_eq, not_true_eq_false, ↓reduceIte, false_and, true_and, false_or]
    cases hh : (entriesFor lk i.request.decl.module).head? with
    | none => simp [-Option.some.injEq, flip]
    | some
      rc =>
      simp only [Option.some.injEq, reduceCtorEq, false_and, exists_eq_left', false_or]
      by_cases hp : rc.common.profile = i.profile
      · by_cases hc : changes rc i = []
        · cases rc with
          | differential c => simp [-Option.some.injEq, flip, hp, hc]
          | proof c e1 e2 =>
            cases hr : retraction s i.request.decl.module i.request.decl.version with
            | none => simp [hp, hc]
            | some rt =>
              simp [-Option.some.injEq, flip, hp, hc]
              exact
                ⟨fun h => ⟨rt, rfl, h⟩, fun ⟨x, hx, h⟩ => by
                  cases hx; exact h⟩
        · simp [-Option.some.injEq, flip, hp, hc]
      · simp [-Option.some.injEq, flip, hp]
  · simp [-Option.some.injEq, flip, ha]

/-- A listed (id, version) is never delivered. -/
theorem retracted_not_delivered (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) (n : Notice)
    (hn : n ∈ s.notices) (hm : n.module = i.request.decl.module)
    (hv : n.version = i.request.decl.version) : ¬Delivered mf lk s i := by
  intro ⟨_, _, _, _, _, _, hr⟩
  have := retraction_listed s n hn
  rw [hm, hv] at this
  exact this hr

/-- P7: one module's `status` per policy: `required` ⇔ delivered; `development` ⇔ a current
receipt of any evidence (a retracted proof still meets it). -/
def statusOk (p : Policy) (mf : Manifest) (lk : Lock) (s : Snapshot) (i : Inputs) : Bool :=
  match p with
  | .required => statusReason mf lk s i == none
  | .development => (entriesFor lk i.request.decl.module).head?.any fun rc => changes rc i == []

/-- P7: exit 0 ⇔ the files agree + every module passes `statusOk` (a disagreement fails `status`
under either policy, also with no manifest module). -/
def statusExit (p : Policy) (mf : Manifest) (lk : Lock) (s : Snapshot) (is : List Inputs) : Exit :=
  if agreement mf lk == [] && is.all (statusOk p mf lk s) then .ok else .negative

theorem statusExit_ok (p : Policy) (mf : Manifest) (lk : Lock) (s : Snapshot) (is : List Inputs) :
    statusExit p mf lk s is = .ok ↔
      agreement mf lk = [] ∧ ∀ i ∈ is, statusOk p mf lk s i = true := by
  unfold statusExit
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    simp only [reduceCtorEq, false_iff]
    exact h

theorem statusExit_required (mf : Manifest) (lk : Lock) (s : Snapshot) (is : List Inputs) :
    statusExit .required mf lk s is = .ok ↔
      agreement mf lk = [] ∧ ∀ i ∈ is, Delivered mf lk s i := by
  rw [statusExit_ok]
  simp only [statusOk, beq_iff_eq]
  exact and_congr_right fun _ => forall₂_congr fun i _ => statusReason_none mf lk s i

theorem statusExit_development (mf : Manifest) (lk : Lock) (s : Snapshot) (is : List Inputs) :
    statusExit .development mf lk s is = .ok ↔
      agreement mf lk = [] ∧
        ∀ i ∈ is,
          ∃ rc, (entriesFor lk i.request.decl.module).head? = some rc ∧ changes rc i = [] := by
  rw [statusExit_ok]
  simp only [statusOk, Option.any_eq_true, beq_iff_eq]

/-! ## Lock decisions (P9) -/

inductive Decision where
  | commit
  | refuse (e : Exit)
  deriving DecidableEq, Repr

/-- P9: `check`'s exit from its fresh results alone (the lock state is no argument). -/
def checkExit (p : Policy) (rs : List (Result × Option Retraction)) : Exit :=
  commandExit (rs.map fun x => moduleExit p x.1 x.2)

/-- P2 + P9: exit 0 ⇔ every fresh result meets the policy. -/
theorem checkExit_ok (p : Policy) (rs : List (Result × Option Retraction)) :
    checkExit p rs = .ok ↔ ∀ x ∈ rs, meets p x.1 x.2 = true := by
  simp only [checkExit, commandExit_ok, List.mem_map]
  constructor
  · intro h x hx
    exact (moduleExit_ok p x.1 x.2).mp (h _ ⟨x, hx, rfl⟩)
  · rintro h e ⟨x, hx, rfl⟩
    exact (moduleExit_ok p x.1 x.2).mpr (h x hx)

/-- P2 + P9: exit 2 ⇔ some fresh result is infrastructure. -/
theorem checkExit_failure (p : Policy) (rs : List (Result × Option Retraction)) :
    checkExit p rs = .failure ↔ ∃ x ∈ rs, ∃ c ns, x.1 = .infra c ns := by
  simp only [checkExit, commandExit_failure, List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, (moduleExit_failure p x.1 x.2).mp he⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (moduleExit_failure p x.1 x.2).mpr h⟩

/-- P9: write the lock iff every module meets the policy; else refuse with `check`'s exit. -/
def lockDecision (p : Policy) (rs : List (Result × Option Retraction)) : Decision :=
  if rs.all fun x => meets p x.1 x.2 then .commit else .refuse (checkExit p rs)

theorem lockDecision_commit (p : Policy) (rs : List (Result × Option Retraction)) :
    lockDecision p rs = .commit ↔ ∀ x ∈ rs, meets p x.1 x.2 = true := by
  unfold lockDecision
  split <;> simp_all

/-- P9: a refusal ⇔ some module misses the policy; its exit = `check`'s. -/
theorem lockDecision_refuse_iff (p : Policy) (rs : List (Result × Option Retraction)) (e : Exit) :
    lockDecision p rs = .refuse e ↔ (∃ x ∈ rs, meets p x.1 x.2 = false) ∧ e = checkExit p rs := by
  unfold lockDecision
  split
  · rename_i h
    constructor
    · intro hd
      cases hd
    · rintro ⟨⟨x, hx, hm⟩, _⟩
      simp only [List.all_eq_true] at h
      have := h x hx
      simp [hm] at this
  · rename_i h
    simp only [List.all_eq_true, Classical.not_forall] at h
    obtain ⟨x, hx, hm⟩ := h
    simp only [Decision.refuse.injEq]
    constructor
    · rintro rfl
      exact ⟨⟨x, hx, by simpa using hm⟩, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl

theorem lockDecision_refuse (p : Policy) (rs : List (Result × Option Retraction)) (e : Exit)
    (h : lockDecision p rs = .refuse e) : e = .negative ∨ e = .failure := by
  obtain ⟨⟨x, hx, hm⟩, rfl⟩ := (lockDecision_refuse_iff p rs e).mp h
  have hne : checkExit p rs ≠ .ok := fun hok => by
    have := (checkExit_ok p rs).mp hok x hx
    simp [hm] at this
  cases hc : checkExit p rs <;> simp_all

inductive LockState where
  | noEntry
  | current
  | outOfDate (cs : List Change)
  deriving DecidableEq, Repr

def Receipt.inputs (rc : Receipt) : Inputs :=
  ⟨rc.common.request, rc.common.library, rc.common.profile⟩

def Receipt.exports : Receipt → Option (Digest × Digest)
  | .proof _ e1 e2 => some (e1, e2)
  | .differential _ => none

/-- P9: the fields `check` compares: P4's inputs, then the policy + the exports (`check` rebuilt
them; `status` cannot), in report order. -/
def lockFields : List Change := inputFields ++ [.policy, .exports]

/-- P9: does field `ch` differ between a lock entry + the fresh receipt? -/
def lockDiffers (rc fresh : Receipt) : Change → Bool
  | .policy => rc.common.policy != fresh.common.policy
  | .exports => rc.exports != fresh.exports
  | ch => inputDiffers rc fresh.inputs ch

/-- P9: what differs between a lock entry + the receipt `check` would write now. -/
def lockChanges (rc fresh : Receipt) : List Change := lockFields.filter (lockDiffers rc fresh)

/-- P9: the lock changes = exactly the differing fields, in report order. -/
theorem lockChanges_exact (rc fresh : Receipt) :
    lockChanges rc fresh = lockFields.filter (lockDiffers rc fresh) := rfl

theorem lockChanges_split (rc fresh : Receipt) :
    lockChanges rc fresh =
      changes rc fresh.inputs ++ [Change.policy, .exports].filter (lockDiffers rc fresh) := by
  simp only [lockChanges, lockFields, List.filter_append, changes]
  congr 1

/-- P9: the lock entry vs the fresh receipt for `check` (checked time never compared). -/
def lockState (old : Option Receipt) (fresh : Receipt) : LockState :=
  match old with
  | none => .noEntry
  | some rc => if lockChanges rc fresh = [] then .current else .outOfDate (lockChanges rc fresh)

theorem lockState_current (rc fresh : Receipt) :
    lockState (some rc) fresh = .current ↔
      changes rc fresh.inputs = [] ∧
        rc.common.policy = fresh.common.policy ∧ rc.exports = fresh.exports := by
  simp only [lockState, lockChanges_split]
  split <;> simp_all [lockDiffers]

/-- P9: an out-of-date entry always names what changed. -/
theorem lockState_outOfDate (rc fresh : Receipt) (cs : List Change) :
    lockState (some rc) fresh = .outOfDate cs ↔ cs ≠ [] ∧ cs = lockChanges rc fresh := by
  simp only [lockState]
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    intro hne heq
    exact hne (heq ▸ h)
  · rename_i h
    simp only [LockState.outOfDate.injEq]
    constructor
    · rintro rfl
      exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl

/-! ## The commit step (X2–X4) -/

/-- X2: what a commit step replaces: the lock, the manifest, either or both. -/
structure WriteSet where
  lock : Option ByteArray
  manifest : Option ByteArray

def WriteSet.bytes (ws : WriteSet) : ProjectFile → Option ByteArray
  | .lock => ws.lock
  | .manifest => ws.manifest

/-- The replaces of a write set in the canonical order: lock, then manifest. -/
def WriteSet.files (ws : WriteSet) : List (ProjectFile × ByteArray) :=
  (match ws.lock with
    | some b => [(.lock, b)]
    | none => []) ++
    match ws.manifest with
    | some b => [(.manifest, b)]
    | none => []

/-- Replace each file in order; stop at the first failure + return it. -/
def commitFiles : List (ProjectFile × ByteArray) → Plan (Option (ProjectFile × String))
  | [] => .pure none
  | (f, b) :: rest =>
    .step (.replace f b) fun
      | .replace (.ok ()) => commitFiles rest
      | .replace (.error e) => .pure (some (f, e))
      | _ => .pure (some (f, "internal: a replace got another effect's response"))

def fileName : ProjectFile → String
  | .lock => "fvdep.lock"
  | .manifest => "fvdep.toml"

/-- X3: decide first; refuse → its exit, nothing written; commit → the write set, a failure → exit 2
naming the file. -/
def authorize (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet) : Plan Exit :=
  match lockDecision p rs with
  | .refuse e => .pure e
  | .commit =>
    (commitFiles ws.files).bind fun
      | none => .pure .ok
      | some (f, e) =>
        .step
          (.err
            (s!"Could not finish writing {fileName f}: {e}. " ++
              "Run \"fvdep status\" to see the state.\n"))
          fun _ => .pure .failure

/-- Every effect of a run of `commitFiles fs` is one of its replaces, in order. -/
theorem commitFiles_prefix (fs : List (ProjectFile × ByteArray)) (evs : List (Eff × Response))
    (r : Option (Option (ProjectFile × String))) (h : Plan.Runs (commitFiles fs) evs r) :
    evs.map Prod.fst <+: fs.map fun x => Eff.replace x.1 x.2 := by
  induction fs generalizing evs with
  | nil =>
    simp only [commitFiles, Plan.runs_pure_iff] at h
    simp [h.1]
  | cons fb rest ih =>
    obtain ⟨f, b⟩ := fb
    simp only [commitFiles, Plan.runs_step_iff] at h
    rcases h with ⟨rfl, _⟩ | ⟨resp, tail, rfl, hf, hr⟩
    · simp
    · simp only [List.map_cons, List.cons_prefix_cons, true_and]
      cases resp with
      | done => simp [Fits] at hf
      | read x => simp [Fits] at hf
      | replace x =>
        cases x with
        | ok u => exact ih tail hr
        | error e =>
          simp only [Plan.runs_pure_iff] at hr
          simp [hr.1]

/-- X2: a completed `commitFiles fs` that returned no failure replaced every file, in order. -/
theorem commitFiles_ok (fs : List (ProjectFile × ByteArray)) (evs : List (Eff × Response))
    (h : Plan.Runs (commitFiles fs) evs (some none)) :
    evs = fs.map fun x => (Eff.replace x.1 x.2, Response.replace (.ok ())) := by
  induction fs generalizing evs with
  | nil =>
    simp only [commitFiles, Plan.runs_pure_iff] at h
    simp [h.1]
  | cons fb rest ih =>
    obtain ⟨f, b⟩ := fb
    simp only [commitFiles, Plan.runs_step_iff] at h
    rcases h with ⟨_, h⟩ | ⟨resp, tail, rfl, hf, hr⟩
    · cases h
    · cases resp with
      | done => simp [Fits] at hf
      | read x => simp [Fits] at hf
      | replace x =>
        cases x with
        | ok u => simp [ih tail hr]
        | error e => simp [Plan.runs_pure_iff] at hr

/-- X2: a failure ends the writes: it is the last replace, every earlier one succeeded. -/
theorem commitFiles_failed (fs : List (ProjectFile × ByteArray)) (evs : List (Eff × Response))
    (f : ProjectFile) (e : String) (h : Plan.Runs (commitFiles fs) evs (some (some (f, e)))) :
    ∃ pre b,
      evs = pre ++ [(Eff.replace f b, Response.replace (.error e))] ∧
        ∀ x ∈ pre, x.2 = Response.replace (.ok ()) := by
  induction fs generalizing evs with
  | nil => simp [commitFiles, Plan.runs_pure_iff] at h
  | cons fb rest ih =>
    obtain ⟨g, b⟩ := fb
    simp only [commitFiles, Plan.runs_step_iff] at h
    rcases h with ⟨_, h⟩ | ⟨resp, tail, rfl, hf, hr⟩
    · cases h
    · cases resp with
      | done => simp [Fits] at hf
      | read x => simp [Fits] at hf
      | replace x =>
        cases x with
        | ok u =>
          obtain ⟨pre, b', rfl, hpre⟩ := ih tail hr
          refine ⟨(Eff.replace g b, Response.replace (.ok u)) :: pre, b', rfl, ?_⟩
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · rfl
          · exact hpre y hy
        | error e' =>
          simp only [Plan.runs_pure_iff, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          exact ⟨[], b, rfl, by simp⟩

/-- X3: a refusal performs no effect at all (so writes nothing). -/
theorem authorize_refuse (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (e : Exit) (hd : lockDecision p rs = .refuse e) (evs : List (Eff × Response)) (r : Option Exit)
    (h : Plan.Runs (authorize p rs ws) evs r) : evs = [] ∧ (r = some e) := by
  simp only [authorize, hd, Plan.runs_pure_iff] at h
  exact h

/-- X3: a complete run after a commit decision: every replace succeeded + exit 0 (the write set's
files in canonical order), or the first failed replace, its diagnostic on stderr + exit 2. -/
theorem authorize_commit (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (evs : List (Eff × Response)) (x : Exit) (hd : lockDecision p rs = .commit)
    (h : Plan.Runs (authorize p rs ws) evs (some x)) :
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
            ∀ y ∈ pre, y.2 = Response.replace (.ok ()) := by
  simp only [authorize, hd] at h
  obtain ⟨e₁, e₂, a, rfl, h₁, h₂⟩ := (Plan.runs_bind_some _ _ _ _).mp h
  cases a with
  | none =>
    simp only [Plan.runs_pure_iff, Option.some.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    exact .inl ⟨rfl, by simpa using commitFiles_ok _ _ h₁⟩
  | some fe =>
    obtain ⟨f, e⟩ := fe
    obtain ⟨pre, b, rfl, hpre⟩ := commitFiles_failed _ _ _ _ h₁
    simp only [Plan.runs_step_iff] at h₂
    rcases h₂ with ⟨_, h₂⟩ | ⟨resp, tail, rfl, _, h₃⟩
    · cases h₂
    · simp only [Plan.runs_pure_iff, Option.some.injEq] at h₃
      obtain ⟨rfl, rfl⟩ := h₃
      exact .inr ⟨rfl, pre, f, b, e, resp, by simp, hpre⟩

/-- X3: with every replace succeeding, a commit decision writes the write set's files in canonical
order, then exits 0. -/
theorem authorize_commit_ok (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (hd : lockDecision p rs = .commit) :
    Plan.Runs (authorize p rs ws)
      (ws.files.map fun f => (Eff.replace f.1 f.2, Response.replace (.ok ()))) (some .ok) := by
  simp only [authorize, hd]
  have hc :
    ∀ fs : List (ProjectFile × ByteArray),
      Plan.Runs (commitFiles fs) (fs.map fun f => (Eff.replace f.1 f.2, Response.replace (.ok ())))
        (some none) := by
    intro fs
    induction fs with
    | nil => exact .done _
    | cons fb rest ih =>
      obtain ⟨f, b⟩ := fb
      exact .step _ _ _ _ _ (by simp [Fits]) ih
  exact (Plan.runs_bind_some _ _ _ _).mpr ⟨_, [], none, by simp, hc ws.files, Plan.Runs.done _⟩

/-- X3 + X4: every replace a run performs comes after a commit decision and writes the bytes the
write set assigns to that file. -/
theorem authorize_replaces (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (evs : List (Eff × Response)) (r : Option Exit) (h : Plan.Runs (authorize p rs ws) evs r)
    (f : ProjectFile) (b : ByteArray) (resp : Response) (hm : (Eff.replace f b, resp) ∈ evs) :
    lockDecision p rs = .commit ∧ ws.bytes f = some b := by
  unfold authorize at h
  cases hd : lockDecision p rs with
  | refuse e =>
    simp only [hd, Plan.runs_pure_iff] at h
    simp [h.1] at hm
  | commit =>
    refine ⟨rfl, ?_⟩
    simp only [hd] at h
    -- the replace events of the run = those of `commitFiles ws.files`
    have hpre :
      ∀ evs₁ r₁,
        Plan.Runs (commitFiles ws.files) evs₁ r₁ →
          (Eff.replace f b, resp) ∈ evs₁ → ws.bytes f = some b := by
      intro evs₁ r₁ h₁ hm₁
      have hp := commitFiles_prefix _ _ _ h₁
      obtain ⟨t, ht⟩ := hp
      have : Eff.replace f b ∈ ws.files.map fun x => Eff.replace x.1 x.2 := by
        rw [← ht]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨_, hm₁, rfl⟩)
      simp only [List.mem_map, Prod.exists] at this
      obtain ⟨g, c, hgc, he⟩ := this
      simp only [Eff.replace.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      cases g <;> cases hl : ws.lock <;> cases hn : ws.manifest <;>
        simp_all [WriteSet.files, WriteSet.bytes]
    cases r with
    | none =>
      rcases (Plan.runs_bind_none _ _ _).mp h with h₁ | ⟨e₁, e₂, a, rfl, h₁, h₂⟩
      · exact hpre _ _ h₁ hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact hpre _ _ h₁ hm
        · cases a with
          | none => simp [Plan.runs_pure_iff] at h₂
          | some fe =>
            obtain ⟨g, err⟩ := fe
            simp only [Plan.runs_step_iff] at h₂
            rcases h₂ with ⟨rfl, _⟩ | ⟨resp', tail, rfl, _, h₃⟩
            · simp at hm
            · simp only [Plan.runs_pure_iff] at h₃
              simp [h₃.1] at hm
    | some x =>
      obtain ⟨e₁, e₂, a, rfl, h₁, h₂⟩ := (Plan.runs_bind_some _ _ _ _).mp h
      rcases List.mem_append.mp hm with hm | hm
      · exact hpre _ _ h₁ hm
      · cases a with
        | none =>
          simp only [Plan.runs_pure_iff] at h₂
          simp [h₂.1] at hm
        | some fe =>
          obtain ⟨g, err⟩ := fe
          simp only [Plan.runs_step_iff] at h₂
          rcases h₂ with ⟨_, h₂⟩ | ⟨resp', tail, rfl, _, h₃⟩
          · cases h₂
          · simp only [Plan.runs_pure_iff] at h₃
            simp [h₃.1] at hm

/-- X4: what a file may hold after a run's events under the atomic-replace relation U3 implements:
a successful replace leaves the new bytes; a failed one (also one cut short by an interruption,
recorded with an error response) leaves the old or the new bytes; other effects leave it. -/
inductive Holds (f : ProjectFile) : ByteArray → List (Eff × Response) → ByteArray → Prop where
  | done (b : ByteArray) : Holds f b [] b
  |
  ok (b b' : ByteArray) (rest : List (Eff × Response)) (c : ByteArray) :
    Holds f b' rest c → Holds f b ((.replace f b', .replace (.ok ())) :: rest) c
  |
  keep (b b' : ByteArray) (e : String) (rest : List (Eff × Response)) (c : ByteArray) :
    Holds f b rest c → Holds f b ((.replace f b', .replace (.error e)) :: rest) c
  |
  land (b b' : ByteArray) (e : String) (rest : List (Eff × Response)) (c : ByteArray) :
    Holds f b' rest c → Holds f b ((.replace f b', .replace (.error e)) :: rest) c
  |
  other (b : ByteArray) (x : Eff × Response) (rest : List (Eff × Response)) (c : ByteArray) :
    (∀ b' r', x ≠ (.replace f b', r')) → Holds f b rest c → Holds f b (x :: rest) c

theorem holds_old_or_new (f : ProjectFile) (new : ByteArray) (evs : List (Eff × Response))
    (hw : ∀ b r, (Eff.replace f b, r) ∈ evs → b = new) (old c : ByteArray) (h : Holds f old evs c) :
    c = old ∨ c = new := by
  induction h with
  | done b => exact .inl rfl
  | ok b b' rest c _ ih =>
    have hb := hw b' _ (List.mem_cons_self ..)
    rcases ih (fun x r hx => hw x r (List.mem_cons_of_mem _ hx)) with h | h
    · exact .inr (h ▸ hb)
    · exact .inr h
  | keep b b' e rest c _ ih => exact ih fun x r hx => hw x r (List.mem_cons_of_mem _ hx)
  | land b b' e rest c _ ih =>
    have hb := hw b' _ (List.mem_cons_self ..)
    rcases ih (fun x r hx => hw x r (List.mem_cons_of_mem _ hx)) with h | h
    · exact .inr (h ▸ hb)
    · exact .inr h
  | other b x rest c _ _ ih => exact ih fun y r hy => hw y r (List.mem_cons_of_mem _ hy)

/-- X4: after any run of the commit step, each file holds its old bytes or the bytes the write set
assigns to it. -/
theorem authorize_old_or_new (p : Policy) (rs : List (Result × Option Retraction)) (ws : WriteSet)
    (evs : List (Eff × Response)) (r : Option Exit) (h : Plan.Runs (authorize p rs ws) evs r)
    (f : ProjectFile) (old c : ByteArray) (hh : Holds f old evs c) :
    c = old ∨ ∃ b, ws.bytes f = some b ∧ c = b := by
  cases hb : ws.bytes f with
  | none =>
    have : ∀ b r, (Eff.replace f b, r) ∈ evs → b = old := by
      intro b r hm
      have := (authorize_replaces p rs ws evs _ h f b r hm).2
      simp [hb] at this
    rcases holds_old_or_new f old evs this old c hh with h | h <;> exact .inl h
  | some
    new =>
    have : ∀ b r, (Eff.replace f b, r) ∈ evs → b = new := by
      intro b r hm
      have := (authorize_replaces p rs ws evs _ h f b r hm).2
      simp_all
    rcases holds_old_or_new f new evs this old c hh with h | h
    · exact .inl h
    · exact .inr ⟨new, rfl, h⟩

end FvdepCore.Status
