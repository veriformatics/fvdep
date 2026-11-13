import FvdepCore.Ids

/-! Evidence → result (contract `docs/contracts/U2-core.md` E1–E7; Decisions `Conformance method`,
`Verification profile`; `docs/interface.md` §4 + §6 codes): what the checking pipeline observed for
one requested module, mapped to its verdict. Producers (sandbox, phases, kernels) = U5–U7; digests
+ their codecs = U3. -/

namespace FvdepCore.Evidence

open Ids

/-- A SHA-256 digest (lowercase hex; U3 computes it). -/
abbrev Digest := String

inductive Shape where
  | fn
  | abi
  deriving DecidableEq, Repr

inductive Kind where
  | proof
  | differential
  deriving DecidableEq, Repr

/-- A manifest entry's declaration (`docs/interface.md` §7): what `fvdep.toml` states. -/
structure Decl where
  module : ModuleId
  version : EntryVersion
  shape : Option Shape
  kind : Kind
  impl : Option String
  proof : Option String
  /-- A differential entry's adapter argv (U3 D3: the receipt names what ran). -/
  adapter : Option (List String)
  deriving DecidableEq, Repr

/-- E1: what the user asked to check: the declaration + the digests of its current inputs. -/
structure RequestKey where
  decl : Decl
  specClosure : Digest
  implSources : Option Digest
  proofSources : Option Digest
  adapter : Option Digest
  deriving DecidableEq, Repr

/-- The kernels the verification profile requires: all three, each alone (Decisions `Verification
profile`; never empty by construction). -/
inductive Kernel where
  | lean
  | conLeche
  | nanoda
  deriving DecidableEq, Repr

def kernels : List Kernel := [.lean, .conLeche, .nanoda]

/-- E1: the qualified verification profile. -/
structure Profile where
  id : String
  allowedAxioms : List String
  deriving DecidableEq, Repr

/-- E1: the request + what it is judged against: the library snapshot, the verification profile
(its allowlist judges the axioms: the profile a result uses is the challenge's by construction) +
the statement. -/
structure ChallengeKey where
  request : RequestKey
  library : Commit
  profile : Profile
  statement : Digest
  deriving DecidableEq

inductive Refusal where
  | profileConstruct
  | importNotAllowed
  | reservedModule
  deriving DecidableEq, Repr

inductive KernelStatus where
  | accept
  | reject
  | crash
  | timeout (seconds : Nat)
  | decline (detail : String)
  deriving DecidableEq, Repr

inductive Infra where
  | sandboxSetup
  | toolMissing
  | adapter
  | fetchFailed
  | io
  deriving DecidableEq, Repr

inductive Comparison where
  | matched
  | mismatch (got want : String)
  | unsupported
  deriving DecidableEq, Repr

/-- A phase build: its export digest, or the failure. -/
inductive Built where
  | ok (digest : Digest)
  | failed (detail : String)
  deriving DecidableEq, Repr

/-- E2: one observation, with the phase outputs it judged (`e1` = phase-1 export, `e2` = solution
export). -/
inductive Obs where
  | implProfile (refusal : Option (Refusal × String))
  | phase1 (result : Built)
  | phase2 (e1 : Digest) (result : Built)
  | statement (e1 e2 : Digest) (matched : Bool)
  | graph (e1 e2 : Digest) (matched : Bool)
  | axioms (e2 : Digest) (names : List String)
  | kernel (e2 : Digest) (k : Kernel) (status : KernelStatus)
  | infra (code : Infra) (detail : String)
  | compare (adapter : Digest) (op input : String) (result : Comparison)
  deriving DecidableEq

structure Observation where
  key : ChallengeKey
  obs : Obs
  deriving DecidableEq

/-- `docs/interface.md` §6 codes (E5a). -/
inductive Code where
  | profileConstruct
  | importNotAllowed
  | reservedModule
  | buildFailed
  | statementMismatch
  | graphMismatch
  | axiom
  | kernelReject
  | kernelCrash
  | kernelTimeout
  | kernelDecline
  | sandboxSetup
  | toolMissing
  | adapter
  | fetchFailed
  | io
  | internal
  | mismatch
  deriving DecidableEq, Repr

structure Reason where
  code : Code
  detail : String
  deriving DecidableEq, Repr

inductive Verdict where
  | proven
  | notProven
  | matched
  | mismatch
  deriving DecidableEq, Repr

/-- E4: an infrastructure cause (exit 2; negative findings seen so far kept), or a verdict with its
reasons. -/
inductive Result where
  | infra (cause : Reason) (negatives : List Reason)
  | verdict (v : Verdict) (reasons : List Reason)
  deriving DecidableEq, Repr

/-! ## Attribution -/

/-- The observations under the request's challenge key. -/
def keyed (c : ChallengeKey) (os : List Observation) : List Obs :=
  (os.filter fun o => o.key == c).map (·.obs)

/-- None, one value (identical duplicates count once), or a conflict. -/
inductive One (α : Type) where
  | none
  | one (a : α)
  | conflict

def one {α : Type} [DecidableEq α] : List α → One α
  | [] => .none
  | a :: rest => if rest.all (· == a) then .one a else .conflict

def implProfiles : List Obs → List (Option (Refusal × String)) :=
  List.filterMap fun
    | .implProfile r => some r
    | _ => none

def phase1s :
    List Obs → List Built := List.filterMap fun
    | .phase1 r => some r
    | _ => none

def phase2s (e1 : Digest) : List Obs → List Built :=
  List.filterMap fun
    | .phase2 x r => if x = e1 then some r else none
    | _ => none

def statements (e1 e2 : Digest) : List Obs → List Bool :=
  List.filterMap fun
    | .statement x y m => if x = e1 ∧ y = e2 then some m else none
    | _ => none

def graphs (e1 e2 : Digest) : List Obs → List Bool :=
  List.filterMap fun
    | .graph x y m => if x = e1 ∧ y = e2 then some m else none
    | _ => none

def axiomLists (e2 : Digest) : List Obs → List (List String) :=
  List.filterMap fun
    | .axioms x n => if x = e2 then some n else none
    | _ => none

def kernelStatuses (e2 : Digest) (k : Kernel) : List Obs → List KernelStatus :=
  List.filterMap fun
    | .kernel x j s => if x = e2 ∧ j = k then some s else none
    | _ => none

def infras : List Obs → List (Infra × String) :=
  List.filterMap fun
    | .infra c d => some (c, d)
    | _ => none

/-- The phase outputs the evidence attributes: phase 1's single export, then phase 2's single
export on it (none where that phase has no single successful build). -/
def bindings (ks : List Obs) : Option Digest × Option Digest :=
  match one (phase1s ks) with
  | .one (.ok e1) =>
    match one (phase2s e1 ks) with
    | .one (.ok e2) => (some e1, some e2)
    | _ => (some e1, none)
  | _ => (none, none)

/-- E3: an observation's export binding names the attributed phase outputs (observations of the
implementation profile + phase 1, infrastructure + comparisons carry none). -/
def bound (b : Option Digest × Option Digest) : Obs → Bool
  | .phase2 x _ => some x == b.1
  | .statement x y _ | .graph x y _ => some x == b.1 && some y == b.2
  | .axioms y _ | .kernel y _ _ => some y == b.2
  | _ => true

/-- E3: the observations that count: under the request's challenge key, bound to the attributed
phase outputs (after a failed phase 1 or 2 no later observation is bound: no export to bind). -/
def attributed (c : ChallengeKey) (os : List Observation) : List Observation :=
  let b := bindings (keyed c os)
  os.filter fun o => o.key == c && bound b o.obs

/-- The attributed observations' contents. -/
def attributedObs (c : ChallengeKey) (os : List Observation) : List Obs :=
  (keyed c os).filter (bound (bindings (keyed c os)))

/-- The phase (0–6) an observation belongs to; infrastructure + comparisons have none. -/
def phaseOf : Obs → Option Nat
  | .implProfile _ => some 0
  | .phase1 _ => some 1
  | .phase2 .. => some 2
  | .statement .. => some 3
  | .graph .. => some 4
  | .axioms .. => some 5
  | .kernel .. => some 6
  | .infra .. | .compare .. => none

/-- Some observation belongs to a phase after `n` (a protocol violation once phase `n` failed). -/
def after (n : Nat) (ks : List Obs) : Bool := ks.any fun o => (phaseOf o).any (· > n)

/-! ## The proof rule (E5) -/

def refusalCode : Refusal → Code
  | .profileConstruct => .profileConstruct
  | .importNotAllowed => .importNotAllowed
  | .reservedModule => .reservedModule

def kernelName : Kernel → String
  | .lean => "lean"
  | .conLeche => "con-leche"
  | .nanoda => "nanoda"

/-- A non-accepting kernel's reason (`kernel_decline` never reported as `kernel_reject`). -/
def kernelReason (k : Kernel) : KernelStatus → Option Reason
  | .accept => none
  | .reject => some ⟨.kernelReject, s!"kernel {kernelName k} rejected the proof"⟩
  | .crash => some ⟨.kernelCrash, s!"kernel {kernelName k} crashed"⟩
  | .timeout s => some ⟨.kernelTimeout, s!"kernel {kernelName k} timed out after {s} s"⟩
  | .decline d => some ⟨.kernelDecline, s!"kernel {kernelName k} declined: {d}"⟩

def infraCode : Infra → Code
  | .sandboxSetup => .sandboxSetup
  | .toolMissing => .toolMissing
  | .adapter => .adapter
  | .fetchFailed => .fetchFailed
  | .io => .io

/-- The phase walk: every phase passed, the first failed phase (its reasons), a phase missing with
no earlier failure, or a protocol violation; the last two keep the negatives already seen. -/
inductive Walk where
  | passed
  | failed (reasons : List Reason)
  | missing (phase : String) (negatives : List Reason)
  | protocol (detail : String) (negatives : List Reason)
  deriving DecidableEq, Repr

/-- A failed phase `n`: its reasons, unless a later phase was observed anyway. -/
def fail (n : Nat) (ks : List Obs) (rs : List Reason) : Walk :=
  if after n ks then .protocol s!"an observation after failed phase {n}" rs else .failed rs

/-- A kernel's reason when it reported one non-accepting status. -/
def kernelSeen (k : Kernel) : One KernelStatus → Option Reason
  | .one s => kernelReason k s
  | _ => none

/-- The kernel phase from each required kernel's single status (`kernels`): every non-accepting one
listed, beside a conflict or a missing kernel too. -/
def kernelWalk (a b c : One KernelStatus) : Walk :=
  let seen := [kernelSeen .lean a, kernelSeen .conLeche b, kernelSeen .nanoda c].filterMap id
  match a, b, c with
  | .one _, .one _, .one _ => if seen.isEmpty then .passed else .failed seen
  | .conflict, _, _ | _, .conflict, _ | _, _, .conflict =>
    .protocol "conflicting kernel results" seen
  | _, _, _ => .missing "kernel" seen

def kernelPhase (e2 : Digest) (ks : List Obs) : Walk :=
  kernelWalk (one (kernelStatuses e2 .lean ks)) (one (kernelStatuses e2 .conLeche ks))
    (one (kernelStatuses e2 .nanoda ks))

def walk (allowed : List String) (ks : List Obs) : Walk :=
  match one (implProfiles ks) with
  | .conflict => .protocol "conflicting implementation profile results" []
  | .none => .missing "implementation profile" []
  | .one (some (r, d)) => fail 0 ks [⟨refusalCode r, d⟩]
  | .one none =>
    match one (phase1s ks) with
    | .conflict => .protocol "conflicting phase 1 results" []
    | .none => .missing "phase 1" []
    | .one (.failed d) => fail 1 ks [⟨.buildFailed, d⟩]
    | .one (.ok e1) =>
      match one (phase2s e1 ks) with
      | .conflict => .protocol "conflicting phase 2 results" []
      | .none => .missing "phase 2" []
      | .one (.failed d) => fail 2 ks [⟨.buildFailed, d⟩]
      | .one (.ok e2) =>
        match one (statements e1 e2 ks) with
        | .conflict => .protocol "conflicting statement results" []
        | .none => .missing "statement" []
        | .one false =>
          fail 3 ks [⟨.statementMismatch, "the proof does not prove the required statement"⟩]
        | .one true =>
          match one (graphs e1 e2 ks) with
          | .conflict => .protocol "conflicting graph results" []
          | .none => .missing "graph" []
          | .one false => fail 4 ks [⟨.graphMismatch, "the implementation changed between phases"⟩]
          | .one true =>
            match one (axiomLists e2 ks) with
            | .conflict => .protocol "conflicting axiom results" []
            | .none => .missing "axioms" []
            | .one names =>
              let bad := names.filter fun a => !allowed.contains a
              if bad.isEmpty then kernelPhase e2 ks
              else fail 5 ks (bad.map fun a => ⟨.axiom, s!"the proof depends on axiom {a}"⟩)

def negatives : Walk → List Reason
  | .passed => []
  | .failed rs | .missing _ rs | .protocol _ rs => rs

/-- E5 for a proof request, over its attributed observations. -/
def proofResult (allowed : List String) (ks : List Obs) : Result :=
  let w := walk allowed ks
  match infras ks with
  | (c, d) :: _ => .infra ⟨infraCode c, d⟩ (negatives w)
  | [] =>
    match w with
    | .passed => .verdict .proven []
    | .failed rs => .verdict .notProven rs
    | .missing ph ns => .infra ⟨.internal, s!"missing {ph} result"⟩ ns
    | .protocol d ns => .infra ⟨.internal, d⟩ ns

/-! ## The differential rule (E7) -/

/-- One step of `dedup`: keep `x` unless already kept. -/
def keepNew {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if acc.contains x then acc else acc ++ [x]

/-- Identical duplicates count once (E3): the first occurrence of each, in order. -/
def dedup {α : Type} [DecidableEq α] (xs : List α) : List α := xs.foldl keepNew []

/-- A comparison under the request's adapter. -/
def compareOf (adapter : Option Digest) : Obs → Option (String × String × Comparison)
  | .compare a op i r => if some a = adapter then some (op, i, r) else none
  | _ => none

def comparisons (adapter : Option Digest) (ks : List Obs) : List (String × String × Comparison) :=
  dedup (ks.filterMap (compareOf adapter))

def mismatchReason : String × String × Comparison → Option Reason
  | (op, i, .mismatch got want) =>
    some ⟨.mismatch, s!"{op}: input {i}: implementation {got}, spec {want}"⟩
  | _ => none

def supported (cs : List (String × String × Comparison)) : List (String × String × Comparison) :=
  cs.filter fun (_, _, r) => !(r matches .unsupported)

def diffResult (adapter : Option Digest) (ks : List Obs) : Result :=
  let sup := supported (comparisons adapter ks)
  let bad := sup.filterMap mismatchReason
  match infras ks with
  | (c, d) :: _ => .infra ⟨infraCode c, d⟩ bad
  | [] =>
    if sup.isEmpty then .infra ⟨.adapter, "no supported comparison"⟩ []
    else if bad.isEmpty then .verdict .matched [] else .verdict .mismatch bad

/-- E5 + E7: a request's result from its attributed observations alone. -/
def result (c : ChallengeKey) (os : List Observation) : Result :=
  match c.request.decl.kind with
  | .proof => proofResult c.profile.allowedAxioms (attributedObs c os)
  | .differential => diffResult c.request.adapter (attributedObs c os)

/-! ## Theorems -/

theorem one_eq_one {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    one xs = .one a ↔ a ∈ xs ∧ ∀ x ∈ xs, x = a := by
  cases xs with
  | nil => simp [one]
  | cons y rest =>
    simp only [one]
    split
    · rename_i h
      simp only [List.all_eq_true, beq_iff_eq] at h
      constructor
      · intro he
        cases he
        refine ⟨List.mem_cons_self .., fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact h x hx
      · rintro ⟨_, hall⟩
        rw [hall y (List.mem_cons_self ..)]
    · rename_i h
      simp only [List.all_eq_true, beq_iff_eq, Classical.not_forall] at h
      obtain ⟨x, hx, hne⟩ := h
      constructor
      · intro he
        cases he
      · rintro ⟨_, hall⟩
        exact
          absurd ((hall x (List.mem_cons_of_mem _ hx)).trans (hall y (List.mem_cons_self ..)).symm)
            hne

theorem one_mem {α : Type} [DecidableEq α] {xs : List α} {a : α} (h : one xs = .one a) :
    a ∈ xs := ((one_eq_one xs a).mp h).1

theorem one_all {α : Type} [DecidableEq α] {xs : List α} {a : α} (h : one xs = .one a) :
    ∀ x ∈ xs, x = a := ((one_eq_one xs a).mp h).2

/-- `one` over a filterMap: one value present, every value it yields equal to it. -/
theorem one_filterMap {β : Type} [DecidableEq β] (f : Obs → Option β) (ks : List Obs) (v : β)
    (hin : ∃ o ∈ ks, f o = some v) (hall : ∀ o ∈ ks, ∀ w, f o = some w → w = v) :
    one (ks.filterMap f) = .one v := by
  rw [one_eq_one]
  refine ⟨List.mem_filterMap.mpr hin, fun w hw => ?_⟩
  obtain ⟨o, ho, hf⟩ := List.mem_filterMap.mp hw
  exact hall o ho w hf

/-- A filter that keeps every element a filterMap reads leaves the filterMap unchanged. -/
theorem filterMap_filter_eq {β : Type} (f : Obs → Option β) (p : Obs → Bool) (ks : List Obs)
    (h : ∀ o ∈ ks, (f o).isSome → p o = true) : (ks.filter p).filterMap f = ks.filterMap f := by
  induction ks with
  | nil => rfl
  | cons o rest ih =>
    have hr := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hp : p o = true
    · simp [hp, List.filterMap_cons, hr]
    · have hn : f o = none := by
        cases hf : f o with
        | none => rfl
        | some y => exact absurd (h o (List.mem_cons_self ..) (by simp [hf])) hp
      simp [hp, hn, hr]

theorem phase1s_filter (ks : List Obs) (b : Option Digest × Option Digest) :
    phase1s (ks.filter (bound b)) = phase1s ks := by
  simp only [phase1s]
  apply filterMap_filter_eq
  intro o _ hs
  cases o <;> simp_all [bound]

theorem phase2s_filter (ks : List Obs) (b : Option Digest × Option Digest) (e1 : Digest)
    (hb1 : b.1 = some e1) : phase2s e1 (ks.filter (bound b)) = phase2s e1 ks := by
  simp only [phase2s]
  apply filterMap_filter_eq
  intro o _ hs
  cases o <;> simp_all [bound]

theorem bindings_fst (ks : List Obs) (e1 : Digest) (h1 : one (phase1s ks) = .one (.ok e1)) :
    (bindings ks).1 = some e1 := by
  simp only [bindings, h1]
  split <;> rfl

theorem bindings_eq (ks : List Obs) (e1 e2 : Digest) (h1 : one (phase1s ks) = .one (.ok e1))
    (h2 : one (phase2s e1 ks) = .one (.ok e2)) : bindings ks = (some e1, some e2) := by
  simp [bindings, h1, h2]

/-- Attribution keeps the bindings it filtered by. -/
theorem bindings_filter (ks : List Obs) (b : Option Digest × Option Digest) (hb : bindings ks = b) :
    bindings (ks.filter (bound b)) = bindings ks := by
  simp only [bindings, phase1s_filter]
  cases h : one (phase1s ks) with
  | none => rfl
  | conflict => rfl
  | one r =>
    cases r with
    | failed d => rfl
    | ok e1 =>
      have hb1 : b.1 = some e1 := hb ▸ bindings_fst ks e1 h
      simp only [phase2s_filter ks b e1 hb1]

theorem infras_filter (ks : List Obs) (b : Option Digest × Option Digest) :
    infras (ks.filter (bound b)) = infras ks := by
  simp only [infras]
  apply filterMap_filter_eq
  intro o _ hs
  cases o <;> simp_all [bound]

theorem keyed_attributed (c : ChallengeKey) (os : List Observation) :
    keyed c (attributed c os) = attributedObs c os := by
  simp only [keyed, attributed, attributedObs, List.filter_filter, List.filter_map,
    Function.comp_def]
  congr 1
  apply List.filter_congr
  intro x _
  cases x.key == c <;> simp

/-- E3: the result depends on the attributed observations alone. -/
theorem result_attributed (c : ChallengeKey) (os : List Observation) :
    result c (attributed c os) = result c os := by
  have h : attributedObs c (attributed c os) = attributedObs c os := by
    have hk := keyed_attributed c os
    simp only [attributedObs] at hk ⊢
    rw [hk, bindings_filter _ _ rfl, List.filter_filter]
    simp
  simp only [result, h]

/-- E3: observations under another key never change a result. -/
theorem result_keyed (c : ChallengeKey) (os : List Observation) :
    result c os = result c (os.filter fun o => o.key == c) := by
  simp [result, attributedObs, keyed, List.filter_filter]

theorem kernelReason_none (k : Kernel) (st : KernelStatus) :
    kernelReason k st = none ↔ st = .accept := by cases st <;> simp [kernelReason]

/-- `kernel_decline` + `kernel_reject` stay apart: each code names its own status. -/
theorem kernelReason_code (k : Kernel) (st : KernelStatus) :
    ((kernelReason k st).map (·.code) = some .kernelReject ↔ st = .reject) ∧
      ((kernelReason k st).map (·.code) = some .kernelDecline ↔ ∃ d, st = .decline d) := by
  cases st <;> simp [kernelReason]

theorem kernelWalk_passed (a b c : One KernelStatus) (h : kernelWalk a b c = .passed) :
    a = .one .accept ∧ b = .one .accept ∧ c = .one .accept := by
  rcases a with _ | x | _ <;> rcases b with _ | y | _ <;> rcases c with _ | z | _ <;>
    simp [kernelWalk] at h
  cases x <;> cases y <;> cases z <;> simp_all [kernelSeen, kernelReason]

theorem fail_ne_passed (n : Nat) (ks : List Obs) (rs : List Reason) : fail n ks rs ≠ .passed := by
  unfold fail
  split <;> simp

/-- Every phase passed ⇒ each phase's single response is the passing one. -/
theorem walk_passed {allowed : List String} {ks : List Obs} (h : walk allowed ks = .passed) :
    ∃ e1 e2 names,
      one (implProfiles ks) = .one none ∧
        one (phase1s ks) = .one (.ok e1) ∧
        one (phase2s e1 ks) = .one (.ok e2) ∧
        one (statements e1 e2 ks) = .one true ∧
        one (graphs e1 e2 ks) = .one true ∧
        one (axiomLists e2 ks) = .one names ∧
        (∀ a ∈ names, a ∈ allowed) ∧
        one (kernelStatuses e2 .lean ks) = .one .accept ∧
        one (kernelStatuses e2 .conLeche ks) = .one .accept ∧
        one (kernelStatuses e2 .nanoda ks) = .one .accept := by
  unfold walk at h
  cases hi : one (implProfiles ks) with
  | conflict => simp [hi] at h
  | none => simp [hi] at h
  | one r =>
    cases r with
    | some rd =>
      simp only [hi] at h
      exact absurd h (fail_ne_passed _ _ _)
    | none =>
      cases h1 : one (phase1s ks) with
      | conflict => simp [hi, h1] at h
      | none => simp [hi, h1] at h
      | one b1 =>
        cases b1 with
        | failed d =>
          simp only [hi, h1] at h
          exact absurd h (fail_ne_passed _ _ _)
        | ok e1 =>
          cases h2 : one (phase2s e1 ks) with
          | conflict => simp [hi, h1, h2] at h
          | none => simp [hi, h1, h2] at h
          | one b2 =>
            cases b2 with
            | failed d =>
              simp only [hi, h1, h2] at h
              exact absurd h (fail_ne_passed _ _ _)
            | ok e2 =>
              cases hs : one (statements e1 e2 ks) with
              | conflict => simp [hi, h1, h2, hs] at h
              | none => simp [hi, h1, h2, hs] at h
              | one m =>
                cases m with
                | false =>
                  simp only [hi, h1, h2, hs] at h
                  exact absurd h (fail_ne_passed _ _ _)
                | true =>
                  cases hg : one (graphs e1 e2 ks) with
                  | conflict => simp [hi, h1, h2, hs, hg] at h
                  | none => simp [hi, h1, h2, hs, hg] at h
                  | one g =>
                    cases g with
                    | false =>
                      simp only [hi, h1, h2, hs, hg] at h
                      exact absurd h (fail_ne_passed _ _ _)
                    | true =>
                      cases ha : one (axiomLists e2 ks) with
                      | conflict => simp [hi, h1, h2, hs, hg, ha] at h
                      | none => simp [hi, h1, h2, hs, hg, ha] at h
                      | one names =>
                        simp only [hi, h1, h2, hs, hg, ha] at h
                        split at h
                        · rename_i hbad
                          obtain ⟨hl, hc, hn⟩ := kernelWalk_passed _ _ _ h
                          refine ⟨e1, e2, names, rfl, rfl, h2, hs, hg, ha, ?_, hl, hc, hn⟩
                          intro a ha'
                          simp only [List.isEmpty_iff, List.filter_eq_nil_iff] at hbad
                          simpa using hbad a ha'
                        · exact absurd h (fail_ne_passed _ _ _)

/-- E7: MATCHED ⇔ no infrastructure failure, ≥ 1 supported comparison, all of them matched. -/
theorem diff_matched (adapter : Option Digest) (ks : List Obs) :
    diffResult adapter ks = .verdict .matched [] ↔
      infras ks = [] ∧
        supported (comparisons adapter ks) ≠ [] ∧
        (supported (comparisons adapter ks)).filterMap mismatchReason = [] := by
  simp only [diffResult]
  generalize supported (comparisons adapter ks) = sup
  cases infras ks with
  | cons x rest => simp
  | nil =>
    cases sup with
    | nil => simp
    | cons y ys => cases (y :: ys).filterMap mismatchReason <;> simp

/-- E7: MISMATCH ⇔ no infrastructure failure + a supported comparison that differs. -/
theorem diff_mismatch (adapter : Option Digest) (ks : List Obs) :
    (∃ rs, diffResult adapter ks = .verdict .mismatch rs) ↔
      infras ks = [] ∧ (supported (comparisons adapter ks)).filterMap mismatchReason ≠ [] := by
  simp only [diffResult]
  generalize supported (comparisons adapter ks) = sup
  cases infras ks with
  | cons x rest => simp
  | nil =>
    cases sup with
    | nil => simp
    | cons y ys => cases (y :: ys).filterMap mismatchReason <;> simp

/-- E7: differential evidence is never PROVEN. -/
theorem diff_not_proven (adapter : Option Digest) (ks : List Obs) (rs : List Reason) :
    diffResult adapter ks ≠ .verdict .proven rs := by
  simp only [diffResult]
  generalize supported (comparisons adapter ks) = sup
  cases infras ks with
  | cons x rest => simp
  | nil =>
    cases sup with
    | nil => simp
    | cons y ys => cases (y :: ys).filterMap mismatchReason <;> simp

theorem proofResult_proven (allowed : List String) (ks : List Obs) :
    proofResult allowed ks = .verdict .proven [] ↔ infras ks = [] ∧ walk allowed ks = .passed := by
  simp only [proofResult]
  cases infras ks with
  | cons x rest => simp
  | nil => cases walk allowed ks <;> simp

theorem obs_of_one {β : Type} [DecidableEq β] {f : Obs → Option β} {ks : List Obs} {v : β}
    (h : one (ks.filterMap f) = .one v) : ∃ o ∈ ks, f o = some v :=
  List.mem_filterMap.mp (one_mem h)

theorem all_of_one {β : Type} [DecidableEq β] {f : Obs → Option β} {ks : List Obs} {v : β}
    (h : one (ks.filterMap f) = .one v) : ∀ o ∈ ks, ∀ w, f o = some w → w = v := fun _ ho w hw =>
  one_all h w (List.mem_filterMap.mpr ⟨_, ho, hw⟩)

/-- E6: the observations of a proof that passed every phase on exports `e1`, `e2`. -/
def passing (e1 e2 : Digest) (names : List String) : List Obs :=
  [.implProfile none, .phase1 (.ok e1), .phase2 e1 (.ok e2), .statement e1 e2 true,
    .graph e1 e2 true, .axioms e2 names, .kernel e2 .lean .accept, .kernel e2 .conLeche .accept,
    .kernel e2 .nanoda .accept]

/-- An observation a proof judged on (`e1`, `e2`) never reads: bound to other exports, or a
comparison (E3, E7). -/
def Elsewhere (e1 e2 : Digest) : Obs → Prop
  | .phase2 x _ => ¬x = e1
  | .statement x y _ | .graph x y _ => ¬(x = e1 ∧ y = e2)
  | .axioms y _ | .kernel y _ _ => ¬y = e2
  | .compare .. => True
  | _ => False

/-- Every phase's single response passing ⇒ each passing observation is present. -/
theorem passing_mem {ks : List Obs} {e1 e2 : Digest} {names : List String}
    (hi : one (implProfiles ks) = .one none) (h1 : one (phase1s ks) = .one (.ok e1))
    (h2 : one (phase2s e1 ks) = .one (.ok e2)) (hs : one (statements e1 e2 ks) = .one true)
    (hg : one (graphs e1 e2 ks) = .one true) (ha : one (axiomLists e2 ks) = .one names)
    (hkl : one (kernelStatuses e2 .lean ks) = .one .accept)
    (hkc : one (kernelStatuses e2 .conLeche ks) = .one .accept)
    (hkn : one (kernelStatuses e2 .nanoda ks) = .one .accept) :
    ∀ o ∈ passing e1 e2 names, o ∈ ks := by
  intro o ho
  simp only [passing, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨x, hx, hf⟩ := obs_of_one hi
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one h1
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one h2
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one hs
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one hg
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one ha
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one hkl
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one hkc
    cases x <;> simp_all
  · obtain ⟨x, hx, hf⟩ := obs_of_one hkn
    cases x <;> simp_all

/-- Every phase's single response passing, no infrastructure failure ⇒ each observation bound to
(`e1`, `e2`) is a passing one or a comparison. -/
theorem walk_class {ks : List Obs} {e1 e2 : Digest} {names : List String}
    (hi : one (implProfiles ks) = .one none) (h1 : one (phase1s ks) = .one (.ok e1))
    (h2 : one (phase2s e1 ks) = .one (.ok e2)) (hs : one (statements e1 e2 ks) = .one true)
    (hg : one (graphs e1 e2 ks) = .one true) (ha : one (axiomLists e2 ks) = .one names)
    (hkl : one (kernelStatuses e2 .lean ks) = .one .accept)
    (hkc : one (kernelStatuses e2 .conLeche ks) = .one .accept)
    (hkn : one (kernelStatuses e2 .nanoda ks) = .one .accept) (hinf : infras ks = []) :
    ∀ o ∈ ks,
      bound (some e1, some e2) o = true →
        o ∈ passing e1 e2 names ∨ ∃ a op i r, o = .compare a op i r := by
  intro o ho hb
  cases o with
  | implProfile r =>
    have := all_of_one hi _ ho r rfl
    simp [passing, this]
  | phase1 r =>
    have := all_of_one h1 _ ho r rfl
    simp [passing, this]
  | phase2 x r =>
    simp only [bound, beq_iff_eq, Option.some.injEq] at hb
    subst hb
    have := all_of_one h2 _ ho r (by simp)
    simp [passing, this]
  | statement x y
    m =>
    simp only [bound, Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := all_of_one hs _ ho m (by simp)
    simp [passing, this]
  | graph x y m =>
    simp only [bound, Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := all_of_one hg _ ho m (by simp)
    simp [passing, this]
  | axioms y n =>
    simp only [bound, beq_iff_eq, Option.some.injEq] at hb
    subst hb
    have := all_of_one ha _ ho n (by simp)
    simp [passing, this]
  | kernel y k st =>
    simp only [bound, beq_iff_eq, Option.some.injEq] at hb
    subst hb
    cases k
    · have := all_of_one hkl _ ho st (by simp)
      simp [passing, this]
    · have := all_of_one hkc _ ho st (by simp)
      simp [passing, this]
    · have := all_of_one hkn _ ho st (by simp)
      simp [passing, this]
  | infra code d =>
    simp only [infras, List.filterMap_eq_nil_iff] at hinf
    exact absurd (hinf _ ho) (by simp)
  | compare a op i r => exact .inr ⟨a, op, i, r, rfl⟩

/-- Evidence holding a passing proof's observations, nothing else but identical duplicates,
observations bound elsewhere + comparisons ⇒ each phase's single response is the passing one + no
infrastructure failure. -/
theorem passing_ones {ks : List Obs} {e1 e2 : Digest} {names : List String}
    (hpres : ∀ o ∈ passing e1 e2 names, o ∈ ks)
    (hall : ∀ o ∈ ks, o ∈ passing e1 e2 names ∨ Elsewhere e1 e2 o) :
    one (implProfiles ks) = .one none ∧
      one (phase1s ks) = .one (.ok e1) ∧
      one (phase2s e1 ks) = .one (.ok e2) ∧
      one (statements e1 e2 ks) = .one true ∧
      one (graphs e1 e2 ks) = .one true ∧
      one (axiomLists e2 ks) = .one names ∧
      one (kernelStatuses e2 .lean ks) = .one .accept ∧
      one (kernelStatuses e2 .conLeche ks) = .one .accept ∧
      one (kernelStatuses e2 .nanoda ks) = .one .accept ∧ infras ks = [] := by
  have inP : ∀ o, o ∈ passing e1 e2 names → o ∈ ks := hpres
  have cls :
    ∀ o ∈ ks,
      o = .implProfile none ∨
        o = .phase1 (.ok e1) ∨
        o = .phase2 e1 (.ok e2) ∨
        o = .statement e1 e2 true ∨
        o = .graph e1 e2 true ∨
        o = .axioms e2 names ∨
        o = .kernel e2 .lean .accept ∨
        o = .kernel e2 .conLeche .accept ∨ o = .kernel e2 .nanoda .accept ∨ Elsewhere e1 e2 o := by
    intro o ho
    rcases hall o ho with hp | he
    · simp only [passing, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h | h | h | h | h | h | h | h <;> simp [h]
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr he))))))))
  refine
    ⟨one_filterMap _ _ _ ⟨.implProfile none, inP _ (by simp [passing]), rfl⟩ ?_,
      one_filterMap _ _ _ ⟨.phase1 (.ok e1), inP _ (by simp [passing]), rfl⟩ ?_,
      one_filterMap _ _ _ ⟨.phase2 e1 (.ok e2), inP _ (by simp [passing]), by simp⟩ ?_,
      one_filterMap _ _ _ ⟨.statement e1 e2 true, inP _ (by simp [passing]), by simp⟩ ?_,
      one_filterMap _ _ _ ⟨.graph e1 e2 true, inP _ (by simp [passing]), by simp⟩ ?_,
      one_filterMap _ _ _ ⟨.axioms e2 names, inP _ (by simp [passing]), by simp⟩ ?_,
      one_filterMap _ _ _ ⟨.kernel e2 .lean .accept, inP _ (by simp [passing]), by simp⟩ ?_,
      one_filterMap _ _ _ ⟨.kernel e2 .conLeche .accept, inP _ (by simp [passing]), by simp⟩ ?_,
      one_filterMap _ _ _ ⟨.kernel e2 .nanoda .accept, inP _ (by simp [passing]), by simp⟩ ?_, ?_⟩
  all_goals
    first
    | ( intro o ho w hw
        rcases cls o ho with h | h | h | h | h | h | h | h | h | h
        all_goals
          first
          | (subst h; simp_all)
          | (cases o <;> simp_all [Elsewhere]))
    | ( simp only [infras, List.filterMap_eq_nil_iff]
        intro o ho
        rcases cls o ho with h | h | h | h | h | h | h | h | h | h
        all_goals
          first
          | (subst h; rfl)
          | (cases o <;> simp_all [Elsewhere]))

/-- E6: PROVEN ⇔ a proof request whose observations under its key hold every observation of a
passing proof on some exports (`e1`, `e2`), with axioms inside the profile's allowlist, and nothing
else but identical duplicates, observations bound to other exports + comparisons. -/
theorem proven_iff (c : ChallengeKey) (os : List Observation) :
    result c os = .verdict .proven [] ↔
      c.request.decl.kind = .proof ∧
        ∃ e1 e2 names,
          (∀ a ∈ names, a ∈ c.profile.allowedAxioms) ∧
            (∀ o ∈ passing e1 e2 names, o ∈ keyed c os) ∧
            ∀ o ∈ keyed c os, o ∈ passing e1 e2 names ∨ Elsewhere e1 e2 o := by
  constructor
  · intro h
    have hk : c.request.decl.kind = .proof := by
      unfold result at h
      revert h
      cases c.request.decl.kind with
      | proof => exact fun _ => rfl
      | differential => exact fun h => absurd h (diff_not_proven _ _ _)
    refine ⟨hk, ?_⟩
    unfold result at h
    rw [hk] at h
    obtain ⟨hinf, hw⟩ := (proofResult_proven _ _).mp h
    obtain ⟨e1, e2, names, hi, h1, h2, hs, hg, ha, hal, hkl, hkc, hkn⟩ := walk_passed hw
    have h1K : one (phase1s (keyed c os)) = .one (.ok e1) := by
      simp only [attributedObs, phase1s_filter] at h1
      exact h1
    have h2K : one (phase2s e1 (keyed c os)) = .one (.ok e2) := by
      simp only [attributedObs, phase2s_filter _ _ e1 (bindings_fst _ e1 h1K)] at h2
      exact h2
    have hb := bindings_eq _ _ _ h1K h2K
    refine ⟨e1, e2, names, hal, fun o ho => ?_, fun o ho => ?_⟩
    · exact (List.mem_filter.mp (passing_mem hi h1 h2 hs hg ha hkl hkc hkn o ho)).1
    · by_cases hbo : bound (some e1, some e2) o = true
      · have hoA : o ∈ attributedObs c os := by
          simp only [attributedObs, hb, List.mem_filter]
          exact ⟨ho, hbo⟩
        rcases walk_class hi h1 h2 hs hg ha hkl hkc hkn hinf o hoA hbo with hp | ⟨a, op, i, r, rfl⟩
        · exact .inl hp
        · exact .inr trivial
      · right
        cases o <;> simp_all [bound, Elsewhere]
  · rintro ⟨hk, e1, e2, names, hal, hpres, hall⟩
    obtain ⟨-, h1K, h2K, -⟩ := passing_ones hpres hall
    have hb := bindings_eq _ _ _ h1K h2K
    have hpresA : ∀ o ∈ passing e1 e2 names, o ∈ attributedObs c os := by
      intro o ho
      simp only [attributedObs, hb, List.mem_filter]
      refine ⟨hpres o ho, ?_⟩
      simp only [passing, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bound]
    have hallA : ∀ o ∈ attributedObs c os, o ∈ passing e1 e2 names ∨ Elsewhere e1 e2 o :=
      fun o ho => hall o (List.mem_filter.mp ho).1
    obtain ⟨hi, h1, h2, hs, hg, ha, hkl, hkc, hkn, hinf⟩ := passing_ones hpresA hallA
    unfold result
    rw [hk]
    refine (proofResult_proven _ _).mpr ⟨hinf, ?_⟩
    simp [walk, hi, h1, h2, hs, hg, ha, kernelPhase, hkl, hkc, hkn, kernelWalk, kernelSeen,
      kernelReason]
    exact fun x hx hn => absurd (hal x hx) hn

/-- The honest evidence for a proof request: every phase passed under its key. -/
def honest (c : ChallengeKey) (e1 e2 : Digest) (names : List String) : List Observation :=
  (passing e1 e2 names).map fun o => ⟨c, o⟩

/-- E6: an attributed infrastructure observation ⇒ an infrastructure result (exit 2), whatever else
was observed. -/
theorem infra_result (c : ChallengeKey) (os : List Observation) (h : infras (keyed c os) ≠ []) :
    ∃ cause negs, result c os = .infra cause negs := by
  have hi : infras (attributedObs c os) = infras (keyed c os) := infras_filter _ _
  unfold result
  cases hk : infras (keyed c os) with
  | nil => exact absurd hk h
  | cons x rest =>
    rw [← hi] at hk
    cases c.request.decl.kind <;> simp [proofResult, diffResult, hk]

/-- E7: an attributed infrastructure observation ⇒ infrastructure with its code; the mismatches seen
kept. -/
theorem diff_infra (adapter : Option Digest) (ks : List Obs) (code : Infra) (d : String)
    (rest : List (Infra × String)) (h : infras ks = (code, d) :: rest) :
    diffResult adapter ks =
      .infra ⟨infraCode code, d⟩
        ((supported (comparisons adapter ks)).filterMap mismatchReason) := by
  simp [diffResult, h]

/-- E7: no supported comparison ⇒ infrastructure `adapter`. -/
theorem diff_unsupported (adapter : Option Digest) (ks : List Obs) (h : infras ks = [])
    (hs : supported (comparisons adapter ks) = []) :
    diffResult adapter ks = .infra ⟨.adapter, "no supported comparison"⟩ [] := by
  simp [diffResult, h, hs]

/-- E7: a proof request never reads comparisons. -/
theorem proof_ignores_compare (allowed : List String) (a : Digest) (op i : String) (r : Comparison)
    (ks : List Obs) : proofResult allowed (.compare a op i r :: ks) = proofResult allowed ks := by
  simp [proofResult, walk, fail, after, kernelPhase, infras, implProfiles, phase1s, phase2s,
    statements, graphs, axiomLists, kernelStatuses, phaseOf]

/-! ## E5 as phase facts -/

/-- A phase's attributed responses: one value (identical duplicates allowed), none, or two different
ones. -/
def Responds {β : Type} (xs : List β) : One β → Prop
  | .one a => a ∈ xs ∧ ∀ x ∈ xs, x = a
  | .none => xs = []
  | .conflict => ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y

/-- E5a: the implementation profile's response judged (`none` = passed). -/
def judgeProfile : Option (Refusal × String) → Option (List Reason)
  | none => none
  | some (r, d) => some [⟨refusalCode r, d⟩]

/-- E5a: a phase build judged. -/
def judgeBuild : Built → Option (List Reason)
  | .ok _ => none
  | .failed d => some [⟨.buildFailed, d⟩]

/-- E5a: the statement check judged. -/
def judgeStatement : Bool → Option (List Reason)
  | true => none
  | false => some [⟨.statementMismatch, "the proof does not prove the required statement"⟩]

/-- E5a: the graph check judged. -/
def judgeGraph : Bool → Option (List Reason)
  | true => none
  | false => some [⟨.graphMismatch, "the implementation changed between phases"⟩]

/-- E5a: the axiom audit judged: each axiom outside the allowlist named. -/
def judgeAxioms (allowed names : List String) : Option (List Reason) :=
  let bad := names.filter fun a => !allowed.contains a
  if bad.isEmpty then none else some (bad.map fun a => ⟨.axiom, s!"the proof depends on axiom {a}"⟩)

/-- An observation of a phase after `n` is present. -/
def Later (ks : List Obs) (n : Nat) : Prop := ∃ o ∈ ks, ∃ i, phaseOf o = some i ∧ n < i

/-- E5 (2): phase `n` (responses `xs`) stops the walk at `w`: two different responses → protocol;
none → missing; one failing response → its reasons, a protocol violation (reasons kept) when a
later phase was observed anyway. -/
def Stops {β : Type} (ks : List Obs) (xs : List β) (judge : β → Option (List Reason)) (n : Nat)
    (w : Walk) : Prop :=
  (Responds xs .conflict ∧ ∃ d, w = .protocol d []) ∨
    (Responds xs .none ∧ ∃ ph, w = .missing ph []) ∨
    ∃ a rs,
      Responds xs (.one a) ∧
        judge a = some rs ∧ (Later ks n ∧ (∃ d, w = .protocol d rs) ∨ ¬Later ks n ∧ w = .failed rs)

/-- Phase responses `xs` pass on `a`. -/
def Passes {β : Type} (xs : List β) (judge : β → Option (List Reason)) (a : β) : Prop :=
  Responds xs (.one a) ∧ judge a = none

/-- E5a: kernel `k`'s single answer judged: accept passes; reject, crash, timeout + decline each
name their own code + the kernel (`kernel_decline` never reported as `kernel_reject`). -/
def judgeKernel (k : Kernel) : KernelStatus → Option (List Reason)
  | .accept => none
  | .reject => some [⟨.kernelReject, s!"kernel {kernelName k} rejected the proof"⟩]
  | .crash => some [⟨.kernelCrash, s!"kernel {kernelName k} crashed"⟩]
  | .timeout s => some [⟨.kernelTimeout, s!"kernel {kernelName k} timed out after {s} s"⟩]
  | .decline d => some [⟨.kernelDecline, s!"kernel {kernelName k} declined: {d}"⟩]

/-- Kernel `k`'s negatives: one non-accepting answer → its judged reasons; accept, silence or two
different answers → none. -/
def kernelNegatives (k : Kernel) : One KernelStatus → List Reason
  | .one s => (judgeKernel k s).getD []
  | _ => []

/-- E5 (2), kernel step, over the required kernels' answers `a b c` (Lean, con-leche, NanoDa): a
kernel with two different answers → protocol; else a silent kernel → missing `kernel`; else all
accept → passed, any other answer → failed. Every outcome lists each kernel that answered once
without accepting, in kernel order. -/
def KernelSpec (a b c : One KernelStatus) (w : Walk) : Prop :=
  let ns := kernelNegatives .lean a ++ kernelNegatives .conLeche b ++ kernelNegatives .nanoda c
  (a = .conflict ∨ b = .conflict ∨ c = .conflict) ∧ (∃ d, w = .protocol d ns) ∨
    a ≠ .conflict ∧
      b ≠ .conflict ∧
      c ≠ .conflict ∧ (a = .none ∨ b = .none ∨ c = .none) ∧ w = .missing "kernel" ns ∨
    ∃ x y z,
      a = .one x ∧
        b = .one y ∧
        c = .one z ∧
        (x = .accept ∧ y = .accept ∧ z = .accept ∧ w = .passed ∨
          ¬(x = .accept ∧ y = .accept ∧ z = .accept) ∧ w = .failed ns)

/-- E5 (2) over evidence `ks`: the phases in order — implementation profile, phase 1, phase 2 (on
phase 1's export), statement, graph, axioms (on both exports) — the first one not passing stops the
walk; once all pass, the kernel step (`KernelSpec`) over each required kernel's responses. -/
def Spec (allowed : List String) (ks : List Obs) (w : Walk) : Prop :=
  Stops ks (implProfiles ks) judgeProfile 0 w ∨
    Passes (implProfiles ks) judgeProfile none ∧
      (Stops ks (phase1s ks) judgeBuild 1 w ∨
        ∃ e1,
          Passes (phase1s ks) judgeBuild (.ok e1) ∧
            (Stops ks (phase2s e1 ks) judgeBuild 2 w ∨
              ∃ e2,
                Passes (phase2s e1 ks) judgeBuild (.ok e2) ∧
                  (Stops ks (statements e1 e2 ks) judgeStatement 3 w ∨
                    Passes (statements e1 e2 ks) judgeStatement true ∧
                      (Stops ks (graphs e1 e2 ks) judgeGraph 4 w ∨
                        Passes (graphs e1 e2 ks) judgeGraph true ∧
                          (Stops ks (axiomLists e2 ks) (judgeAxioms allowed) 5 w ∨
                            ∃ names a b c,
                              Passes (axiomLists e2 ks) (judgeAxioms allowed) names ∧
                                Responds (kernelStatuses e2 .lean ks) a ∧
                                Responds (kernelStatuses e2 .conLeche ks) b ∧
                                Responds (kernelStatuses e2 .nanoda ks) c ∧ KernelSpec a b c w)))))

theorem responds_one {β : Type} [DecidableEq β] (xs : List β) : Responds xs (one xs) := by
  cases h : one xs with
  | one a => exact (one_eq_one xs a).mp h
  | none =>
    cases xs with
    | nil => rfl
    | cons y rest =>
      simp only [one] at h
      split at h <;> cases h
  | conflict =>
    cases xs with
    | nil => simp [one] at h
    | cons y rest =>
      simp only [one] at h
      split at h
      · cases h
      · rename_i hn
        simp only [List.all_eq_true, beq_iff_eq, Classical.not_forall] at hn
        obtain ⟨x, hx, hne⟩ := hn
        exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_self .., hne⟩

theorem later_iff (ks : List Obs) (n : Nat) : Later ks n ↔ after n ks = true := by
  simp only [Later, after, List.any_eq_true]
  constructor
  · rintro ⟨o, ho, i, hi, hn⟩
    exact ⟨o, ho, by simp [hi, hn]⟩
  · rintro ⟨o, ho, h⟩
    cases hp : phaseOf o with
    | none => simp [hp] at h
    | some i =>
      simp only [hp, Option.any_some, decide_eq_true_eq] at h
      exact ⟨o, ho, i, hp, h⟩

theorem conflict_stops {β : Type} [DecidableEq β] (ks : List Obs) (xs : List β)
    (judge : β → Option (List Reason)) (n : Nat) (d : String) (h : one xs = .conflict) :
    Stops ks xs judge n (.protocol d []) := .inl ⟨h ▸ responds_one xs, d, rfl⟩

theorem none_stops {β : Type} [DecidableEq β] (ks : List Obs) (xs : List β)
    (judge : β → Option (List Reason)) (n : Nat) (ph : String) (h : one xs = .none) :
    Stops ks xs judge n (.missing ph []) := .inr (.inl ⟨h ▸ responds_one xs, ph, rfl⟩)

theorem fail_stops {β : Type} [DecidableEq β] (ks : List Obs) (xs : List β)
    (judge : β → Option (List Reason)) (n : Nat) (a : β) (rs : List Reason) (h : one xs = .one a)
    (hj : judge a = some rs) : Stops ks xs judge n (fail n ks rs) := by
  refine .inr (.inr ⟨a, rs, (one_eq_one xs a).mp h, hj, ?_⟩)
  by_cases hl : after n ks = true
  · exact
      .inl ⟨(later_iff ks n).mpr hl, s!"an observation after failed phase {n}", by simp [fail, hl]⟩
  · exact .inr ⟨fun h => hl ((later_iff ks n).mp h), by simp [fail, hl]⟩

theorem passes_of {β : Type} [DecidableEq β] (xs : List β) (judge : β → Option (List Reason))
    (a : β) (h : one xs = .one a) (hj : judge a = none) : Passes xs judge a :=
  ⟨(one_eq_one xs a).mp h, hj⟩

theorem kernelSeen_list (k : Kernel) (x : One KernelStatus) :
    (kernelSeen k x).toList = kernelNegatives k x := by
  cases x with
  | none => rfl
  | one s => cases s <;> rfl
  | conflict => rfl

theorem kernelWalk_seen (a b c : One KernelStatus) :
    [kernelSeen .lean a, kernelSeen .conLeche b, kernelSeen .nanoda c].filterMap id =
      kernelNegatives .lean a ++ kernelNegatives .conLeche b ++ kernelNegatives .nanoda c := by
  rw [← kernelSeen_list .lean a, ← kernelSeen_list .conLeche b, ← kernelSeen_list .nanoda c]
  cases kernelSeen .lean a <;> cases kernelSeen .conLeche b <;> cases kernelSeen .nanoda c <;> rfl

theorem kernelNegatives_nil (k : Kernel) (s : KernelStatus) :
    kernelNegatives k (.one s) = [] ↔ s = .accept := by
  cases s <;> simp [kernelNegatives, judgeKernel]

/-- E5: the kernel step obeys `KernelSpec`. -/
theorem kernelWalk_spec (a b c : One KernelStatus) : KernelSpec a b c (kernelWalk a b c) := by
  unfold kernelWalk
  rw [kernelWalk_seen]
  unfold KernelSpec
  rcases a with _ | x | _ <;> rcases b with _ | y | _ <;> rcases c with _ | z | _ <;> simp
  simp only [kernelNegatives_nil]
  by_cases h : x = .accept ∧ y = .accept ∧ z = .accept
  · exact .inl ⟨h.1, h.2.1, h.2.2, h.1, h.2.1, h.2.2⟩
  · exact .inr ⟨fun hx hy hz => h ⟨hx, hy, hz⟩, fun hx hy hz => h ⟨hx, hy, hz⟩⟩

/-- E5: the walk obeys `Spec`. -/
theorem walk_spec (allowed : List String) (ks : List Obs) : Spec allowed ks (walk allowed ks) := by
  unfold Spec walk
  cases hi : one (implProfiles ks) with
  | conflict =>
    dsimp only
    exact .inl (conflict_stops _ _ _ _ _ hi)
  | none =>
    dsimp only
    exact .inl (none_stops _ _ _ _ _ hi)
  | one r =>
    cases r with
    | some rd =>
      obtain ⟨r, d⟩ := rd
      dsimp only
      exact .inl (fail_stops _ _ _ _ _ _ hi rfl)
    | none =>
      dsimp only
      refine .inr ⟨passes_of _ _ _ hi rfl, ?_⟩
      cases h1 : one (phase1s ks) with
      | conflict =>
        dsimp only
        exact .inl (conflict_stops _ _ _ _ _ h1)
      | none =>
        dsimp only
        exact .inl (none_stops _ _ _ _ _ h1)
      | one b1 =>
        cases b1 with
        | failed d =>
          dsimp only
          exact .inl (fail_stops _ _ _ _ _ _ h1 rfl)
        | ok e1 =>
          dsimp only
          refine .inr ⟨e1, passes_of _ _ _ h1 rfl, ?_⟩
          cases h2 : one (phase2s e1 ks) with
          | conflict =>
            dsimp only
            exact .inl (conflict_stops _ _ _ _ _ h2)
          | none =>
            dsimp only
            exact .inl (none_stops _ _ _ _ _ h2)
          | one b2 =>
            cases b2 with
            | failed d =>
              dsimp only
              exact .inl (fail_stops _ _ _ _ _ _ h2 rfl)
            | ok e2 =>
              dsimp only
              refine .inr ⟨e2, passes_of _ _ _ h2 rfl, ?_⟩
              cases hs : one (statements e1 e2 ks) with
              | conflict =>
                dsimp only
                exact .inl (conflict_stops _ _ _ _ _ hs)
              | none =>
                dsimp only
                exact .inl (none_stops _ _ _ _ _ hs)
              | one m =>
                cases m with
                | false =>
                  dsimp only
                  exact .inl (fail_stops _ _ _ _ _ _ hs rfl)
                | true =>
                  dsimp only
                  refine .inr ⟨passes_of _ _ _ hs rfl, ?_⟩
                  cases hg : one (graphs e1 e2 ks) with
                  | conflict =>
                    dsimp only
                    exact .inl (conflict_stops _ _ _ _ _ hg)
                  | none =>
                    dsimp only
                    exact .inl (none_stops _ _ _ _ _ hg)
                  | one g =>
                    cases g with
                    | false =>
                      dsimp only
                      exact .inl (fail_stops _ _ _ _ _ _ hg rfl)
                    | true =>
                      dsimp only
                      refine .inr ⟨passes_of _ _ _ hg rfl, ?_⟩
                      cases ha : one (axiomLists e2 ks) with
                      | conflict =>
                        dsimp only
                        exact .inl (conflict_stops _ _ _ _ _ ha)
                      | none =>
                        dsimp only
                        exact .inl (none_stops _ _ _ _ _ ha)
                      | one names =>
                        dsimp only
                        by_cases hb : ∀ a ∈ names, a ∈ allowed
                        · have hif :
                            (names.filter fun a => !allowed.contains a).isEmpty = true := by
                            simpa using hb
                          refine
                            .inr
                              ⟨names, _, _, _,
                                passes_of _ _ _ ha (by simp only [judgeAxioms, hif, ↓reduceIte]),
                                responds_one _, responds_one _, responds_one _, ?_⟩
                          simp only [hif, ↓reduceIte, kernelPhase]
                          exact kernelWalk_spec _ _ _
                        · have hif :
                            (names.filter fun a => !allowed.contains a).isEmpty = false := by
                            simpa using hb
                          have hj :
                            judgeAxioms allowed names =
                              some
                                ((names.filter fun a => !allowed.contains a).map fun a =>
                                  ⟨.axiom, s!"the proof depends on axiom {a}"⟩) := by
                            simp only [judgeAxioms, hif, Bool.false_eq_true, ↓reduceIte]
                          simp only [hif, Bool.false_eq_true, ↓reduceIte]
                          exact .inl (fail_stops _ _ _ _ _ _ ha hj)

/-- E5: a proof request's result: the first attributed infrastructure observation's code beside the
walk's negatives, else PROVEN, NOT PROVEN with the failed phase's reasons, or infrastructure
`internal` for a missing phase or a protocol violation (negatives kept); the walk obeys `Spec`. -/
theorem result_spec (c : ChallengeKey) (os : List Observation) (hk : c.request.decl.kind = .proof) :
    ∃ w,
      Spec c.profile.allowedAxioms (attributedObs c os) w ∧
        (∀ code d rest,
          infras (attributedObs c os) = (code, d) :: rest →
            result c os = .infra ⟨infraCode code, d⟩ (negatives w)) ∧
        (infras (attributedObs c os) = [] →
          (w = .passed → result c os = .verdict .proven []) ∧
            (∀ rs, w = .failed rs → result c os = .verdict .notProven rs) ∧
            (∀ ph ns, w = .missing ph ns → ∃ d, result c os = .infra ⟨.internal, d⟩ ns) ∧
            ∀ d ns, w = .protocol d ns → result c os = .infra ⟨.internal, d⟩ ns) := by
  refine ⟨walk c.profile.allowedAxioms (attributedObs c os), walk_spec _ _, ?_, ?_⟩
  · intro code d rest h
    simp [result, hk, proofResult, h]
  · intro h
    refine
        ⟨fun hw => ?_, fun rs hw => ?_, fun ph ns hw => ⟨s!"missing {ph} result", ?_⟩,
          fun d ns hw => ?_⟩ <;>
      simp [result, hk, proofResult, h, hw]

/-! ## E4: reasons ↔ verdict -/

theorem stops_failed {β : Type} {ks : List Obs} {xs : List β} {judge : β → Option (List Reason)}
    {n : Nat} {rs : List Reason} (h : Stops ks xs judge n (.failed rs))
    (hj : ∀ a rs, judge a = some rs → rs ≠ []) : rs ≠ [] := by
  rcases h with ⟨_, d, h⟩ | ⟨_, ph, h⟩ | ⟨a, rs', _, hja, ⟨_, d, h⟩ | ⟨_, h⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
    exact hj a _ hja

theorem kernelSpec_failed {a b c : One KernelStatus} {rs : List Reason}
    (h : KernelSpec a b c (.failed rs)) : rs ≠ [] := by
  dsimp only [KernelSpec] at h
  rcases h with ⟨_, d, h⟩ | ⟨_, _, _, _, h⟩ | ⟨x, y, z, rfl, rfl, rfl, ⟨_, _, _, h⟩ | ⟨hn, h⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
    simpa [kernelNegatives_nil] using hn

theorem judgeAxioms_ne (allowed names : List String) (rs : List Reason)
    (h : judgeAxioms allowed names = some rs) : rs ≠ [] := by
  simp only [judgeAxioms] at h
  split at h
  · cases h
  · rename_i hb
    cases h
    simpa using hb

/-- A failed walk names at least one reason. -/
theorem spec_failed {allowed : List String} {ks : List Obs} {rs : List Reason}
    (h : Spec allowed ks (.failed rs)) : rs ≠ [] := by
  have jp : ∀ a rs, judgeProfile a = some rs → rs ≠ [] := by
    intro a rs h
    cases a with
    | none => cases h
    | some rd =>
      cases h
      simp
  have jb : ∀ a rs, judgeBuild a = some rs → rs ≠ [] := by
    intro a rs h
    cases a <;> cases h
    simp
  have js : ∀ a rs, judgeStatement a = some rs → rs ≠ [] := by
    intro a rs h
    cases a <;> cases h
    simp
  have jg : ∀ a rs, judgeGraph a = some rs → rs ≠ [] := by
    intro a rs h
    cases a <;> cases h
    simp
  rcases h with h |
    ⟨_, h | ⟨e1, _, h | ⟨e2, _, h | ⟨_, h | ⟨_, h | ⟨names, a, b, c, _, _, _, _, hw⟩⟩⟩⟩⟩⟩
  · exact stops_failed h jp
  · exact stops_failed h jb
  · exact stops_failed h jb
  · exact stops_failed h js
  · exact stops_failed h jg
  · exact stops_failed h (judgeAxioms_ne allowed)
  · exact kernelSpec_failed hw

/-- E4: a verdict names reasons ⇔ it is NOT PROVEN or MISMATCH. -/
theorem result_reasons (c : ChallengeKey) (os : List Observation) (v : Verdict) (rs : List Reason)
    (h : result c os = .verdict v rs) : rs ≠ [] ↔ v = .notProven ∨ v = .mismatch := by
  unfold result at h
  cases hk : c.request.decl.kind with
  | proof =>
    simp only [hk, proofResult] at h
    split at h
    · cases h
    · rename_i hw
      cases hw' : walk c.profile.allowedAxioms (attributedObs c os) <;> simp only [hw'] at h <;>
        cases h
      · simp
      · rename_i rs'
        have := spec_failed (hw' ▸ walk_spec c.profile.allowedAxioms (attributedObs c os))
        simp [this]
  | differential =>
    simp only [hk, diffResult] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          simp
        · rename_i hb
          cases h
          simpa using hb

/-! ## E3: identical duplicates -/

theorem one_append_mem {β : Type} [DecidableEq β] (xs : List β) (y : β) (hy : y ∈ xs) :
    one (xs ++ [y]) = one xs := by
  cases xs with
  | nil => simp at hy
  | cons a
    rest =>
    simp only [List.cons_append, one, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    by_cases h : rest.all (· == a) = true
    · have hya : (y == a) = true := by
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · simp only [List.all_eq_true] at h
          exact h y hy
      simp [h, hya]
    · simp [h]

theorem one_filterMap_append {β : Type} [DecidableEq β] (f : Obs → Option β) (ks : List Obs)
    (x : Obs) (hx : x ∈ ks) : one ((ks ++ [x]).filterMap f) = one (ks.filterMap f) := by
  rw [List.filterMap_append]
  cases hf : f x with
  | none => simp [hf]
  | some y =>
    simp only [List.filterMap_cons, hf, List.filterMap_nil]
    exact one_append_mem _ _ (List.mem_filterMap.mpr ⟨x, hx, hf⟩)

theorem after_append (n : Nat) (ks : List Obs) (x : Obs) (hx : x ∈ ks) :
    after n (ks ++ [x]) = after n ks := by
  simp only [after, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  cases h : (phaseOf x).any (· > n)
  · simp
  · have : (ks.any fun o => (phaseOf o).any (· > n)) = true := List.any_eq_true.mpr ⟨x, hx, h⟩
    simp [this]

theorem walk_append (allowed : List String) (ks : List Obs) (x : Obs) (hx : x ∈ ks) :
    walk allowed (ks ++ [x]) = walk allowed ks := by
  simp only [walk, fail, kernelPhase, implProfiles, phase1s, phase2s, statements, graphs,
    axiomLists, kernelStatuses, one_filterMap_append _ _ _ hx, after_append _ _ _ hx]

theorem infras_append (ks : List Obs) (x : Obs) (hx : x ∈ ks) :
    (infras (ks ++ [x])).head? = (infras ks).head? := by
  simp only [infras, List.filterMap_append]
  cases h :
    ks.filterMap fun o =>
      match o with
      | .infra c d => some (c, d)
      | _ => none with
  | cons y t => simp
  | nil =>
    have hn := List.filterMap_eq_nil_iff.mp h x hx
    simp [hn]

theorem proofResult_append (allowed : List String) (ks : List Obs) (x : Obs) (hx : x ∈ ks) :
    proofResult allowed (ks ++ [x]) = proofResult allowed ks := by
  have hi := infras_append ks x hx
  simp only [proofResult, walk_append _ _ _ hx]
  cases h : infras ks with
  | nil =>
    rw [h] at hi
    cases h' : infras (ks ++ [x]) with
    | nil => rfl
    | cons y t => simp [h'] at hi
  | cons y t =>
    rw [h] at hi
    cases h' : infras (ks ++ [x]) with
    | nil => simp [h'] at hi
    | cons y' t' =>
      simp only [h', List.head?_cons, Option.some.injEq] at hi
      subst hi
      rfl

theorem mem_foldl_keepNew {α : Type} [DecidableEq α] (xs acc : List α) (y : α) :
    y ∈ xs.foldl keepNew acc ↔ y ∈ acc ∨ y ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, keepNew, List.mem_cons]
    split
    · rename_i h
      have : a ∈ acc := by simpa using h
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl this
        · exact .inr h
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | rfl) | h)
        · exact .inl h
        · exact .inr (.inl rfl)
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inl h)
        · exact .inl (.inr rfl)
        · exact .inr h

theorem dedup_append_mem {α : Type} [DecidableEq α] (xs : List α) (y : α) (hy : y ∈ xs) :
    dedup (xs ++ [y]) = dedup xs := by
  have hm : y ∈ xs.foldl keepNew [] := (mem_foldl_keepNew xs [] y).mpr (.inr hy)
  simp only [dedup, List.foldl_append, List.foldl_cons, List.foldl_nil, keepNew]
  simp [hm]

theorem comparisons_append (adapter : Option Digest) (ks : List Obs) (x : Obs) (hx : x ∈ ks) :
    comparisons adapter (ks ++ [x]) = comparisons adapter ks := by
  simp only [comparisons, List.filterMap_append]
  cases hf : compareOf adapter x with
  | none => simp [hf]
  | some y =>
    simp only [List.filterMap_cons, hf, List.filterMap_nil]
    exact dedup_append_mem _ _ (List.mem_filterMap.mpr ⟨x, hx, hf⟩)

theorem diffResult_append (adapter : Option Digest) (ks : List Obs) (x : Obs) (hx : x ∈ ks) :
    diffResult adapter (ks ++ [x]) = diffResult adapter ks := by
  have hi := infras_append ks x hx
  simp only [diffResult, comparisons_append _ _ _ hx]
  cases h : infras ks with
  | nil =>
    rw [h] at hi
    cases h' : infras (ks ++ [x]) with
    | nil => rfl
    | cons y t => simp [h'] at hi
  | cons y t =>
    rw [h] at hi
    cases h' : infras (ks ++ [x]) with
    | nil => simp [h'] at hi
    | cons y' t' =>
      simp only [h', List.head?_cons, Option.some.injEq] at hi
      subst hi
      rfl

/-- E3: an identical duplicate of an observation counts once. -/
theorem result_dup (c : ChallengeKey) (os : List Observation) (o : Observation) (ho : o ∈ os) :
    result c (os ++ [o]) = result c os := by
  by_cases hc : (o.key == c) = true
  · have hmem : o.obs ∈ keyed c os := List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, hc⟩, rfl⟩
    have hK : keyed c (os ++ [o]) = keyed c os ++ [o.obs] := by simp [keyed, List.filter_append, hc]
    have hb : bindings (keyed c os ++ [o.obs]) = bindings (keyed c os) := by
      simp only [bindings, phase1s, phase2s, one_filterMap_append _ _ _ hmem]
    have hA :
      attributedObs c (os ++ [o]) =
        attributedObs c os ++ [o.obs].filter (bound (bindings (keyed c os))) := by
      simp only [attributedObs, hK, hb, List.filter_append]
    by_cases hbo : bound (bindings (keyed c os)) o.obs = true
    · have hmA : o.obs ∈ attributedObs c os := List.mem_filter.mpr ⟨hmem, hbo⟩
      have hA' : attributedObs c (os ++ [o]) = attributedObs c os ++ [o.obs] := by
        rw [hA]
        simp [hbo]
      unfold result
      rw [hA']
      cases c.request.decl.kind
      · exact proofResult_append _ _ _ hmA
      · exact diffResult_append _ _ _ hmA
    · have hA' : attributedObs c (os ++ [o]) = attributedObs c os := by
        rw [hA]
        simp [hbo]
      simp only [result, hA']
  · have hK : keyed c (os ++ [o]) = keyed c os := by simp [keyed, List.filter_append, hc]
    simp only [result, attributedObs, hK]

end FvdepCore.Evidence
