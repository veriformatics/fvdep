import FvdepAudit.Oracle.Command.Proof.Basic

/-! `fvdep oracle` against the run written apart (`OracleRun`): the completed runs = exactly the
runs written apart; an interrupted run = a prefix of one; no run reads or replaces a project file;
every text write = lines under interface §1's line rule. Headers = the ledger statements. -/

namespace FvdepAudit.Oracle.Command.Proof

open Lean FvdepCore FvdepCore.Ids FvdepCore.Index FvdepCore.Protocol FvdepCore.Oracle
open FvdepCore.Oracle.Command FvdepAudit.Oracle.Command.Spec
open FvdepAudit.Index.Command.Proof (runs_extends escapeControls_clean isControl_false)
open FvdepCore.Index.Rules (entryModule closure)

/-! ## The effects every run may perform -/

/-- Every effect a plan may perform under fitting responses satisfies `P`. -/
def EveryFit {α : Type} (P : Eff → Prop) : Plan α → Prop
  | .pure _ => True
  | .step e k => P e ∧ ∀ r, Fits e r → EveryFit P (k r)

theorem everyFit_step {α : Type} {P : Eff → Prop} {e : Eff} {k : Response → Plan α} :
    EveryFit P (.step e k) ↔ P e ∧ ∀ r, Fits e r → EveryFit P (k r) := Iff.rfl

theorem everyFit_runs {α : Type} {P : Eff → Prop} {p : Plan α} {evs : List (Eff × Response)}
    {r : Option α} (h : Plan.Runs p evs r) (hp : EveryFit P p) : ∀ x ∈ evs, P x.1 := by
  revert hp
  induction h with
  | done => exact fun _ x hx => by cases hx
  | stop => exact fun _ x hx => by cases hx
  | step e k resp evs r hf _ ih =>
    intro hp x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp.1
    · exact ih (hp.2 resp hf) x hx

/-- What every effect of `fvdep oracle` meets: no project-file read or replace; each text write =
one or more messages, each on its own line. -/
def OSafe (e : Eff) : Prop :=
  (∀ f, e ≠ .read f) ∧
    (∀ f b, e ≠ .replace f b) ∧
    ∀ s, (e = .out s ∨ e = .err s) → ∃ ms, ms ≠ [] ∧ s = FvdepCore.Index.Command.lines ms

/-- An observation effect or the replies' write. -/
theorem osafe_obs {e : Eff}
    (h :
      match e with
      | .out _ | .err _ | .read _ | .replace _ _ => False
      | _ => True) :
    OSafe e := by
  cases e <;> simp only at h <;>
    exact
      ⟨(fun _ hx => by cases hx), (fun _ _ hx => by cases hx), fun _ hs => by
        rcases hs with hx | hx <;> cases hx⟩

theorem osafe_err (ms : List String) (hm : ms ≠ []) :
    OSafe (.err (FvdepCore.Index.Command.lines ms)) :=
  ⟨(fun _ hx => by cases hx), (fun _ _ hx => by cases hx), fun s hs => by
    rcases hs with hx | hx
    · cases hx
    · cases hx
      exact ⟨ms, hm, rfl⟩⟩

theorem every_refuse (ms : List String) (hm : ms ≠ []) : EveryFit OSafe (refuse ms) := by
  have he : ms.isEmpty = false := List.isEmpty_eq_false_iff.mpr hm
  simp only [refuse, FvdepCore.Index.Command.stop, he, Bool.false_eq_true, ↓reduceIte]
  exact everyFit_step.mpr ⟨osafe_err ms hm, fun _ _ => trivial⟩

/-- A step of an observation effect whose fitting responses are `C x`. -/
theorem every_obs {β : Type} {e : Eff} {C : β → Response}
    (hC : ∀ resp, Fits e resp ↔ ∃ x, resp = C x) (he : OSafe e) {k : Response → Plan UInt32}
    (hk : ∀ x, EveryFit OSafe (k (C x))) : EveryFit OSafe (.step e k) := by
  refine everyFit_step.mpr ⟨he, fun r hr => ?_⟩
  obtain ⟨x, rfl⟩ := (hC r).mp hr
  exact hk x

theorem every_reply (lim : Command.Limits) (rs : List Reply) : EveryFit OSafe (reply lim rs) := by
  unfold reply
  split
  · exact every_refuse _ (one_ne _)
  · split
    · trivial
    · exact everyFit_step.mpr ⟨osafe_obs trivial, fun _ _ => trivial⟩

theorem every_merged (lim : Command.Limits) (sig : Sig) (reqs : List Req) (b : ByteArray) :
    EveryFit OSafe
      (match merge sig.result reqs b with
      | .ok rs => reply lim rs
      | .error k =>
        refuse [s!"infra io: oracle, evaluate: the driver's reply {k} is malformed"]) := by
  split
  · exact every_reply lim _
  · exact every_refuse _ (one_ne _)

theorem every_onEvaluate (lim : Command.Limits) (sig : Sig) (reqs : List Req)
    (rr : Except Cause ByteArray) : EveryFit OSafe (onEvaluate lim sig reqs (.evaluate rr)) := by
  unfold onEvaluate
  cases rr with
  | ok b => exact every_merged lim sig reqs b
  | error c => exact every_refuse _ (one_ne _)

theorem every_onStdin (lim : Command.Limits) (M spec : Name) (sig : Sig) (view : String)
    (r : FileRead) : EveryFit OSafe (onStdin lim M spec sig view (.stdin r)) := by
  unfold onStdin
  cases r with
  | tooLarge => exact every_refuse _ (one_ne _)
  | failed x => exact every_refuse _ (one_ne _)
  | absent => exact every_refuse _ (one_ne _)
  | bytes b =>
    dsimp only
    split
    · exact every_refuse _ (one_ne _)
    · cases stageFrom lim sig b 0 {} with
      | error o =>
        cases o with
        | batch => exact every_refuse _ (one_ne _)
        | staging => exact every_refuse _ (one_ne _)
      | ok st =>
        dsimp only
        split
        · exact every_merged lim sig _ _
        · exact
            every_obs (fits_evaluate _ _ _ _) (osafe_obs trivial) fun rr =>
              every_onEvaluate lim sig _ rr

theorem every_onExport2 (lim : Command.Limits) (t : Target) (commit : String) (M spec : Name)
    (view : String) (r : Except Cause ByteArray) :
    EveryFit OSafe (onExport2 lim t commit M spec view (.leanexport r)) := by
  unfold onExport2
  cases r with
  | error c => exact every_refuse _ (one_ne _)
  | ok b =>
    dsimp only
    cases Export.read Lean.githash Lean.versionString b with
    | error x => exact every_refuse _ (one_ne _)
    | ok ds =>
      dsimp only
      cases specSig spec ds with
      | error w => exact every_refuse _ (one_ne _)
      | ok sig =>
        exact
          every_obs (fits_stdin _) (osafe_obs trivial) fun x => every_onStdin lim M spec sig view x

theorem every_onExport1 (lim : Command.Limits) (t : Target) (m : ModuleId) (v : EntryVersion)
    (commit : String) (mods : List Name) (view : String) (r : Except Cause ByteArray) :
    EveryFit OSafe (onExport1 lim t m v commit mods view (.leanexport r)) := by
  unfold onExport1
  cases r with
  | error c => exact every_refuse _ (one_ne _)
  | ok b =>
    dsimp only
    cases Export.read Lean.githash Lean.versionString b with
    | error x => exact every_refuse _ (one_ne _)
    | ok ds =>
      dsimp only
      cases entrySpec lim.decodeNodes m v mods ds with
      | error w => exact every_refuse _ (one_ne _)
      | ok spec =>
        exact
          every_obs (fits_leanexport _ _ _) (osafe_obs trivial) fun x =>
            every_onExport2 lim t commit (entryModule m v) spec view x

theorem every_onView (lim : Command.Limits) (t : Target) (m : ModuleId) (v : EntryVersion)
    (commit : String) (mods : List Name) (r : Except Cause String) :
    EveryFit OSafe (onView lim t m v commit mods (.view r)) := by
  unfold onView
  cases r with
  | error c => exact every_refuse _ (one_ne _)
  | ok view =>
    exact
      every_obs (fits_leanexport _ _ _) (osafe_obs trivial) fun x =>
        every_onExport1 lim t m v commit mods view x

theorem every_onClosure (h : ByteArray → String) (lim : Command.Limits) (t : Target) (m : ModuleId)
    (v : EntryVersion) (s : Snap) (i : IndexFile) (o : Operation) (r : Except String (List Src)) :
    EveryFit OSafe (onClosure h lim t m v s i o (.closure r)) := by
  unfold onClosure
  cases r with
  | error x => exact every_refuse _ (one_ne _)
  | ok srcs =>
    dsimp only
    cases
      coherence h (FvdepCore.Index.Command.textOfBytes s.toolchain) i o (entryModule m v) srcs with
    | some why => exact every_refuse _ (one_ne _)
    | none =>
      exact
        every_obs (fits_view _ _) (osafe_obs trivial) fun x => every_onView lim t m v s.commit _ x

theorem every_served (h : ByteArray → String) (lim : Command.Limits) (t : Target) (s : Snap) :
    EveryFit OSafe (served h lim t s) := by
  unfold served
  cases
    FvdepCore.Library.toolchainRefusal s.commit (FvdepCore.Index.Command.textOfBytes s.toolchain)
      FvdepCore.Index.Command.toolchain with
  | some x => exact every_refuse _ (one_ne _)
  | none =>
    dsimp only
    cases decodeIndex s.index with
    | error e => exact every_refuse _ (one_ne _)
    | ok i =>
      dsimp only
      cases t with
      | profile p => exact every_refuse _ (one_ne _)
      | op m v =>
        dsimp only
        cases rowOf i m v with
        | none => exact every_refuse _ (one_ne _)
        | some o =>
          exact
            every_obs (fits_closure _ _) (osafe_obs trivial) fun x =>
              every_onClosure h lim _ m v s i o x

set_option maxHeartbeats 2000000 in
theorem every_fetch (h : ByteArray → String) (lim : Command.Limits) (t : Target)
    (pin : Option String) : EveryFit OSafe (fetch h lim t pin) := by
  unfold fetch
  refine every_obs (fits_snapshot _ _) (osafe_obs trivial) fun x => ?_
  unfold onSnapshot
  cases x with
  | error x => exact every_refuse _ (one_ne _)
  | ok sn =>
    dsimp only
    cases sn.notice with
    | none => exact every_served h lim t sn
    | some n =>
      refine everyFit_step.mpr ⟨osafe_err _ (one_ne _), fun _ _ => ?_⟩
      exact every_served h lim t sn

theorem every_onManifest (h : ByteArray → String) (lim : Command.Limits) (t : Target) (dir : String)
    (r : FileRead) : EveryFit OSafe (onManifest h lim t dir (.manifest r)) := by
  unfold onManifest
  cases r with
  | absent => exact every_refuse _ (one_ne _)
  | tooLarge => exact every_refuse _ (one_ne _)
  | failed x => exact every_refuse _ (one_ne _)
  | bytes b =>
    dsimp only
    cases FvdepCore.Manifest.textStage b with
    | error e => exact every_refuse _ (one_ne _)
    | ok text =>
      refine every_obs (fits_parse _) (osafe_obs trivial) fun pr => ?_
      unfold onParse
      cases pr with
      | error e => exact every_refuse _ (one_ne _)
      | ok tree =>
        dsimp only
        cases FvdepCore.Manifest.validate tree with
        | error e => exact every_refuse _ (one_ne _)
        | ok mf => exact every_fetch h lim t _

theorem every_plan (h : ByteArray → String) (lim : Command.Limits) (t : Target)
    (explicit : Option String) :
    EveryFit OSafe (FvdepCore.Oracle.Command.plan h lim t explicit) := by
  unfold FvdepCore.Oracle.Command.plan
  refine every_obs (fits_project _) (osafe_obs trivial) fun seen => ?_
  unfold onProject
  dsimp only
  cases FvdepCore.Project.selectProject seen with
  | none => exact every_fetch h lim t none
  | refuse x => exact every_refuse _ (one_ne _)
  | project dir =>
    exact every_obs (fits_manifest _) (osafe_obs trivial) fun r => every_onManifest h lim t dir r

/-! ## The claims -/

/-- U5b O3 `oracleExact`: a completed run of `fvdep oracle` = exactly a run written apart
(`OracleRun`): the project, its manifest's pin or the head, the snapshot (its notice), the
toolchain, `index.json`, the target's row, K's discovery + E2's coherence, the view, export 1 + the
entry, export 2 + the signature, stdin, V2's staging + budgets, the one evaluation (none for no
valid request), the merge, the batch budget, then the replies in one stdout write; each refusal =
its line on stderr + exit 2, no effect after it. -/
theorem oracle_exact (h : ByteArray → String) (lim : FvdepCore.Oracle.Command.Limits)
    (t : FvdepCore.Oracle.Target) (explicit : Option String) (evs : List (Eff × Response))
    (code : UInt32) :
    Plan.Runs (FvdepCore.Oracle.Command.plan h lim t explicit) evs (some code) ↔
      OracleRun h lim t explicit evs code := runs_plan h lim t explicit evs code

/-- U2 X5 for `fvdep oracle`: an interrupted run performed a prefix of a completed run written
apart. -/
theorem oracle_prefix (h : ByteArray → String) (lim : FvdepCore.Oracle.Command.Limits)
    (t : FvdepCore.Oracle.Target) (explicit : Option String) (evs : List (Eff × Response)) :
    Plan.Runs (FvdepCore.Oracle.Command.plan h lim t explicit) evs none →
      ∃ rest code, OracleRun h lim t explicit (evs ++ rest) code := by
  intro hr
  obtain ⟨rest, code, hc⟩ := runs_extends hr
  exact ⟨rest, code, (runs_plan h lim t explicit _ code).mp hc⟩

/-- U5b O1: no run of `fvdep oracle`, completed or interrupted, writes a project file or reads one
through the generic project-file effects (the selected project's `fvdep.toml` arrives through P2's
`manifest` effect alone: `oracleExact`). -/
theorem oracle_files (h : ByteArray → String) (lim : FvdepCore.Oracle.Command.Limits)
    (t : FvdepCore.Oracle.Target) (explicit : Option String) (evs : List (Eff × Response))
    (r : Option UInt32) :
    Plan.Runs (FvdepCore.Oracle.Command.plan h lim t explicit) evs r →
      ∀ x ∈ evs, (∀ f, x.1 ≠ .read f) ∧ ∀ f b, x.1 ≠ .replace f b := by
  intro hr x hx
  have hs := everyFit_runs hr (every_plan h lim t explicit) x hx
  exact ⟨hs.1, hs.2.1⟩

/-- Interface §1's line rule for `fvdep oracle`, structurally: every text write of every run = one
or more lines, each ending in LF, with no Unicode `Cc` character inside a line (the escaping's
spelling = `escapeControls`, tested presentation, bound to each message by `oracleExact`). -/
theorem oracle_lines (h : ByteArray → String) (lim : FvdepCore.Oracle.Command.Limits)
    (t : FvdepCore.Oracle.Target) (explicit : Option String) (evs : List (Eff × Response))
    (r : Option UInt32) :
    Plan.Runs (FvdepCore.Oracle.Command.plan h lim t explicit) evs r →
      ∀ x ∈ evs,
        ∀ s,
          (x.1 = .out s ∨ x.1 = .err s) →
            ∃ ls : List String,
              ls ≠ [] ∧
                s = String.join (ls.map (· ++ "\n")) ∧
                ∀ l ∈ ls, ∀ c ∈ l.toList, ¬(c.toNat < 32 ∨ 127 ≤ c.toNat ∧ c.toNat ≤ 159) := by
  intro hr x hx s hs
  obtain ⟨ms, hm, rfl⟩ := (everyFit_runs hr (every_plan h lim t explicit) x hx).2.2 s hs
  refine ⟨ms.map FvdepCore.Doc.escapeControls, by simpa using hm, ?_, ?_⟩
  · rw [List.map_map]
    rfl
  · intro l hl c hc
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hl
    exact isControl_false.mp (escapeControls_clean m c hc)

end FvdepAudit.Oracle.Command.Proof
