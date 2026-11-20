import FvdepAudit.Index.Command.Proof.Basic
import FvdepAudit.Oracle.Command.Proof.Stage

/-! The oracle plan's stages against the run written apart: each new effect's fitting responses,
the messages, each stage = the relation the spec states for it. -/

namespace FvdepAudit.Oracle.Command.Proof

open Lean FvdepCore FvdepCore.Ids FvdepCore.Index FvdepCore.Protocol FvdepCore.Oracle
open FvdepCore.Oracle.Command FvdepAudit.Oracle.Command.Spec
open FvdepAudit.Index.Command.Proof (runs_fit runs_stop runs_then)
open FvdepAudit.Index.Command.Spec (Refused Out)
open FvdepCore.Index.Rules (entryModule closure)

/-! ## Effects + their responses -/

theorem fits_project (x : Option String) (resp : Response) :
    Fits (.project x) resp ↔ ∃ r, resp = .project r := by cases resp <;> simp [Fits]

theorem fits_manifest (d : String) (resp : Response) :
    Fits (.manifest d) resp ↔ ∃ r, resp = .manifest r := by cases resp <;> simp [Fits]

theorem fits_parse (t : String) (resp : Response) :
    Fits (.parse t) resp ↔ ∃ r, resp = .parse r := by cases resp <;> simp [Fits]

theorem fits_snapshot (p : Option String) (l : FvdepCore.Library.Limits) (resp : Response) :
    Fits (.snapshot p l) resp ↔ ∃ r, resp = .snapshot r := by cases resp <;> simp [Fits]

theorem fits_closure (t : String) (rs : List String) (resp : Response) :
    Fits (.closure t rs) resp ↔ ∃ r, resp = .closure r := by cases resp <;> simp [Fits]

theorem fits_view (t : String) (rs : List String) (resp : Response) :
    Fits (.view t rs) resp ↔ ∃ r, resp = .view r := by cases resp <;> simp [Fits]

theorem fits_leanexport (v : String) (is rs : List String) (resp : Response) :
    Fits (.leanexport v is rs) resp ↔ ∃ r, resp = .leanexport r := by cases resp <;> simp [Fits]

theorem fits_stdin (c : Nat) (resp : Response) : Fits (.stdin c) resp ↔ ∃ r, resp = .stdin r := by
  cases resp <;> simp [Fits]

theorem fits_evaluate (v d : String) (b : ByteArray) (n : Nat) (resp : Response) :
    Fits (.evaluate v d b n) resp ↔ ∃ r, resp = .evaluate r := by cases resp <;> simp [Fits]

/-! ## Messages -/

theorem refuse_iff (ms : List String) (hm : ms ≠ []) (evs : List (Eff × Response))
    (code : UInt32) : Plan.Runs (refuse ms) evs (some code) ↔ Refused ms evs code :=
  runs_stop ms hm evs code

theorem one_ne (m : String) : [m] ≠ [] := List.cons_ne_nil _ _

theorem infraWord_eq : infraWord = word := by
  funext c
  cases c <;> rfl

theorem causeLine_eq (s : String) (c : Cause) : causeLine s c = causeMsg s c := by
  unfold causeLine causeMsg
  rw [infraWord_eq]
  rfl

theorem whyLine_eq (t : Target) (commit : String) (n : Nat) (w : Why) :
    whyLine t commit n w = whyMsg t commit n w := by
  cases w <;> rfl

theorem exportLine_eq (k : Nat) (r : Export.Refusal) : exportLine k r = exportMsg k r := by
  unfold exportLine exportMsg
  cases r.cls <;> simp [String.append_assoc] <;> rfl

theorem dotted_eq : Command.dotted = Spec.dotted := rfl

/-! ## V3–V5 -/

theorem runs_reply (lim : Command.Limits) (rs : List Reply) (evs : List (Eff × Response))
    (code : UInt32) : Plan.Runs (reply lim rs) evs (some code) ↔ Replied lim rs evs code := by
  unfold reply Replied
  rw [encodeAll_empty]
  dsimp only
  by_cases hc : lim.batchBytes < ((rs.map encodeReply).foldl (· ++ ·) ByteArray.empty).size
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact refuse_iff _ (one_ne _) evs code
  · rw [ite_eq_right hc, ite_eq_right hc]
    dsimp only
    by_cases hz : ((rs.map encodeReply).foldl (· ++ ·) ByteArray.empty).size = 0
    · rw [ite_eq_left hz]
      simp only [hz, beq_self_eq_true, ↓reduceIte, Plan.runs_pure_iff, Option.some.injEq]
    · rw [ite_eq_right hz]
      have hz' : (((rs.map encodeReply).foldl (· ++ ·) ByteArray.empty).size == 0) = false := by
        simpa using hz
      simp only [hz', Bool.false_eq_true, ↓reduceIte]
      rw [FvdepAudit.Index.Command.Proof.runs_last (Plan.fits_outBytes _)]

theorem runs_merged (lim : Command.Limits) (sig : Sig) (reqs : List Req) (b : ByteArray)
    (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs
        (match merge sig.result reqs b with
        | .ok rs => reply lim rs
        | .error k =>
          refuse [s!"infra io: oracle, evaluate: the driver's reply {k} is malformed"])
        evs (some code) ↔
      Merged lim sig reqs b evs code := by
  unfold Merged
  cases merge sig.result reqs b with
  | ok rs => exact runs_reply lim rs evs code
  | error k => exact refuse_iff _ (one_ne _) evs code

theorem runs_onEvaluate (lim : Command.Limits) (sig : Sig) (reqs : List Req)
    (rr : Except Cause ByteArray) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (onEvaluate lim sig reqs (.evaluate rr)) evs (some code) ↔
      match rr with
      | .ok rb => Merged lim sig reqs rb evs code
      | .error c => Refused [causeMsg "evaluate" c] evs code := by
  unfold onEvaluate
  cases rr with
  | ok rb => exact runs_merged lim sig reqs rb evs code
  | error c =>
    dsimp only
    rw [causeLine_eq]
    exact refuse_iff _ (one_ne _) evs code

theorem all_ne_valid (reqs : List Req) : reqs.all (· != .valid) = true ↔ Req.valid ∉ reqs := by
  simp only [List.all_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro h hm
    exact h _ hm rfl
  · intro h x hx hxv
    exact h (hxv ▸ hx)

theorem runs_onStdin (lim : Command.Limits) (M spec : Name) (sig : Sig) (view : String)
    (r : FileRead) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (onStdin lim M spec sig view (.stdin r)) evs (some code) ↔
      Input lim M spec sig view r evs code := by
  unfold onStdin Input
  cases r with
  | tooLarge => exact refuse_iff _ (one_ne _) evs code
  | failed x => exact refuse_iff _ (one_ne _) evs code
  | absent => exact refuse_iff _ (one_ne _) evs code
  | bytes b =>
    dsimp only
    by_cases hc : lim.requestBytes < b.size
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact refuse_iff _ (one_ne _) evs code
    · rw [ite_eq_right hc, ite_eq_right hc]
      rw [staged_iff lim sig b]
      cases hs : stageFrom lim sig b 0 {} with
      | error o =>
        cases o with
        | batch => exact refuse_iff _ (one_ne _) evs code
        | staging => exact refuse_iff _ (one_ne _) evs code
      | ok st =>
        dsimp only [Except.map]
        by_cases hv : Req.valid ∈ st.reqs.reverse
        · have hall : (st.reqs.reverse.all (· != .valid)) = false := by
            cases hb : st.reqs.reverse.all (· != .valid) with
            | false => rfl
            | true => exact absurd hv ((all_ne_valid _).mp hb)
          simp only [hall, Bool.false_eq_true, ↓reduceIte, hv]
          rw [runs_fit (fits_evaluate _ _ _ _)]
          refine exists_congr fun rr => exists_congr fun rest => and_congr_right fun _ => ?_
          exact runs_onEvaluate lim sig _ rr rest code
        · have hall : (st.reqs.reverse.all (· != .valid)) = true := (all_ne_valid _).mpr hv
          simp only [hall, ↓reduceIte, hv]
          exact runs_merged lim sig _ _ evs code

/-! ## E1–E5 + K -/

theorem runs_onExport2 (lim : Command.Limits) (t : Target) (commit : String) (M spec : Name)
    (view : String) (r : Except Cause ByteArray) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (onExport2 lim t commit M spec view (.leanexport r)) evs (some code) ↔
      Exported 2 r evs code (Signed lim t commit M spec view) := by
  unfold onExport2 Exported Signed
  cases r with
  | error c =>
    dsimp only
    rw [causeLine_eq]
    exact refuse_iff _ (one_ne _) evs code
  | ok b =>
    dsimp only
    cases Export.read Lean.githash Lean.versionString b with
    | error x =>
      dsimp only
      rw [exportLine_eq]
      exact refuse_iff _ (one_ne _) evs code
    | ok ds =>
      dsimp only
      cases specSig spec ds with
      | error w =>
        dsimp only
        rw [whyLine_eq]
        exact refuse_iff _ (one_ne _) evs code
      | ok sig =>
        dsimp only
        rw [runs_fit (fits_stdin _)]
        refine exists_congr fun x => exists_congr fun rest => and_congr_right fun _ => ?_
        exact runs_onStdin lim M spec sig view x rest code

theorem runs_onExport1 (lim : Command.Limits) (t : Target) (m : ModuleId) (v : EntryVersion)
    (commit : String) (mods : List Name) (view : String) (r : Except Cause ByteArray)
    (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (onExport1 lim t m v commit mods view (.leanexport r)) evs (some code) ↔
      Exported 1 r evs code (Entered lim t m v commit mods view) := by
  unfold onExport1 Exported Entered
  cases r with
  | error c =>
    dsimp only
    rw [causeLine_eq]
    exact refuse_iff _ (one_ne _) evs code
  | ok b =>
    dsimp only
    cases Export.read Lean.githash Lean.versionString b with
    | error x =>
      dsimp only
      rw [exportLine_eq]
      exact refuse_iff _ (one_ne _) evs code
    | ok ds =>
      dsimp only
      cases entrySpec lim.decodeNodes m v mods ds with
      | error w =>
        dsimp only
        rw [whyLine_eq]
        exact refuse_iff _ (one_ne _) evs code
      | ok spec =>
        dsimp only
        rw [runs_fit (fits_leanexport _ _ _)]
        refine exists_congr fun x => exists_congr fun rest => and_congr_right fun _ => ?_
        exact runs_onExport2 lim t commit (entryModule m v) spec view x rest code

theorem runs_onView (lim : Command.Limits) (t : Target) (m : ModuleId) (v : EntryVersion)
    (commit : String) (mods : List Name) (r : Except Cause String) (evs : List (Eff × Response))
    (code : UInt32) :
    Plan.Runs (onView lim t m v commit mods (.view r)) evs (some code) ↔
      Viewed lim t m v commit mods r evs code := by
  unfold onView Viewed
  cases r with
  | error c =>
    dsimp only
    rw [causeLine_eq]
    exact refuse_iff _ (one_ne _) evs code
  | ok view =>
    dsimp only
    rw [runs_fit (fits_leanexport _ _ _)]
    refine exists_congr fun x => exists_congr fun rest => and_congr_right fun _ => ?_
    exact runs_onExport1 lim t m v commit mods view x rest code

theorem runs_onClosure (h : ByteArray → String) (lim : Command.Limits) (t : Target) (m : ModuleId)
    (v : EntryVersion) (s : Snap) (i : IndexFile) (o : Operation) (r : Except String (List Src))
    (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (onClosure h lim t m v s i o (.closure r)) evs (some code) ↔
      Discovered h lim t m v s i o r evs code := by
  unfold onClosure Discovered
  cases r with
  | error x => exact refuse_iff _ (one_ne _) evs code
  | ok srcs =>
    dsimp only
    cases
      coherence h (FvdepCore.Index.Command.textOfBytes s.toolchain) i o (entryModule m v)
        srcs with
    | some why => exact refuse_iff _ (one_ne _) evs code
    | none =>
      dsimp only
      rw [runs_fit (fits_view _ _)]
      refine exists_congr fun x => exists_congr fun rest => and_congr_right fun _ => ?_
      exact runs_onView lim t m v s.commit _ x rest code

theorem runs_served (h : ByteArray → String) (lim : Command.Limits) (t : Target) (s : Snap)
    (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (served h lim t s) evs (some code) ↔ Served h lim t s evs code := by
  unfold served Served
  cases
    FvdepCore.Library.toolchainRefusal s.commit
      (FvdepCore.Index.Command.textOfBytes s.toolchain) FvdepCore.Index.Command.toolchain with
  | some x => exact refuse_iff _ (one_ne _) evs code
  | none =>
    dsimp only
    cases decodeIndex s.index with
    | error e => exact refuse_iff _ (one_ne _) evs code
    | ok i =>
      dsimp only
      cases t with
      | profile p => exact refuse_iff _ (one_ne _) evs code
      | op m v =>
        dsimp only
        cases rowOf i m v with
        | none => exact refuse_iff _ (one_ne _) evs code
        | some o =>
          dsimp only
          rw [runs_fit (fits_closure _ _)]
          refine exists_congr fun x => exists_congr fun rest => and_congr_right fun _ => ?_
          exact runs_onClosure h lim (.op m v) m v s i o x rest code

theorem runs_fetch (h : ByteArray → String) (lim : Command.Limits) (t : Target)
    (pin : Option String) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (fetch h lim t pin) evs (some code) ↔ Fetched h lim t pin evs code := by
  unfold fetch Fetched
  rw [runs_fit (fits_snapshot _ _)]
  refine exists_congr fun r => exists_congr fun rest => and_congr_right fun _ => ?_
  unfold onSnapshot
  cases r with
  | error x => exact refuse_iff _ (one_ne _) rest code
  | ok sn =>
    dsimp only
    cases sn.notice with
    | none => exact runs_served h lim t sn rest code
    | some n =>
      dsimp only
      rw [runs_then (Plan.fits_err _)]
      refine exists_congr fun post => and_congr_right fun _ => ?_
      exact runs_served h lim t sn post code

theorem runs_onManifest (h : ByteArray → String) (lim : Command.Limits) (t : Target) (dir : String)
    (r : FileRead) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (onManifest h lim t dir (.manifest r)) evs (some code) ↔
      ManifestRead h lim t dir r evs code := by
  unfold onManifest ManifestRead
  cases r with
  | absent => exact refuse_iff _ (one_ne _) evs code
  | tooLarge => exact refuse_iff _ (one_ne _) evs code
  | failed x => exact refuse_iff _ (one_ne _) evs code
  | bytes b =>
    dsimp only
    cases FvdepCore.Manifest.textStage b with
    | error e => exact refuse_iff _ (one_ne _) evs code
    | ok text =>
      dsimp only
      rw [runs_fit (fits_parse _)]
      refine exists_congr fun pr => exists_congr fun rest => and_congr_right fun _ => ?_
      unfold onParse
      cases pr with
      | error e => exact refuse_iff _ (one_ne _) rest code
      | ok tree =>
        dsimp only
        cases FvdepCore.Manifest.validate tree with
        | error e => exact refuse_iff _ (one_ne _) rest code
        | ok mf => exact runs_fetch h lim t _ rest code

/-- O3: a completed run of the oracle plan = exactly a run written apart. -/
theorem runs_plan (h : ByteArray → String) (lim : Command.Limits) (t : Target)
    (explicit : Option String) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (FvdepCore.Oracle.Command.plan h lim t explicit) evs (some code) ↔
      OracleRun h lim t explicit evs code := by
  unfold FvdepCore.Oracle.Command.plan OracleRun
  rw [runs_fit (fits_project _)]
  refine exists_congr fun seen => exists_congr fun rest => and_congr_right fun _ => ?_
  unfold onProject
  dsimp only
  cases FvdepCore.Project.selectProject seen with
  | none => exact runs_fetch h lim t none rest code
  | refuse x => exact refuse_iff _ (one_ne _) rest code
  | project dir =>
    dsimp only
    rw [runs_fit (fits_manifest _)]
    refine exists_congr fun r => exists_congr fun post => and_congr_right fun _ => ?_
    exact runs_onManifest h lim t dir r post code

end FvdepAudit.Oracle.Command.Proof
