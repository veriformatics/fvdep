import FvdepAudit.Index.Assemble.Proof.Basic
import FvdepAudit.Index.Command.Spec

/-! The index plan's stages against the run written apart: each effect's fitting responses, a
message = its lines on one stream, the toolchain reading + trim, the certificate's first refusal,
each stage relation as the function the plan computes; every plan extends to a completed run; the
effects every run of the plan may perform. -/

namespace FvdepAudit.Index.Command.Proof

open Lean FvdepCore FvdepCore.Doc FvdepCore.Index FvdepCore.Index.Registry FvdepCore.Index.Rules
open FvdepCore.Index.Statuses FvdepCore.Index.Assemble FvdepCore.Index.Command
open FvdepAudit.Index.Assemble.Spec FvdepAudit.Index.Assemble.Proof FvdepAudit.Index.Command.Spec

/-! ## Effects + their responses -/

/-- A step whose effect fits exactly the responses `C x`: a completed run = one such response, then
a completed run of the continuation. -/
theorem runs_fit {α β : Type} {e : Eff} {C : β → Response}
    (hC : ∀ resp, Fits e resp ↔ ∃ x, resp = C x) (k : Response → Plan α)
    (evs : List (Eff × Response)) (a : α) :
    Plan.Runs (.step e k) evs (some a) ↔
      ∃ x rest, evs = (e, C x) :: rest ∧ Plan.Runs (k (C x)) rest (some a) := by
  rw [Plan.runs_step_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨resp, rest, rfl, hf, hr⟩)
    · cases h
    · obtain ⟨x, rfl⟩ := (hC resp).mp hf
      exact ⟨x, rest, rfl, hr⟩
  · rintro ⟨x, rest, rfl, hr⟩
    exact .inr ⟨C x, rest, rfl, (hC _).mpr ⟨x, rfl⟩, hr⟩

theorem fits_probe (resp : Response) : Fits .probe resp ↔ ∃ r, resp = .probe r := by
  cases resp <;> simp [Fits]

theorem fits_facts (resp : Response) : Fits .libraryFacts resp ↔ ∃ r, resp = .facts r := by
  cases resp <;> simp [Fits]

theorem fits_replay (resp : Response) : Fits .replay resp ↔ ∃ r, resp = .replay r := by
  cases resp <;> simp [Fits]

theorem fits_read (f : ProjectFile) (resp : Response) :
    Fits (.read f) resp ↔ ∃ r, resp = .read r := by cases resp <;> simp [Fits]

theorem fits_replace (f : ProjectFile) (b : ByteArray) (resp : Response) :
    Fits (.replace f b) resp ↔ ∃ r, resp = .replace r := by cases resp <;> simp [Fits]

/-- An output write (response `done`), then a continuation. -/
theorem runs_then {α : Type} {e : Eff} (he : ∀ resp, Fits e resp ↔ resp = .done) (p : Plan α)
    (evs : List (Eff × Response)) (a : α) :
    Plan.Runs (.step e fun _ => p) evs (some a) ↔
      ∃ rest, evs = (e, .done) :: rest ∧ Plan.Runs p rest (some a) := by
  rw [Plan.runs_step_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨resp, rest, rfl, hf, hr⟩)
    · cases h
    · obtain rfl := (he resp).mp hf
      exact ⟨rest, rfl, hr⟩
  · rintro ⟨rest, rfl, hr⟩
    exact .inr ⟨.done, rest, rfl, (he _).mpr rfl, hr⟩

/-- An output write, then the exit code. -/
theorem runs_last {α : Type} {e : Eff} (he : ∀ resp, Fits e resp ↔ resp = .done) (c : α)
    (evs : List (Eff × Response)) (a : α) :
    Plan.Runs (.step e fun _ => .pure c) evs (some a) ↔ evs = [(e, .done)] ∧ a = c := by
  rw [runs_then he]
  constructor
  · rintro ⟨rest, rfl, hr⟩
    obtain ⟨rfl, h⟩ := (Plan.runs_pure_iff c rest (some a)).mp hr
    exact ⟨rfl, Option.some.inj h⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨[], rfl, .done _⟩

/-! ## The messages -/

/-- A refusal = its messages, one line each, on stderr + exit 2. -/
theorem runs_stop (ms : List String) (hm : ms ≠ []) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (stop ms 2) evs (some code) ↔ Refused ms evs code := by
  have he : ms.isEmpty = false := List.isEmpty_eq_false_iff.mpr hm
  simp only [stop, he, Bool.false_eq_true, ↓reduceIte]
  exact runs_last (Plan.fits_err _) 2 evs code

theorem runs_say (m : String) (c : UInt32) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (say m c) evs (some code) ↔ Said m c evs code :=
  runs_last (Plan.fits_out _) c evs code

/-! ## The toolchain -/

theorem textOf_iff (b : ByteArray) (s : String) : TextOf b s ↔ s = textOfBytes b := by
  unfold TextOf textOfBytes
  cases String.fromUTF8? b with
  | some s' =>
    simp only [Option.some.injEq, reduceCtorEq, false_and, or_false]
    exact eq_comm
  | none =>
    simp only [reduceCtorEq, true_and, false_or]
    rw [← String.toList_inj, String.toList_ofList]

/-- The text + its trim are functions of the bytes. -/
theorem text_trim (b : ByteArray) (P : String → String → Prop) :
    (∃ raw t, TextOf b raw ∧ Trimmed raw t ∧ P raw t) ↔
      P (textOfBytes b) (trimText (textOfBytes b)) := by
  constructor
  · rintro ⟨raw, t, hr, ht, hp⟩
    obtain rfl := (textOf_iff b raw).mp hr
    obtain rfl := trimmed_eq ht
    exact hp
  · intro hp
    exact ⟨_, _, (textOf_iff b _).mpr rfl, trimText_trimmed _, hp⟩

/-! ## The certificate + the registry's judgment -/

theorem certifiedList_iff (o : Observed) (c : Name) : certifiedList o c = true ↔ Certified o c := by
  have mn : (`Fvdep.Registry.modules : Name) ≠ `Fvdep.Registry.notices := by decide
  have mr : (`Fvdep.Registry.modules : Name) ≠ `Fvdep.Registry.removed := by decide
  have nr : (`Fvdep.Registry.notices : Name) ≠ `Fvdep.Registry.removed := by decide
  unfold certifiedList listType Certified FieldsOk
  simp only [modulesName, noticesName, removedName, moduleFields, noticeFields, removedFields]
  by_cases h1 : c = `Fvdep.Registry.modules
  · subst h1
    simp [mn, mr]
  · by_cases h2 : c = `Fvdep.Registry.notices
    · subst h2
      simp [Ne.symm mn, nr]
    · by_cases h3 : c = `Fvdep.Registry.removed
      · subst h3
        simp [Ne.symm mr, Ne.symm nr]
      · simp [h1, h2, h3]

theorem certifiedList_false (o : Observed) (c : Name) :
    certifiedList o c = false ↔ ¬Certified o c := by
  rw [← certifiedList_iff]
  cases certifiedList o c <;> simp

/-- The first list `certificate` holds that the observations do not certify. -/
theorem uncertified_first {o : Observed} {r : RawLists} {pre post : List (Name × Form × List Val)}
    {x : Name × Form × List Val} (e : certificate r = pre ++ x :: post) (hx : ¬Certified o x.1)
    (hpre : ∀ y ∈ pre, Certified o y.1) : uncertified o r = some x.1 := by
  unfold uncertified
  rw [List.find?_eq_some_iff_append.mpr
      ⟨by simpa [certifiedList_false] using hx, pre, post, e, fun y hy => by
        simpa [certifiedList_iff] using hpre y hy⟩]
  rfl

theorem judged_iff (o : Observed) (j : Except String Lists) :
    Judged o j ↔ j = Index.Command.judge o := by
  unfold Judged Index.Command.judge
  cases readRaw o.facts with
  | error c => exact Iff.rfl
  | ok r =>
    simp only
    cases hu : uncertified o r with
    | some c =>
      have hf := hu
      unfold uncertified at hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hf
      obtain ⟨hpx, pre, post, e, hpre⟩ := List.find?_eq_some_iff_append.mp hx
      have hnx : ¬Certified o x.1 := by
        rw [← certifiedList_iff]
        simpa using hpx
      have hpre' : ∀ y ∈ pre, Certified o y.1 := fun y hy => by
        rw [← certifiedList_iff]
        simpa using hpre y hy
      constructor
      · rintro (⟨pre', x', post', e', hx', hpre'', rfl⟩ | ⟨hall, _⟩)
        · rw [uncertified_first e' hx' hpre''] at hu
          have hx1 : x'.1 = x.1 := Option.some.inj hu
          show Except.error (formMsg x'.1) = Except.error (formLine x.1)
          rw [hx1]
          rfl
        · exact absurd (hall x (by simp [e])) hnx
      · rintro rfl
        exact .inl ⟨pre, x, post, e, hnx, hpre', rfl⟩
    | none =>
      have hall : ∀ y ∈ certificate r, Certified o y.1 := by
        unfold uncertified at hu
        simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true',
          Bool.not_eq_false] at hu
        exact fun y hy => (certifiedList_iff o y.1).mp (hu y hy)
      constructor
      · rintro (⟨pre, x, post, e, hx, _, _⟩ | ⟨_, hv⟩)
        · exact absurd (hall x (by simp [e])) hx
        · cases hval : validate o.facts (Lists.ofRaw r) <;> simp_all
      · intro hj
        refine .inr ⟨hall, ?_⟩
        cases hval : validate o.facts (Lists.ofRaw r) <;> simp_all

theorem indexed_iff (h : ByteArray → String) (raw : String) (o : Observed) (l : Lists)
    (j : Except (List String × String) (List String × ByteArray × Nat)) :
    Indexed h raw o l j ↔ j = indexStage h raw o l := by
  unfold Indexed indexStage
  cases assemble o.facts o.axioms l raw h with
  | error f => exact Iff.rfl
  | ok p =>
    obtain ⟨v, ws⟩ := p
    simp only
    cases IndexFile.ofJson v with
    | error e => exact Iff.rfl
    | ok i =>
      simp only
      cases encodeIndex i with
      | error e => exact Iff.rfl
      | ok b => exact Iff.rfl

/-! ## The stages -/

theorem runs_compare (b : ByteArray) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (.step (.read .index) (Index.Command.compare b)) evs (some code) ↔
      ∃ rr post, evs = (.read .index, .read rr) :: post ∧ Compared b rr post code := by
  rw [runs_fit (fits_read .index)]
  refine exists_congr fun rr => exists_congr fun post => and_congr_right fun _ => ?_
  cases rr with
  | error r => exact runs_stop _ (List.cons_ne_nil _ _) post code
  | ok x =>
    cases x with
    | none => exact runs_say _ _ post code
    | some
      c =>
      show
        Plan.Runs (if c.data = b.data then say current 0 else say differs 1) post (some code) ↔
          if c.data = b.data then Said "index.json is current" 0 post code
          else Said "index.json differs from the library" 1 post code
      by_cases hc : c.data = b.data
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact runs_say _ _ post code
      · rw [ite_eq_right hc, ite_eq_right hc]
        exact runs_say _ _ post code

theorem runs_written (b : ByteArray) (n : Nat) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (.step (.replace .index b) (written n)) evs (some code) ↔
      ∃ rr post, evs = (.replace .index b, .replace rr) :: post ∧ Wrote n rr post code := by
  rw [runs_fit (fits_replace .index b)]
  refine exists_congr fun rr => exists_congr fun post => and_congr_right fun _ => ?_
  cases rr with
  | error r => exact runs_stop _ (List.cons_ne_nil _ _) post code
  | ok u => exact runs_say _ _ post code

theorem runs_finish (check : Bool) (ws : List String) (b : ByteArray) (n : Nat)
    (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (finish check ws b n) evs (some code) ↔ Decided check ws b n evs code := by
  have hact :
    ∀ rest,
      Plan.Runs
          (if check then .step (.read .index) (Index.Command.compare b)
          else .step (.replace .index b) (written n))
          rest (some code) ↔
        if check then ∃ rr post, rest = (.read .index, .read rr) :: post ∧ Compared b rr post code
        else ∃ rr post, rest = (.replace .index b, .replace rr) :: post ∧ Wrote n rr post code := by
    intro rest
    cases check
    · exact runs_written b n rest code
    · exact runs_compare b rest code
  unfold finish Decided
  cases ws with
  | nil =>
    simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append, exists_eq_left']
    exact hact evs
  | cons w
    ws =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, List.cons_append,
      List.nil_append]
    rw [runs_then (Plan.fits_err _)]
    exact exists_congr fun rest => and_congr_right fun _ => hact rest

theorem runs_onReplay (h : ByteArray → String) (check : Bool) (tc : String) (o : Observed)
    (l : Lists) (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (.step .replay (onReplay h check tc o l)) evs (some code) ↔
      Replayed h check tc o l evs code := by
  rw [runs_fit fits_replay]
  unfold Replayed
  refine exists_congr fun rr => exists_congr fun rest => and_congr_right fun _ => ?_
  cases rr with
  | error r => exact runs_stop _ (List.cons_ne_nil _ _) rest code
  | ok x =>
    cases x with
    | some p =>
      obtain ⟨m, k⟩ := p
      exact runs_stop _ (List.cons_ne_nil _ _) rest code
    | none =>
      simp only [indexed_iff, exists_eq_left]
      unfold onReplay
      simp only [replayStage]
      cases indexStage h tc o l with
      | error p =>
        obtain ⟨ws, m⟩ := p
        exact runs_stop _ (by simp) rest code
      | ok p =>
        obtain ⟨ws, b, n⟩ := p
        exact runs_finish check ws b n rest code

theorem runs_onFacts (h : ByteArray → String) (check : Bool) (tc : String)
    (evs : List (Eff × Response)) (code : UInt32) :
    Plan.Runs (.step .libraryFacts (onFacts h check tc)) evs (some code) ↔
      Built h check tc evs code := by
  rw [runs_fit fits_facts]
  unfold Built
  refine exists_congr fun rf => exists_congr fun rest => and_congr_right fun _ => ?_
  cases rf with
  | error f =>
    cases f with
    | build l => exact runs_stop _ (List.cons_ne_nil _ _) rest code
    | load r => exact runs_stop _ (List.cons_ne_nil _ _) rest code
  | ok o =>
    simp only [judged_iff, exists_eq_left]
    unfold onFacts
    simp only [factsStage]
    cases Index.Command.judge o with
    | error m => exact runs_stop _ (List.cons_ne_nil _ _) rest code
    | ok l => exact runs_onReplay h check tc o l rest code

/-! ## Every plan completes; an interrupted run extends to a completed one -/

theorem fits_any (e : Eff) : ∃ r, Fits e r := by
  cases e with
  | out => exact ⟨.done, trivial⟩
  | err => exact ⟨.done, trivial⟩
  | read => exact ⟨.read (.ok none), trivial⟩
  | replace => exact ⟨.replace (.ok ()), trivial⟩
  | probe => exact ⟨.probe (.ok none), trivial⟩
  | libraryFacts => exact ⟨.facts (.error (.build "")), trivial⟩
  | replay => exact ⟨.replay (.ok none), trivial⟩

theorem runs_completes {α : Type} (p : Plan α) : ∃ evs a, Plan.Runs p evs (some a) := by
  induction p with
  | pure a => exact ⟨[], a, .done a⟩
  | step e k ih =>
    obtain ⟨r, hr⟩ := fits_any e
    obtain ⟨evs, a, h⟩ := ih r
    exact ⟨(e, r) :: evs, a, .step e k r evs (some a) hr h⟩

theorem runs_extends {α : Type} {p : Plan α} {evs : List (Eff × Response)}
    (h : Plan.Runs p evs none) : ∃ rest a, Plan.Runs p (evs ++ rest) (some a) := by
  generalize hn : (none : Option α) = r at h
  revert hn
  induction h with
  | done a => exact fun hn => by cases hn
  | stop e k => exact fun _ => runs_completes (.step e k)
  | step e k resp evs r hf _ ih =>
    intro hn
    obtain ⟨rest, a, h⟩ := ih hn
    exact ⟨rest, a, .step e k resp (evs ++ rest) (some a) hf h⟩

/-! ## The effects every run may perform -/

/-- Every effect a plan may perform, whatever the responses, satisfies `P`. -/
def Every {α : Type} (P : Eff → Prop) : Plan α → Prop
  | .pure _ => True
  | .step e k => P e ∧ ∀ r, Every P (k r)

theorem every_step {α : Type} {P : Eff → Prop} {e : Eff} {k : Response → Plan α} :
    Every P (.step e k) ↔ P e ∧ ∀ r, Every P (k r) := Iff.rfl

theorem every_runs {α : Type} {P : Eff → Prop} {p : Plan α} {evs : List (Eff × Response)}
    {r : Option α} (h : Plan.Runs p evs r) (hp : Every P p) : ∀ x ∈ evs, P x.1 := by
  revert hp
  induction h with
  | done => exact fun _ x hx => by cases hx
  | stop => exact fun _ x hx => by cases hx
  | step e k resp evs r _ _ ih =>
    intro hp x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp.1
    · exact ih (hp.2 resp) x hx

/-- What every effect of `fvdep index` meets: `index.json` alone is read (with `--check`) or
replaced (without it); each output write = one or more messages, each on its own line. -/
def Safe (check : Bool) (e : Eff) : Prop :=
  (∀ f, e = .read f → f = .index ∧ check = true) ∧
    (∀ f b, e = .replace f b → f = .index ∧ check = false) ∧
    ∀ s, (e = .out s ∨ e = .err s) → ∃ ms, ms ≠ [] ∧ s = lines ms

theorem safe_observe (check : Bool) (e : Eff) (he : e = .probe ∨ e = .libraryFacts ∨ e = .replay) :
    Safe check e := by
  rcases he with rfl | rfl | rfl <;>
    exact
      ⟨(fun _ h => by cases h), (fun _ _ h => by cases h), fun _ hs => by
        rcases hs with h | h <;> cases h⟩

theorem safe_err (check : Bool) (ms : List String) (hm : ms ≠ []) : Safe check (.err (lines ms)) :=
  ⟨(fun _ h => by cases h), (fun _ _ h => by cases h), fun s hs => by
    rcases hs with h | h
    · cases h
    · cases h
      exact ⟨ms, hm, rfl⟩⟩

theorem every_stop (check : Bool) (ms : List String) (hm : ms ≠ []) (c : UInt32) :
    Every (Safe check) (stop ms c) := by
  have he : ms.isEmpty = false := List.isEmpty_eq_false_iff.mpr hm
  simp only [stop, he, Bool.false_eq_true, ↓reduceIte]
  exact every_step.mpr ⟨safe_err check ms hm, fun _ => trivial⟩

theorem every_say (check : Bool) (m : String) (c : UInt32) : Every (Safe check) (say m c) :=
  every_step.mpr
    ⟨⟨(fun _ h => by cases h), (fun _ _ h => by cases h), fun s hs => by
        rcases hs with h | h
        · cases h
          exact ⟨[m], List.cons_ne_nil _ _, rfl⟩
        · cases h⟩,
      fun _ => trivial⟩

theorem every_compare (check : Bool) (b : ByteArray) (r : Response) :
    Every (Safe check) (Index.Command.compare b r) := by
  unfold Index.Command.compare
  split <;> (try split) <;>
    first
    | exact every_say check _ _
    | exact every_stop check _ (List.cons_ne_nil _ _) 2

theorem every_written (check : Bool) (n : Nat) (r : Response) :
    Every (Safe check) (written n r) := by
  unfold written
  split <;>
    first
    | exact every_say check _ _
    | exact every_stop check _ (List.cons_ne_nil _ _) 2

theorem every_finish (check : Bool) (ws : List String) (b : ByteArray) (n : Nat) :
    Every (Safe check) (finish check ws b n) := by
  have hact :
    Every (Safe check)
      (if check then Plan.step (.read .index) (Index.Command.compare b)
      else .step (.replace .index b) (written n)) := by
    cases check
    · refine
        every_step.mpr ⟨⟨(fun _ h => by cases h), fun f b' h => ?_, fun s hs => ?_⟩, fun r => ?_⟩
      · cases h
        exact ⟨rfl, rfl⟩
      · rcases hs with h | h <;> cases h
      · exact every_written false n r
    · refine
        every_step.mpr ⟨⟨fun f h => ?_, (fun _ _ h => by cases h), fun s hs => ?_⟩, fun r => ?_⟩
      · cases h
        exact ⟨rfl, rfl⟩
      · rcases hs with h | h <;> cases h
      · exact every_compare true b r
  unfold finish
  cases ws with
  | nil => exact hact
  | cons w ws => exact every_step.mpr ⟨safe_err check _ (List.cons_ne_nil _ _), fun _ => hact⟩

theorem every_onReplay (h : ByteArray → String) (check : Bool) (tc : String) (o : Observed)
    (l : Lists) (r : Response) : Every (Safe check) (onReplay h check tc o l r) := by
  unfold onReplay
  split
  · exact every_stop check _ (List.cons_ne_nil _ _) 2
  · split
    · exact every_stop check _ (by simp) 2
    · exact every_finish check _ _ _

theorem every_onFacts (h : ByteArray → String) (check : Bool) (tc : String) (r : Response) :
    Every (Safe check) (onFacts h check tc r) := by
  unfold onFacts
  split
  · exact every_stop check _ (List.cons_ne_nil _ _) 2
  · split
    · exact every_stop check _ (List.cons_ne_nil _ _) 2
    · exact
        every_step.mpr
          ⟨safe_observe check _ (.inr (.inr rfl)), fun r => every_onReplay h check tc _ _ r⟩

theorem every_onProbe (h : ByteArray → String) (check : Bool) (r : Response) :
    Every (Safe check) (onProbe h check r) := by
  unfold onProbe
  split
  · exact every_stop check _ (List.cons_ne_nil _ _) 2
  · exact
      every_step.mpr ⟨safe_observe check _ (.inr (.inl rfl)), fun r => every_onFacts h check _ r⟩

theorem every_plan (h : ByteArray → String) (check : Bool) :
    Every (Safe check) (Index.Command.plan h check) :=
  every_step.mpr ⟨safe_observe check _ (.inl rfl), fun r => every_onProbe h check r⟩

/-! ## The line rule -/

theorem isControl_false {c : Char} :
    isControl c = false ↔ ¬(c.toNat < 32 ∨ 127 ≤ c.toNat ∧ c.toNat ≤ 159) := by
  simp only [isControl, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  constructor <;> intro h <;> omega

theorem hexUpper_clean : ∀ k, k < 16 → isControl (hexUpper k) = false := by decide

/-- An escaped message holds no control character (interface §1's line rule). -/
theorem escapeControls_clean (m : String) (c : Char) (hc : c ∈ (escapeControls m).toList) :
    isControl c = false := by
  simp only [escapeControls, String.toList_ofList, List.mem_flatMap] at hc
  obtain ⟨d, _, hd⟩ := hc
  have hctl : isControl d = true → d.toNat ≤ 159 := by
    intro h
    simp only [isControl, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    omega
  generalize hn : d.toNat = n at hd
  split at hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  · split at hd
    · have h159 := hctl ‹_›
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · exact hexUpper_clean _ (by omega)
      · exact hexUpper_clean _ (Nat.mod_lt _ (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [hd]
      simpa using ‹¬isControl d = true›

end FvdepAudit.Index.Command.Proof
