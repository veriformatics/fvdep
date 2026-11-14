import FvdepAudit.Sys.Proof.ReplaceExact

/-! The directory model: per-call effects + runs of trace segments (`Seg`). -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

@[simp]
theorem put_files (s : DirState) (p : String) (c : Option (List UInt8)) (q : String) :
    (s.put p c).files q = if q = p then c else s.files q := rfl

@[simp]
theorem put_owners (s : DirState) (p : String) (c : Option (List UInt8)) :
    (s.put p c).owners = s.owners := rfl

@[simp]
theorem own_files (s : DirState) (fd : Nat) (p : Option String) :
    (s.own fd p).files = s.files := rfl

@[simp]
theorem own_owners (s : DirState) (fd : Nat) (p : Option String) (g : Nat) :
    (s.own fd p).owners g = if g = fd then p else s.owners g := rfl

theorem move_files_other (s : DirState) {src dst q : String} (hs : q ≠ src) (hd : q ≠ dst) :
    (s.move src dst).files q = s.files q := by
  unfold DirState.move
  split
  · rfl
  · split
    · rfl
    · simp [hs, hd]

theorem move_owners (s : DirState) (src dst : String) : (s.move src dst).owners = s.owners := by
  unfold DirState.move
  split
  · rfl
  · split
    · rfl
    · rfl

theorem move_absent (s : DirState) {src dst : String} (h : s.files src = none) :
    s.move src dst = s := by
  unfold DirState.move
  split
  · rfl
  · rw [h]

theorem move_present (s : DirState) {src dst : String} {c : List UInt8} (hne : src ≠ dst)
    (h : s.files src = some c) :
    (s.move src dst).files dst = some c ∧ (s.move src dst).files src = none := by
  unfold DirState.move
  simp [hne, h, Ne.symm hne]

theorem tempText_ne (dir : Path) (name : Name) (pid n : Nat) :
    tempText dir name pid n ≠ targetText dir name := by
  intro h
  have := congrArg (fun s => s.toList.length) h
  simp [tempText, targetText] at this
  omega

theorem dir_ne_target (dir : Path) (name : Name) : dir.toString ≠ targetText dir name := by
  intro h
  have := congrArg (fun s => s.toList.length) h
  simp [targetText] at this

/-! ### Per-call effects -/

theorem step_files_other {payload : List UInt8} {s s' : DirState} {request : Request}
    {response : Response} {t : String} (h : Step payload s ⟨request, response⟩ s')
    (hn : ¬Names t request) (hw : ∀ g o c, request = .write g o c → s.owners g ≠ some t) :
    s'.files t = s.files t := by
  cases h with
  | applied =>
    cases request with
    | create p mode =>
      cases response with
      | ok
        fd =>
        have hp : t ≠ p.toString := fun e =>
          hn
            (by
              simp only [Names]; exact e.symm)
        simp [apply, hp]
      | error n => rfl
    | openDir p => cases response <;> rfl
    | openRead p => cases response <;> rfl
    | openLock p =>
      cases response with
      | ok
        fd =>
        have hp : t ≠ p.toString := fun e =>
          hn
            (by
              simp only [Names]; exact e.symm)
        simp [apply, hp]
      | error n => rfl
    | write g o c =>
      cases response with
      | ok n =>
        simp only [apply]
        cases hg : s.owners g with
        | none => rfl
        | some
          p =>
          have hp : t ≠ p := fun e =>
            hw g o c rfl
              (by
                rw [e]; exact hg)
          simp [hp]
      | error n => rfl
    | fsync g => cases response <;> rfl
    | close g => cases response <;> rfl
    | read g c => cases response <;> rfl
    | rename src dst =>
      cases response with
      | ok n =>
        simp only [Names, not_or] at hn
        exact move_files_other s (Ne.symm hn.1) (Ne.symm hn.2)
      | error n => rfl
    | unlink p =>
      cases response with
      | ok
        n =>
        have hp : t ≠ p.toString := fun e =>
          hn
            (by
              simp only [Names]; exact e.symm)
        simp [apply, hp]
      | error n => rfl
    | lock g => cases response <;> rfl
  | landed =>
    simp only [Names, not_or] at hn
    exact move_files_other s (Ne.symm hn.1) (Ne.symm hn.2)

theorem step_write_owners {payload : List UInt8} {s s' : DirState} {fd o c : Nat}
    {response : Response} (h : Step payload s ⟨.write fd o c, response⟩ s') :
    s'.owners = s.owners := by
  cases h with
  | applied =>
    cases response with
    | ok n =>
      simp only [apply]
      cases s.owners fd with
      | none => rfl
      | some p => rfl
    | error n => rfl

theorem step_write_ok {payload : List UInt8} {s s' : DirState} {fd o c n : Nat} {tp : String}
    (h : Step payload s ⟨.write fd o c, .ok n⟩ s') (owner : s.owners fd = some tp) :
    s' = s.put tp ((s.files tp).map (· ++ (payload.drop o).take n)) := by
  cases h with
  | applied => simp [apply, owner]

theorem step_write_error {payload : List UInt8} {s s' : DirState} {fd o c n : Nat}
    (h : Step payload s ⟨.write fd o c, .error n⟩ s') : s' = s := by
  cases h with
  | applied => rfl

theorem step_rename {payload : List UInt8} {s s' : DirState} {src dst : Path} {response : Response}
    (h : Step payload s ⟨.rename src dst, response⟩ s') :
    s' = s ∨ s' = s.move src.toString dst.toString := by
  cases h with
  | applied =>
    cases response with
    | ok n => exact .inr rfl
    | error n => exact .inl rfl
  | landed => exact .inr rfl

theorem step_rename_ok {payload : List UInt8} {s s' : DirState} {src dst : Path} {n : Nat}
    (h : Step payload s ⟨.rename src dst, .ok n⟩ s') : s' = s.move src.toString dst.toString := by
  cases h with
  | applied => rfl

theorem step_create_ok {payload : List UInt8} {s s' : DirState} {p : Path} {mode : Mode} {fd : Nat}
    (h : Step payload s ⟨.create p mode, .ok fd⟩ s') :
    s' = (s.put p.toString (some [])).own fd (some p.toString) := by
  cases h with
  | applied => rfl

/-! ### Runs -/

theorem steps_append {payload : List UInt8} {a b : Trace} :
    ∀ {s s' : DirState},
      Steps payload s (a ++ b) s' ↔ ∃ m, Steps payload s a m ∧ Steps payload m b s' := by
  induction a with
  | nil =>
    intro s s'
    constructor
    · intro h
      exact ⟨s, .nil s, h⟩
    · rintro ⟨m, hm, hb⟩
      cases hm
      exact hb
  | cons e a ih =>
    intro s s'
    constructor
    · intro h
      cases h with
      | cons head tail =>
        obtain ⟨m, h₁, h₂⟩ := ih.mp tail
        exact ⟨m, .cons head h₁, h₂⟩
    · rintro ⟨m, hm, hb⟩
      cases hm with
      | cons head tail => exact .cons head (ih.mpr ⟨m, tail, hb⟩)

theorem steps_preserve {payload : List UInt8} (P : DirState → Prop) :
    ∀ {ev : Trace} {s s' : DirState},
      (∀ e ∈ ev, ∀ r s s', P s → Step payload s ⟨e.request, r⟩ s' → P s') →
        Steps payload s ev s' → P s → P s'
  | [], _, _, _, hs, hp => by
    cases hs
    exact hp
  | e :: _, _, _, h, hs, hp => by
    cases hs with
    | cons head tail =>
      exact
        steps_preserve P (fun x hx => h x (List.mem_cons_of_mem _ hx)) tail
          (h e (List.mem_cons_self ..) e.response _ _ hp head)

theorem steps_same {payload : List UInt8} :
    ∀ {ev : Trace} {s s' : DirState},
      (∀ e ∈ ev, ∀ s s', Step payload s e s' → s' = s) → Steps payload s ev s' → s' = s
  | [], _, _, _, hs => by
    cases hs
    rfl
  | e :: _, _, _, h, hs => by
    cases hs with
    | cons head tail =>
      rw [steps_same (fun x hx => h x (List.mem_cons_of_mem _ hx)) tail,
        h e (List.mem_cons_self ..) _ _ head]

/-- Every way to run `seg` from a state satisfying `pre`: a complete run ends in `post`; a run
stopped at any call (in flight: not started, or done with any response) ends in `cut`. -/
def Seg (payload : List UInt8) (pre : DirState → Prop) (seg : Trace) (post cut : DirState → Prop) :
    Prop :=
  (∀ s s', pre s → Steps payload s seg s' → post s') ∧
    ∀ s done x rest s₁ s',
      pre s →
        seg = done ++ x :: rest →
        Steps payload s done s₁ → InFlight payload s₁ x.request s' → cut s'

theorem seg_append {payload : List UInt8} {pre mid post cutA cutB : DirState → Prop} {a b : Trace}
    (ha : Seg payload pre a mid cutA) (hb : Seg payload mid b post cutB) :
    Seg payload pre (a ++ b) post fun s => cutA s ∨ cutB s := by
  constructor
  · intro s s' hp h
    obtain ⟨m, h₁, h₂⟩ := steps_append.mp h
    exact hb.1 m s' (ha.1 s m hp h₁) h₂
  · intro s done x rest s₁ s' hp he hd hf
    rcases List.append_eq_append_iff.mp he with ⟨a', rfl, hb'⟩ | ⟨c', ha', hx⟩
    · obtain ⟨m, h₁, h₂⟩ := steps_append.mp hd
      exact .inr (hb.2 m a' x rest s₁ s' (ha.1 s m hp h₁) hb' h₂ hf)
    · cases c' with
      | nil =>
        simp only [List.append_nil] at ha'
        subst ha'
        exact .inr (hb.2 s₁ [] x rest s₁ s' (ha.1 s s₁ hp hd) (by simpa using hx.symm) (.nil s₁) hf)
      | cons y c'' =>
        simp only [List.cons_append, List.cons.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact .inl (ha.2 s done x c'' s₁ s' hp ha' hd hf)

theorem seg_mono {payload : List UInt8} {pre pre' post post' cut cut' : DirState → Prop}
    {seg : Trace} (h : Seg payload pre seg post cut) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s, post s → post' s) (hcut : ∀ s, cut s → cut' s) :
    Seg payload pre' seg post' cut' :=
  ⟨fun s s' hp hs => hpost s' (h.1 s s' (hpre s hp) hs), fun s done x rest s₁ s' hp he hd hf =>
    hcut s' (h.2 s done x rest s₁ s' (hpre s hp) he hd hf)⟩

theorem seg_each {payload : List UInt8} {seg : Trace} (P : DirState → Prop)
    (h : ∀ e ∈ seg, ∀ r s s', P s → Step payload s ⟨e.request, r⟩ s' → P s') :
    Seg payload P seg P P := by
  constructor
  · intro s s' hp hs
    exact steps_preserve P h hs hp
  · intro s done x rest s₁ s' hp he hd hf
    subst he
    have h₁ := steps_preserve P (fun e he => h e (List.mem_append_left _ he)) hd hp
    rcases hf with rfl | ⟨r, hr⟩
    · exact h₁
    · exact h x (List.mem_append_right _ (List.mem_cons_self ..)) r s₁ s' h₁ hr

/-- A segment whose calls never name `t` + never write keeps `t`'s file. -/
theorem seg_inert {payload : List UInt8} {seg : Trace} {t : String} (Φ : Option (List UInt8) → Prop)
    (h : ∀ e ∈ seg, ¬Names t e.request ∧ ∀ g o c, e.request ≠ .write g o c) :
    Seg payload (fun s => Φ (s.files t)) seg (fun s => Φ (s.files t)) (fun s => Φ (s.files t)) :=
  seg_each _ fun e he r s s' hp hs => by
    show Φ (s'.files t)
    rw [step_files_other hs (h e he).1 fun g o c hc => absurd hc ((h e he).2 g o c)]
    exact hp

/-! ### The protocol's segments -/

theorem retry_ok_last {request budget events n} (h : Retry request budget events (.ok n)) :
    ∃ pre, events = pre ++ [⟨request, .ok n⟩] ∧ ∀ e ∈ pre, e = ⟨request, .error 4⟩ := by
  generalize hr : Except.ok n = result at h
  induction h with
  | success =>
    cases hr; exact ⟨[], rfl, by simp⟩
  | failure => cases hr
  | exhausted => cases hr
  | interrupted _ ih =>
    obtain ⟨pre, rfl, hp⟩ := ih hr
    refine ⟨⟨request, .error 4⟩ :: pre, rfl, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact hp e he

theorem retry_head {request budget events result} (h : Retry request budget events result) :
    ∃ response rest, events = ⟨request, response⟩ :: rest := by
  cases h with
  | success => exact ⟨_, [], rfl⟩
  | failure => exact ⟨_, [], rfl⟩
  | exhausted => exact ⟨_, [], rfl⟩
  | interrupted => exact ⟨_, _, rfl⟩

theorem walk_requests {dir name pid n events result} (h : TempWalk dir name pid n events result) :
    ∀ e ∈ events, ∃ p m k, e.request = .create p m ∧ p.toString = tempText dir name pid k := by
  induction h with
  | created _ named _ attempt =>
    intro e he
    exact ⟨_, _, _, retry_requests attempt e he, named⟩
  | taken _ named _ attempt _ ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ⟨_, _, _, retry_requests attempt e he, named⟩
    · exact ih e he
  | failed _ named _ attempt _ =>
    intro e he
    exact ⟨_, _, _, retry_requests attempt e he, named⟩
  | allTaken => simp

theorem walk_ok {dir name pid n events temp fd}
    (h : TempWalk dir name pid n events (.ok (temp, fd))) :
    ∃ pre mode k,
      events = pre ++ [⟨.create temp mode, .ok fd⟩] ∧ temp.toString = tempText dir name pid k := by
  generalize hr : Except.ok (temp, fd) = result at h
  induction h with
  | created _ named _ attempt =>
    cases hr
    obtain ⟨pre, rfl, _⟩ := retry_ok_last attempt
    exact ⟨pre, _, _, rfl, named⟩
  | @taken n first rest result temp' mode' bound named perm attempt next
    ih =>
    obtain ⟨pre, mode, k, rfl, named⟩ := ih hr
    exact ⟨first ++ pre, mode, k, by simp, named⟩
  | failed => cases hr
  | allTaken => cases hr

theorem walk_inert {dir name pid n events result} (h : TempWalk dir name pid n events result) :
    ∀ e ∈ events, ¬Names (targetText dir name) e.request ∧ ∀ g o c, e.request ≠ .write g o c := by
  intro e he
  obtain ⟨p, m, k, hq, named⟩ := walk_requests h e he
  rw [hq]
  refine ⟨?_, fun _ _ _ => by simp⟩
  simp only [Names, named]
  exact tempText_ne dir name pid k

theorem unlinked_requests {temp e events e'} (h : Unlinked temp e events e') :
    ∀ x ∈ events, x.request = .unlink temp := by
  cases h with
  | removed attempt => exact retry_requests attempt
  | failed attempt => exact retry_requests attempt
  | interrupted attempt => exact retry_requests attempt

theorem abandoned_requests {temp fd e events e'} (h : Abandoned temp fd e events e') :
    ∀ x ∈ events, x.request = .close fd ∨ x.request = .unlink temp := by
  cases h with
  | closed unlink =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl rfl
    · exact .inr (unlinked_requests unlink x hx)
  | closeFailed unlink =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl rfl
    · exact .inr (unlinked_requests unlink x hx)

theorem directory_requests {path events result} (h : Directory path events result) :
    ∀ x ∈ events,
      x.request = .openDir path ∨ (∃ g, x.request = .fsync g) ∨ ∃ g, x.request = .close g := by
  cases h with
  | openFailed attempt => exact fun x hx => .inl (retry_requests attempt x hx)
  | opened opened synced =>
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | hx) | rfl
    · exact .inl (retry_requests opened x hx)
    · exact .inr (.inl ⟨_, retry_requests synced x hx⟩)
    · exact .inr (.inr ⟨_, rfl⟩)

theorem unlink_inert {dir name pid n} {temp : Path}
    (named : temp.toString = tempText dir name pid n) :
    ¬Names (targetText dir name) (.unlink temp) ∧ ∀ g o c, Request.unlink temp ≠ .write g o c := by
  refine ⟨?_, fun _ _ _ => by simp⟩
  simp only [Names, named]
  exact tempText_ne dir name pid n

theorem close_inert (t : String) (fd : Nat) :
    ¬Names t (.close fd) ∧ ∀ g o c, Request.close fd ≠ .write g o c :=
  ⟨by simp [Names], fun _ _ _ => by simp⟩

theorem fsync_inert (t : String) (fd : Nat) :
    ¬Names t (.fsync fd) ∧ ∀ g o c, Request.fsync fd ≠ .write g o c :=
  ⟨by simp [Names], fun _ _ _ => by simp⟩

theorem take_split (l : List UInt8) (o n r : Nat) (hn : n ≤ r) :
    (l.drop o).take n ++ (l.drop (o + n)).take (r - n) = (l.drop o).take r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = n + k := ⟨r - n, by omega⟩
  rw [List.take_add, List.drop_drop, Nat.add_sub_cancel_left]

theorem writes_requests {fd offset remaining events result}
    (h : Writes fd offset remaining events result) :
    ∀ e ∈ events, ∃ o c, e.request = .write fd o c := by
  induction h with
  | empty => simp
  | progress _ attempt _ _ _ ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ⟨_, _, retry_requests attempt e he⟩
    · exact ih e he
  | stalled _ attempt => exact fun e he => ⟨_, _, retry_requests attempt e he⟩
  | failed _ attempt => exact fun e he => ⟨_, _, retry_requests attempt e he⟩

/-- The data writes: the target kept, the temp's description kept, a complete success appends
the payload slice. -/
theorem writes_complete {payload : List UInt8} {fd offset remaining events result} {tp : String}
    (h : Writes fd offset remaining events result) :
    ∀ {s s' : DirState} (c : List UInt8),
      Steps payload s events s' →
        s.owners fd = some tp →
        s.files tp = some c →
        s'.owners fd = some tp ∧
          (result = .ok () → s'.files tp = some (c ++ (payload.drop offset).take remaining)) := by
  induction h with
  | empty =>
    intro s s' c hs ho hf
    cases hs
    exact ⟨ho, fun _ => by simp [hf]⟩
  | @progress offset remaining n first rest result nonempty attempt positive bounded tail
    ih =>
    intro s s' c hs ho hf
    obtain ⟨m, h₁, h₂⟩ := steps_append.mp hs
    obtain ⟨pre, rfl, hpre⟩ := retry_ok_last attempt
    obtain ⟨m₀, h₀, hl⟩ := steps_append.mp h₁
    have hm₀ : m₀ = s :=
      steps_same
        (fun e he s s' hs => by
          rw [hpre e he] at hs
          exact step_write_error hs)
        h₀
    subst hm₀
    cases hl with
    | cons head tail =>
      cases tail
      have hm := step_write_ok head ho
      subst hm
      have ⟨ho', hok⟩ :=
        ih (c ++ (payload.drop offset).take n) h₂ (by simpa using ho) (by simp [hf])
      refine ⟨ho', fun ok => ?_⟩
      rw [hok ok, List.append_assoc,
        take_split payload offset n remaining (Nat.le_trans bounded (Nat.min_le_left _ _))]
  | stalled nonempty attempt =>
    intro s s' c hs ho _
    refine ⟨?_, fun ok => by cases ok⟩
    exact
      steps_preserve (fun s => s.owners fd = some tp)
        (fun e he r s s' hp hs => by
          show s'.owners fd = some tp
          rw [retry_requests attempt e he] at hs
          rw [step_write_owners hs]
          exact hp)
        hs ho
  | failed nonempty attempt =>
    intro s s' c hs ho _
    refine ⟨?_, fun ok => by cases ok⟩
    exact
      steps_preserve (fun s => s.owners fd = some tp)
        (fun e he r s s' hp hs => by
          show s'.owners fd = some tp
          rw [retry_requests attempt e he] at hs
          rw [step_write_owners hs]
          exact hp)
        hs ho

theorem writes_seg {payload : List UInt8} {fd offset remaining events result} {t tp : String}
    (h : Writes fd offset remaining events result) (hne : tp ≠ t) (v : Option (List UInt8))
    (c : List UInt8) :
    Seg payload (fun s => s.files t = v ∧ s.owners fd = some tp ∧ s.files tp = some c) events
      (fun s =>
        s.files t = v ∧
          s.owners fd = some tp ∧
          (result = .ok () → s.files tp = some (c ++ (payload.drop offset).take remaining)))
      fun s => s.files t = v := by
  have keep :=
    seg_each (payload := payload) (seg := events) (fun s => s.files t = v ∧ s.owners fd = some tp)
      fun e he r s s' hp hs => by
      show s'.files t = v ∧ s'.owners fd = some tp
      obtain ⟨o, n, hq⟩ := writes_requests h e he
      rw [hq] at hs
      refine
        ⟨?_, by
          rw [step_write_owners hs]; exact hp.2⟩
      rw [step_files_other hs (by simp [Names]) fun g o' c' hw => by
          cases hw
          rw [hp.2]
          simpa using hne]
      exact hp.1
  refine
    ⟨fun s s' hp hs => ?_, fun s done x rest s₁ s' hp he hd hf =>
      (keep.2 s done x rest s₁ s' ⟨hp.1, hp.2.1⟩ he hd hf).1⟩
  have ⟨hv, _⟩ := keep.1 s s' ⟨hp.1, hp.2.1⟩ hs
  exact ⟨hv, writes_complete h c hs hp.2.1 hp.2.2⟩

/-- The rename step: the target holds its old state + the temp the payload, or the target holds
the payload + the temp is gone; a complete success ends in the latter. -/
def Renaming (payload : List UInt8) (v : Option (List UInt8)) (t tp : String) (s : DirState) :
    Prop := s.files t = v ∧ s.files tp = some payload ∨ s.files t = some payload ∧ s.files tp = none

theorem rename_keeps {payload : List UInt8} {v : Option (List UInt8)} {temp target : Path}
    (hne : temp.toString ≠ target.toString) {s s' : DirState} {response : Response}
    (h : Step payload s ⟨.rename temp target, response⟩ s')
    (hp : Renaming payload v target.toString temp.toString s) :
    Renaming payload v target.toString temp.toString s' := by
  rcases step_rename h with rfl | rfl
  · exact hp
  · rcases hp with ⟨_, hc⟩ | ⟨ht, hc⟩
    · exact .inr (move_present s hne hc)
    · rw [move_absent s hc]
      exact .inr ⟨ht, hc⟩

theorem rename_seg {payload : List UInt8} {v : Option (List UInt8)} {temp target : Path}
    {budget events result} (h : Retry (.rename temp target) budget events result)
    (hne : temp.toString ≠ target.toString) :
    Seg payload (Renaming payload v target.toString temp.toString) events
      (fun s =>
        Renaming payload v target.toString temp.toString s ∧
          ∀ n, result = .ok n → s.files target.toString = some payload)
      (Renaming payload v target.toString temp.toString) := by
  have pres :
    ∀ e ∈ events,
      ∀ r s s',
        Renaming payload v target.toString temp.toString s →
          Step payload s ⟨e.request, r⟩ s' → Renaming payload v target.toString temp.toString s' :=
    fun e he r s s' hp hs => by
    rw [retry_requests h e he] at hs
    exact rename_keeps hne hs hp
  have keep := seg_each (payload := payload) _ pres
  refine ⟨fun s s' hp hs => ⟨keep.1 s s' hp hs, fun n hn => ?_⟩, keep.2⟩
  subst hn
  obtain ⟨pre, hev, _⟩ := retry_ok_last h
  subst hev
  obtain ⟨m, h₁, h₂⟩ := steps_append.mp hs
  have hm := steps_preserve _ (fun e he => pres e (List.mem_append_left _ he)) h₁ hp
  cases h₂ with
  | cons head tail =>
    cases tail
    rw [step_rename_ok head]
    rcases hm with ⟨_, hc⟩ | ⟨ht, hc⟩
    · exact (move_present m hne hc).1
    · rw [move_absent m hc]
      exact ht

end FvdepAudit.Sys.Proof
