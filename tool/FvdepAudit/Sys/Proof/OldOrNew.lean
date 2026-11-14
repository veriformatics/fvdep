import FvdepAudit.Sys.Proof.Dir
import FvdepCore.Status

/-! F4 `ReplaceOldOrNew` + its bridge to U2 X4's `Holds`, over the directory model. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem unlinked_durability {temp e events e'} (h : Unlinked temp e events e') :
    e'.durability = e.durability := by cases h <;> rfl

theorem abandoned_durability {temp fd e events e'} (h : Abandoned temp fd e events e') :
    e'.durability = e.durability := by
  cases h with
  | closed u => exact unlinked_durability u
  | closeFailed u =>
    have h := unlinked_durability u
    exact h

theorem walk_error_durability {dir name pid n events e}
    (h : TempWalk dir name pid n events (.error e)) : e.durability = false := by
  generalize hr : Except.error e = result at h
  induction h with
  | created => cases hr
  | taken _ _ _ _ _ ih => exact ih hr
  | failed =>
    cases hr; rfl
  | allTaken =>
    cases hr; rfl

/-- A cut at or after a rename lies past `A ++ [y]`; with no rename in `done ++ [x]`, it lies in
`A`. -/
theorem cut_before {done rest A B : Trace} {x y : Event} (he : done ++ x :: rest = A ++ y :: B)
    (hy : ∃ src dst, y.request = .rename src dst) (hn : NoRename (done ++ [x])) :
    ∃ rest', A = done ++ x :: rest' := by
  obtain ⟨src, dst, hq⟩ := hy
  rcases List.append_eq_append_iff.mp he with ⟨a', hA, hx⟩ | ⟨c', hd, hy⟩
  · cases a' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hx
      exact absurd (hx.1 ▸ hq) (hn x (by simp) src dst)
    | cons z a'' =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, _⟩ := hx
      exact ⟨a'', hA⟩
  · cases c' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hy
      exact absurd (hy.1 ▸ hq) (hn x (by simp) src dst)
    | cons z c'' =>
      simp only [List.cons_append, List.cons.injEq] at hy
      obtain ⟨rfl, _⟩ := hy
      exact absurd hq (hn y (by simp [hd]) src dst)

/-- The run never passes a rename: the target keeps its state at every cut + at the end. -/
theorem finish_kept {payload : List UInt8} {ev : Trace} {s₀ : DirState} {t : String}
    {R : Except SysError Unit}
    (seg :
      Seg payload (fun s => s.files t = s₀.files t) ev (fun s => s.files t = s₀.files t) fun s =>
        s.files t = s₀.files t)
    (hR : ∀ e, R = .error e → e.durability = false) (hok : R ≠ .ok ()) :
    (∀ s,
        Steps payload s₀ ev s →
          OldOrNew payload s₀ s t ∧
            (R = .ok () → s.files t = some payload) ∧
            (∀ e, R = .error e → e.durability = true → s.files t = some payload) ∧
            (NoRename ev → s.files t = s₀.files t)) ∧
      ∀ done x rest s₁ s,
        ev = done ++ x :: rest →
          Steps payload s₀ done s₁ →
          InFlight payload s₁ x.request s →
          OldOrNew payload s₀ s t ∧ (NoRename (done ++ [x]) → s.files t = s₀.files t) := by
  constructor
  · intro s hs
    have hv := seg.1 s₀ s rfl hs
    refine ⟨.inl hv, fun h => absurd h hok, fun e he hd => ?_, fun _ => hv⟩
    rw [hR e he] at hd
    cases hd
  · intro done x rest s₁ s he hd hf
    have hv := seg.2 s₀ done x rest s₁ s rfl he hd hf
    exact ⟨.inl hv, fun _ => hv⟩

/-- The run passes the rename step: `A` (target kept, temp = payload at its end), the rename step,
then `C` (never names the target, never writes). -/
theorem finish_renamed {payload : List UInt8} {ev A C renamed : Trace} {s₀ : DirState} {t : String}
    {temp target : Path} {budget : Nat} {rr : Except Cause Nat} {R : Except SysError Unit}
    (hev : ev = A ++ renamed ++ C) (ht : target.toString = t)
    (segA :
      Seg payload (fun s => s.files t = s₀.files t) A
        (fun s => s.files t = s₀.files t ∧ s.files temp.toString = some payload) fun s =>
        s.files t = s₀.files t)
    (hren : Retry (.rename temp target) budget renamed rr) (hne : temp.toString ≠ t)
    (hC : ∀ e ∈ C, ¬Names t e.request ∧ ∀ g o c, e.request ≠ .write g o c)
    (hok : R = .ok () → ∃ n, rr = .ok n)
    (hdur : ∀ e, R = .error e → e.durability = true → ∃ n, rr = .ok n) :
    (∀ s,
        Steps payload s₀ ev s →
          OldOrNew payload s₀ s t ∧
            (R = .ok () → s.files t = some payload) ∧
            (∀ e, R = .error e → e.durability = true → s.files t = some payload) ∧
            (NoRename ev → s.files t = s₀.files t)) ∧
      ∀ done x rest s₁ s,
        ev = done ++ x :: rest →
          Steps payload s₀ done s₁ →
          InFlight payload s₁ x.request s →
          OldOrNew payload s₀ s t ∧ (NoRename (done ++ [x]) → s.files t = s₀.files t) := by
  subst ht
  subst hev
  have segR := rename_seg (payload := payload) (v := s₀.files target.toString) hren hne
  have segAR := seg_append (seg_mono segA (fun _ h => h) (fun _ h => .inl h) fun _ h => h) segR
  have renamingOk :
    ∀ s,
      Renaming payload (s₀.files target.toString) target.toString temp.toString s →
        OldOrNew payload s₀ s target.toString :=
    fun s h => by
    rcases h with ⟨h, _⟩ | ⟨h, _⟩
    · exact .inl h
    · exact .inr h
  obtain ⟨y, B, hy⟩ := retry_head hren
  have hasRename : ∃ src dst, (⟨.rename temp target, y⟩ : Event).request = .rename src dst :=
    ⟨temp, target, rfl⟩
  constructor
  · intro s hs
    obtain ⟨m, h₁, h₂⟩ := steps_append.mp hs
    have ⟨hm, hfin⟩ := segAR.1 s₀ m rfl h₁
    have hkeep := (seg_inert (payload := payload) (· = m.files target.toString) hC).1 m s rfl h₂
    refine ⟨?_, fun h => ?_, fun e he hd => ?_, fun hn => ?_⟩
    · show
        s.files target.toString = s₀.files target.toString ∨ s.files target.toString = some payload
      rw [hkeep]
      exact renamingOk m hm
    · obtain ⟨n, hn⟩ := hok h
      rw [hkeep]
      exact hfin n hn
    · obtain ⟨n, hn⟩ := hdur e he hd
      rw [hkeep]
      exact hfin n hn
    · subst hy
      exact absurd rfl (hn ⟨.rename temp target, y⟩ (by simp) temp target)
  · intro done x rest s₁ s he hd hf
    have segAll :=
      seg_append segAR
        (seg_mono
          (seg_inert (payload := payload) (fun c => c = s₀.files target.toString ∨ c = some payload)
            hC)
          (fun s h => renamingOk s h.1) (fun _ h => h) fun _ h => h)
    refine ⟨?_, fun hn => ?_⟩
    · rcases segAll.2 s₀ done x rest s₁ s rfl he hd hf with (h | h) | h
      · exact .inl h
      · exact renamingOk s h
      · exact h
    · subst hy
      obtain ⟨rest', hA⟩ :=
        cut_before (A := A) (B := B ++ C) (by simpa [List.append_assoc] using he.symm) hasRename hn
      exact segA.2 s₀ done x rest' s₁ s rfl hA hd hf

theorem walk_seg {payload : List UInt8} {dir : Path} {name : Name} {pid : Nat} {created : Trace}
    {temp : Path} {fd : Nat} (walk : TempWalk dir name pid 0 created (.ok (temp, fd)))
    (v : Option (List UInt8)) :
    Seg payload (fun s => s.files (targetText dir name) = v) created
      (fun s =>
        s.files (targetText dir name) = v ∧
          s.owners fd = some temp.toString ∧ s.files temp.toString = some [])
      fun s => s.files (targetText dir name) = v := by
  have inert := seg_inert (payload := payload) (· = v) (walk_inert walk)
  refine ⟨fun s s' hp hs => ⟨inert.1 s s' hp hs, ?_⟩, inert.2⟩
  obtain ⟨pre, mode, k, hcr, _⟩ := walk_ok walk
  subst hcr
  obtain ⟨m, _, h₂⟩ := steps_append.mp hs
  cases h₂ with
  | cons head tail =>
    cases tail
    rw [step_create_ok head]
    simp

theorem step_fsync {payload : List UInt8} {s s' : DirState} {g : Nat} {r : Response}
    (h : Step payload s ⟨.fsync g, r⟩ s') : s' = s := by
  cases h with
  | applied => cases r <;> rfl

theorem step_close_files {payload : List UInt8} {s s' : DirState} {g : Nat} {r : Response}
    (h : Step payload s ⟨.close g, r⟩ s') : s'.files = s.files := by
  cases h with
  | applied => cases r <;> rfl

theorem fsync_seg {payload : List UInt8} {fd budget events result} (P : DirState → Prop)
    (h : Retry (.fsync fd) budget events result) : Seg payload P events P P :=
  seg_each P fun e he r s s' hp hs => by
    rw [retry_requests h e he] at hs
    rw [step_fsync hs]
    exact hp

theorem close_seg {payload : List UInt8} (Φ : (String → Option (List UInt8)) → Prop) (fd : Nat)
    (r : Response) :
    Seg payload (fun s => Φ s.files) [⟨.close fd, r⟩] (fun s => Φ s.files) fun s => Φ s.files :=
  seg_each _ fun e he r' s s' hp hs => by
    simp only [List.mem_singleton] at he
    subst he
    show Φ s'.files
    rw [step_close_files hs]
    exact hp

theorem dir_inert {dir : Path} {events result} (name : Name) (h : Directory dir events result) :
    ∀ x ∈ events, ¬Names (targetText dir name) x.request ∧ ∀ g o c, x.request ≠ .write g o c := by
  intro x hx
  rcases directory_requests h x hx with hq | ⟨g, hq⟩ | ⟨g, hq⟩ <;> rw [hq]
  · refine ⟨?_, fun _ _ _ => by simp⟩
    simp only [Names]
    exact dir_ne_target dir name
  · exact fsync_inert _ g
  · exact close_inert _ g

theorem old_or_new_of {payload : List UInt8} {dir : Path} {name : Name} {pid : Nat} {ev : Trace}
    {R : Except SysError Unit} (hR : Replace dir name pid payload.length ev R) (s₀ : DirState) :
    (∀ s,
        Steps payload s₀ ev s →
          OldOrNew payload s₀ s (targetText dir name) ∧
            (R = .ok () → s.files (targetText dir name) = some payload) ∧
            (∀ e,
              R = .error e → e.durability = true → s.files (targetText dir name) = some payload) ∧
            (NoRename ev → s.files (targetText dir name) = s₀.files (targetText dir name))) ∧
      ∀ done x rest s₁ s,
        ev = done ++ x :: rest →
          Steps payload s₀ done s₁ →
          InFlight payload s₁ x.request s →
          OldOrNew payload s₀ s (targetText dir name) ∧
            (NoRename (done ++ [x]) →
              s.files (targetText dir name) = s₀.files (targetText dir name)) := by
  cases hR with
  | noTemp walk =>
    exact
      finish_kept
        (seg_inert (payload := payload) (· = s₀.files (targetText dir name)) (walk_inert walk))
        (fun e he => by
          cases he; exact walk_error_durability walk)
        (by simp)
  | @opened created rest temp fd result walk
    body =>
    obtain ⟨pre, mode, k, -, named⟩ := walk_ok walk
    have hne : temp.toString ≠ targetText dir name := by
      rw [named]
      exact tempText_ne dir name pid k
    have segW := walk_seg (payload := payload) walk (s₀.files (targetText dir name))
    have segWr := fun {written result} (data : Writes fd 0 payload.length written result) =>
      writes_seg (payload := payload) data hne (s₀.files (targetText dir name)) []
    have cleanInert :
      ∀ {e events e'},
        Abandoned temp fd e events e' →
          ∀ x ∈ events,
            ¬Names (targetText dir name) x.request ∧ ∀ g o c, x.request ≠ .write g o c :=
      fun clean x hx => by
      rcases abandoned_requests clean x hx with h | h <;> rw [h]
      · exact close_inert _ fd
      · exact unlink_inert named
    have unlinkInert :
      ∀ {e events e'},
        Unlinked temp e events e' →
          ∀ x ∈ events,
            ¬Names (targetText dir name) x.request ∧ ∀ g o c, x.request ≠ .write g o c :=
      fun clean x hx => by
      rw [unlinked_requests clean x hx]
      exact unlink_inert named
    cases body with
    | writeFailed data
      clean =>
      have seg :=
        seg_append (seg_append segW (segWr data))
          (seg_mono
            (seg_inert (payload := payload) (· = s₀.files (targetText dir name)) (cleanInert clean))
            (fun _ h => h.1) (fun _ h => h) fun _ h => h)
      have seg' :=
        seg_mono seg (fun _ h => h) (fun _ h => h) fun _ h => by
          rcases h with (h | h) | h <;> exact h
      simp only [List.append_assoc] at seg'
      exact
        finish_kept seg'
          (fun e he => by
            cases he; rw [abandoned_durability clean])
          (by simp)
    | syncFailed data sync
      clean =>
      have seg :=
        seg_append (seg_append (seg_append segW (segWr data)) (fsync_seg _ sync))
          (seg_mono
            (seg_inert (payload := payload) (· = s₀.files (targetText dir name)) (cleanInert clean))
            (fun _ h => h.1) (fun _ h => h) fun _ h => h)
      have seg' :=
        seg_mono seg (fun _ h => h) (fun _ h => h) fun _ h => by
          rcases h with ((h | h) | h) | h <;>
            first
            | exact h
            | exact h.1
      simp only [List.append_assoc] at seg' ⊢
      exact
        finish_kept seg'
          (fun e he => by
            cases he; rw [abandoned_durability clean])
          (by simp)
    | @closeFailed written synced cleanup n m e data sync
      clean =>
      have tailInert :
        ∀ x ∈ (⟨.close fd, .error n⟩ :: cleanup : Trace),
          ¬Names (targetText dir name) x.request ∧ ∀ g o c, x.request ≠ .write g o c := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact close_inert _ fd
        · exact unlinkInert clean x hx
      have seg :=
        seg_append (seg_append (seg_append segW (segWr data)) (fsync_seg _ sync))
          (seg_mono (seg_inert (payload := payload) (· = s₀.files (targetText dir name)) tailInert)
            (fun _ h => h.1) (fun _ h => h) fun _ h => h)
      have seg' :=
        seg_mono seg (fun _ h => h) (fun _ h => h) fun _ h => by
          rcases h with ((h | h) | h) | h <;>
            first
            | exact h
            | exact h.1
      simp only [List.append_assoc] at seg' ⊢
      exact
        finish_kept seg'
          (fun e' he => by
            cases he; rw [unlinked_durability clean])
          (by simp)
    | @closed written synced crest n m result data sync
      commit =>
      let PA : DirState → Prop := fun s =>
        s.files (targetText dir name) = s₀.files (targetText dir name) ∧
          s.files temp.toString = some payload
      have segA :
        Seg payload (fun s => s.files (targetText dir name) = s₀.files (targetText dir name))
          (created ++ written ++ synced ++ [⟨.close fd, .ok n⟩]) PA fun s =>
          s.files (targetText dir name) = s₀.files (targetText dir name) := by
        have seg :=
          seg_append
            (seg_append
              (seg_append segW
                (seg_mono (segWr data) (fun _ h => h)
                  (fun s h => (⟨h.1, by simpa using h.2.2 rfl⟩ : PA s)) fun _ h => h))
              (fsync_seg PA sync))
            (close_seg (payload := payload)
              (fun f =>
                f (targetText dir name) = s₀.files (targetText dir name) ∧
                  f temp.toString = some payload)
              fd (.ok n))
        exact
          seg_mono seg (fun _ h => h) (fun _ h => h) fun _ h => by
            rcases h with ((h | h) | h) | h <;>
              first
              | exact h
              | exact h.1
      cases commit with
      | renameFailed namedT attempt clean =>
        exact
          finish_renamed (by simp) namedT segA attempt hne (unlinkInert clean) (fun h => by cases h)
            fun e he _ => by
            cases he
            rw [unlinked_durability clean] at *
            contradiction
      | unsynced namedT attempt flush =>
        exact
          finish_renamed (by simp) namedT segA attempt hne (dir_inert name flush)
            (fun h => by cases h) fun _ _ _ => ⟨_, rfl⟩
      | replaced namedT attempt flush =>
        exact
          finish_renamed (by simp) namedT segA attempt hne (dir_inert name flush)
            (fun _ => ⟨_, rfl⟩) fun _ he _ => by cases he

end FvdepAudit.Sys.Proof
