import FvdepAudit.Sys.Proof.Lock
import FvdepAudit.Sys.Proof.Read
import FvdepAudit.Sys.Proof.Touch

/-! F4 `SysClaims`: the theorems the coverage ledger credits; each header = its ledger statement.
fvapi's five claims, per operation: `NoFalseSuccess` + `ErrorExact` + `RetryBounded` =
`create_exact`, `writer_exact`, `directory_exact` (the result = the one the spec relation assigns
to the calls, ok + error alike) + `write_acknowledged` + `retry_bounded`; `CloseOnce` =
`close_once_actions`, `close_once_directory`; `SameDescription` = `same_description`. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem create_exact (path : Path) (mode : Mode) (script : Script) (r : Except SysError Nat) :
    ((create scripted path mode).run script).result = r ↔
      Create path mode ((create scripted path mode).run script).events r := by
  constructor
  · intro h
    rw [← h]
    exact create_sound path mode script
  · exact create_unique (create_sound path mode script)

theorem writer_exact (owned : WriterState) (action : WriterAction) (script : Script)
    (hc : Consistent ((writer scripted owned action).run script).events) (r : Except SysError Nat) :
    ((writer scripted owned action).run script).result = r ↔
      WriterOperation owned action ((writer scripted owned action).run script).events r := by
  constructor
  · intro h
    rw [← h]
    exact writer_sound owned action script hc
  · exact writer_unique (writer_sound owned action script hc)

theorem directory_exact (path : Path) (script : Script) (r : Except SysError Nat) :
    ((directory scripted path).run script).result = r ↔
      Directory path ((directory scripted path).run script).events r := by
  constructor
  · intro h
    rw [← h]
    exact directory_sound path script
  · exact directory_unique (directory_sound path script)

theorem write_acknowledged (owned : WriterState) (size : Nat) (script : Script) (n : Nat)
    (hc : Consistent ((writer scripted owned (.write size)).run script).events)
    (ok : ((writer scripted owned (.write size)).run script).result = .ok n) :
    acknowledged ((writer scripted owned (.write size)).run script).events = size :=
  operation_write_acknowledged (writer_sound owned (.write size) script hc) ok

theorem retry_bounded :
    (∀ (request : Request) (budget : Nat) (events : Trace) (result : Except Cause Nat),
        Retry request budget events result → events.length ≤ budget + 1) ∧
      (∀ request : Request,
        Retry request 64 (List.replicate 65 ⟨request, .error 4⟩) (.error .retryExhausted)) ∧
      ∀ (request : Request) (budget : Nat) (events : Trace) (result : Except Cause Nat),
        Retry request budget events result → ∀ e ∈ events, e.request = request :=
  ⟨fun _ _ _ _ h => retry_length h, fun request => retry_exhaustion request 64, fun _ _ _ _ h =>
    retry_requests h⟩

theorem close_once_actions (owned : WriterState) (steps : List WriterAction) (script : Script)
    (hc : Consistent ((actions scripted owned steps).run script).events) :
    closeCount ((actions scripted owned steps).run script).events ≤ if owned.closed then 0 else 1 :=
  writer_trace_close_count (actions_sound owned steps script hc)

theorem close_once_directory (path : Path) (script : Script) :
    closeCount ((directory scripted path).run script).events ≤ 1 ∧
      ((∃ e ∈ ((directory scripted path).run script).events,
          ∃ fd, e.request = .openDir path ∧ e.response = .ok fd) →
        closeCount ((directory scripted path).run script).events = 1) :=
  ⟨directory_close_count (directory_sound path script),
    directory_opened_close (directory_sound path script)⟩

theorem same_description (owned : WriterState) (action : WriterAction) (script : Script)
    (hc : Consistent ((writer scripted owned action).run script).events) :
    writerOnly owned.fd ((writer scripted owned action).run script).events ∧
      (owned.closed = true → ((writer scripted owned action).run script).events = []) := by
  have h := writer_sound owned action script hc
  exact ⟨operation_owned h, operation_closed_empty h⟩

/-- F4 `ReplaceOldOrNew` over the directory model, absent + present targets alike. -/
theorem replace_old_or_new (dir : Path) (name : Name) (pid : Nat) (payload : List UInt8)
    (script : Script) (s₀ : DirState) (run : Recorded (Except SysError Unit))
    (hrun : run = (replace scripted dir name pid payload.length).run script)
    (hc : Consistent run.events) :
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
              s.files (targetText dir name) = s₀.files (targetText dir name)) := by
  subst hrun
  exact old_or_new_of (replace_sound dir name pid payload.length script hc) s₀

/-- F4: `ReplaceOldOrNew`'s bridge to U2 X4's `Holds` for a present target. -/
theorem replace_holds (dir : Path) (name : Name) (pid : Nat) (payload old : List UInt8)
    (script : Script) (s₀ : DirState) (f : FvdepCore.ProjectFile)
    (run : Recorded (Except SysError Unit))
    (hrun : run = (replace scripted dir name pid payload.length).run script)
    (hc : Consistent run.events) (hold : s₀.files (targetText dir name) = some old) :
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
                [(.replace f (bytesOf payload), .replace (.error msg))] (bytesOf c) := by
  have h := replace_old_or_new dir name pid payload script s₀ run hrun hc
  have keepOrLand :
    ∀ c msg,
      (c = old ∨ c = payload) →
        FvdepCore.Status.Holds f (bytesOf old)
          [(.replace f (bytesOf payload), .replace (.error msg))] (bytesOf c) := by
    rintro c msg (rfl | rfl)
    · exact .keep _ _ msg [] _ (.done _)
    · exact .land _ _ msg [] _ (.done _)
  have value :
    ∀ s,
      OldOrNew payload s₀ s (targetText dir name) →
        ∃ c, s.files (targetText dir name) = some c ∧ (c = old ∨ c = payload) := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨old, hs.trans hold, .inl rfl⟩
    · exact ⟨payload, hs, .inr rfl⟩
  constructor
  · intro s hs
    obtain ⟨hon, hok, -, -⟩ := h.1 s hs
    obtain ⟨c, hc', hco⟩ := value s hon
    refine ⟨c, hc', fun hr => ?_, fun e msg _ => keepOrLand c msg hco⟩
    have hp := hok hr
    rw [hc'] at hp
    cases hp
    exact .ok _ _ [] _ (.done _)
  · intro done x rest s₁ s msg he hd hf
    obtain ⟨c, hc', hco⟩ := value s (h.2 done x rest s₁ s he hd hf).1
    exact ⟨c, hc', keepOrLand c msg hco⟩

/-- F4 `ReplaceExact`: a run's calls + result follow F2's protocol written apart (`Replace`),
which fixes the result from the calls. -/
theorem replace_exact (dir : Path) (name : Name) (pid size : Nat) (script : Script)
    (r : Except SysError Unit)
    (hc : Consistent ((replace scripted dir name pid size).run script).events) :
    ((replace scripted dir name pid size).run script).result = r ↔
      Replace dir name pid size ((replace scripted dir name pid size).run script).events r :=
  replace_exact_script dir name pid size script r hc

/-- F2 `readFile` (beyond F4's list): the calls + result follow the protocol written apart. -/
theorem read_exact (path : Path) (cap : Nat) (script : Script) (r : Except SysError (Option Nat))
    (hc : Consistent ((readFile scripted path cap).run script).events) :
    ((readFile scripted path cap).run script).result = r ↔
      ReadFile path cap ((readFile scripted path cap).run script).events r :=
  read_exact_script path cap script r hc

/-- F4 `LockExact` over the script monad. -/
theorem lock_exact {α : Type} (dir : Path) (act : ScriptIO α) (script : Script)
    (r : Except SysError α) :
    ((withLock scripted dir act).run script).result = r ↔
      Lock dir act script ((withLock scripted dir act).run script).events r :=
  lock_exact_script dir act script r

end FvdepAudit.Sys.Proof
