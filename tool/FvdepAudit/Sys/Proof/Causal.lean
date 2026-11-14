import FvdepAudit.Sys.Proof.Trace

/-! F4's model step, policy half (`Spec.Causal`): `pure`, one call + `bind` read their answers in
order, hence so does every policy function built from them (each loop by induction on its
measure) ⇒ `replace`. -/

namespace FvdepAudit.Sys.Proof

open FvdepIO.Sys FvdepIO.Sys.Model FvdepIO.Sys.Policy
open FvdepAudit.Sys.Spec

theorem map_range_add {β : Type} (s : Nat → β) (c d : Nat) :
    (List.range (c + d)).map s = (List.range c).map s ++ (List.range d).map fun n => s (n + c) := by
  induction d with
  | zero => simp
  | succ d ih =>
    simp only [← Nat.add_assoc, List.range_succ, List.map_append, ih, List.append_assoc,
      List.map_cons, List.map_nil, Nat.add_comm d c]

theorem _root_.FvdepAudit.Sys.Spec.Causal.length {α : Type} {m : ScriptIO α} (h : Causal m)
    (s : Script) : (m.run s).events.length = (m.run s).consumed := by
  simpa using congrArg List.length (h.recorded s)

theorem causal_pure {α : Type} (a : α) : Causal (pure a : ScriptIO α) where
  recorded _ := rfl
  settled _ _ _ _ _ := rfl
  requests _ _ _ _ := rfl

theorem causal_call (request : Request) : Causal (scripted.call request) where
  recorded _ := rfl
  settled s s' k agree within := by
    simp only [run_call] at within ⊢
    rw [agree 0 (by omega)]
  requests _ _ _ _ := by simp [run_call]

theorem causal_bind {α β : Type} {a : ScriptIO α} {f : α → ScriptIO β} (ha : Causal a)
    (hf : ∀ x, Causal (f x)) : Causal (a >>= f)
    where
  recorded s := by
    simp only [run_bind, List.map_append, ha.recorded s, (hf (a.run s).result).recorded,
      map_range_add]
  settled s s' k agree within := by
    simp only [run_bind] at within ⊢
    rw [ha.settled s s' k agree (by omega),
      (hf (a.run s).result).settled (fun n => s (n + (a.run s).consumed))
        (fun n => s' (n + (a.run s).consumed)) (k - (a.run s).consumed)
        (fun i hi => agree _ (by omega)) (by omega)]
  requests s s' k agree := by
    simp only [run_bind, List.take_append, List.map_append]
    by_cases hk : (a.run s).consumed ≤ k
    · rw [ha.settled s s' k agree hk, ha.length s,
        show k + 1 - (a.run s).consumed = k - (a.run s).consumed + 1 by omega,
        (hf (a.run s).result).requests (fun n => s (n + (a.run s).consumed))
          (fun n => s' (n + (a.run s).consumed)) (k - (a.run s).consumed)
          (fun i hi => agree _ (by omega))]
    · have hl : k + 1 ≤ (a.run s').consumed := by
        refine Classical.byContradiction fun hc => hk ?_
        have hc' : (a.run s').consumed ≤ k := by omega
        rw [ha.settled s' s k (fun i hi => (agree i hi).symm) hc']
        exact hc'
      rw [ha.length s', ha.length s, show k + 1 - (a.run s').consumed = 0 by omega,
        show k + 1 - (a.run s).consumed = 0 by omega, ha.requests s s' k agree]
      simp

theorem causal_retry (request : Request) (budget : Nat) :
    Causal (retry scripted request budget) := by
  induction budget with
  | zero =>
    rw [retry]
    refine causal_bind (causal_call request) fun r => ?_
    cases r <;> exact causal_pure _
  | succ budget ih =>
    rw [retry]
    refine causal_bind (causal_call request) fun r => ?_
    cases r with
    | ok => exact causal_pure _
    | error n =>
      show Causal (if n = eintr then _ else _)
      split
      · exact ih
      · exact causal_pure _

theorem causal_writes (fd offset remaining : Nat) :
    Causal (writes scripted fd offset remaining) := by
  induction remaining using Nat.strongRecOn generalizing offset with
  | ind remaining ih =>
    rw [writes]
    split
    · exact causal_pure _
    · refine causal_bind (causal_retry _ _) fun r => ?_
      rcases r with _ | (_ | n)
      · exact causal_pure _
      · exact causal_pure _
      · show Causal (if n + 1 ≤ min remaining maxChunk then _ else _)
        split
        · exact ih _ (by omega) _
        · exact causal_pure _

theorem causal_createTemp (dir : Path) (name : Name) (pid n : Nat) :
    Causal (createTemp scripted dir name pid n) := by
  generalize hd : tempTries - n = d
  induction d using Nat.strongRecOn generalizing n with
  | ind d ih =>
    rw [createTemp]
    split
    · refine causal_bind (causal_retry _ _) fun r => ?_
      cases r with
      | ok => exact causal_pure _
      | error cause =>
        show Causal (if cause = .errno eexist then _ else _)
        split
        · exact ih (tempTries - (n + 1)) (by omega) (n + 1) rfl
        · exact causal_pure _
    · exact causal_pure _

theorem causal_dropTemp (temp : Path) (e : SysError) : Causal (dropTemp scripted temp e) := by
  rw [dropTemp]
  refine causal_bind (causal_retry _ _) fun r => ?_
  cases r <;> exact causal_pure _

theorem causal_abandon (temp : Path) (fd : Nat) (e : SysError) :
    Causal (abandon scripted temp fd e) := by
  rw [abandon]
  exact causal_bind (causal_call _) fun _ => causal_dropTemp _ _

theorem causal_directory (path : Path) : Causal (directory scripted path) := by
  rw [directory]
  refine causal_bind (causal_retry _ _) fun r => ?_
  cases r with
  | error => exact causal_pure _
  | ok fd =>
    exact causal_bind (causal_retry _ _) fun _ => causal_bind (causal_call _) fun _ => causal_pure _

theorem causal_commit (dir : Path) (name : Name) (temp : Path) :
    Causal (commit scripted dir name temp) := by
  rw [commit]
  refine causal_bind (causal_retry _ _) fun r => ?_
  cases r with
  | error => exact causal_bind (causal_dropTemp _ _) fun _ => causal_pure _
  | ok =>
    refine causal_bind (causal_directory _) fun r => ?_
    cases r <;> exact causal_pure _

theorem causal_body (dir : Path) (name : Name) (size : Nat) (temp : Path) (fd : Nat) :
    Causal (body scripted dir name size temp fd) := by
  rw [body]
  refine causal_bind (causal_writes _ _ _) fun r => ?_
  cases r with
  | error => exact causal_bind (causal_abandon _ _ _) fun _ => causal_pure _
  | ok =>
    refine causal_bind (causal_retry _ _) fun r => ?_
    cases r with
    | error => exact causal_bind (causal_abandon _ _ _) fun _ => causal_pure _
    | ok =>
      refine causal_bind (causal_call _) fun r => ?_
      cases r with
      | error => exact causal_bind (causal_dropTemp _ _) fun _ => causal_pure _
      | ok => exact causal_commit _ _ _

theorem causal_replace (dir : Path) (name : Name) (pid size : Nat) :
    Causal (replace scripted dir name pid size) := by
  rw [replace]
  refine causal_bind (causal_createTemp _ _ _ _) fun r => ?_
  rcases r with _ | ⟨temp, fd⟩
  · exact causal_pure _
  · exact causal_body _ _ _ _ _

end FvdepAudit.Sys.Proof
