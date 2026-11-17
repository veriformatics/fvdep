import FvdepAudit.Sandbox.Spec

/-! Proofs of the sandbox claims (contract `docs/contracts/U5-sandbox.md` R1 + R6; statements =
`FvdepLedger.Rows.SandboxClaims`). -/

namespace FvdepAudit.Sandbox.Proof

open FvdepCore.Sandbox FvdepAudit.Sandbox.Spec

theorem parseNat_num (n : Nat) : FvdepCore.Ids.parseNat (num n).toList = some n := by
  simp [num, String.toList_ofList, FvdepCore.Ids.parseNat_decimal]

/-- bwrap reads one operation's arguments back as that operation, then the rest. -/
theorem readOps_render (o : Op) (r : List String) (acc : List Op) :
    readOps (o.render ++ r) acc = readOps r (o :: acc) := by
  cases o <;> simp [Op.render, readOps, parseNat_num]

theorem readOps_flatMap (os : List Op) (r : List String) (acc : List Op) :
    readOps (os.flatMap Op.render ++ r) acc = readOps r (os.reverse ++ acc) := by
  induction os generalizing acc with
  | nil => simp
  | cons o os ih => simp [List.flatMap_cons, List.append_assoc, readOps_render, ih]

/-- R1: bwrap reads `bwrapArgs s` as exactly `ops s`, then the helper + the step's argv verbatim. -/
theorem bwrapArgs_read (s : Spec) : bwrapRead (bwrapArgs s) = some (ops s, helper :: s.argv) := by
  simp [bwrapRead, bwrapArgs, readOps_flatMap, readOps]

theorem filter_const_false {α : Type} (l : List α) : l.filter (fun _ => false) = [] :=
  List.filter_eq_nil_iff.mpr (by simp)

theorem filter_const_true {α : Type} (l : List α) : l.filter (fun _ => true) = l :=
  List.filter_eq_self.mpr (by simp)

/-- R1 (f): the storage the sandbox keeps writable = the two sized tmpfs, at `/fvdep/work` + `/tmp`.
-/
theorem ops_writable (s : Spec) :
    (ops s).filter writableStorage =
      [.sizedTmpfs s.workBytes "/fvdep/work", .sizedTmpfs s.tmpBytes "/tmp"] := by
  simp [ops, isolation, envOps, mounts, finish, writableStorage, List.filter_map, Function.comp_def,
    List.filter_cons, filter_const_false]

/-- R1 (c): the environment operations = clear, then exactly the spec's variables in order. -/
theorem ops_env (s : Spec) :
    (ops s).filter isEnv = .clearenv :: s.env.map fun e => .setenv e.1 e.2 := by
  simp [ops, isolation, envOps, mounts, finish, isEnv, List.filter_map, Function.comp_def,
    List.filter_cons, filter_const_false, filter_const_true]

/-- R1 (f): the operations end with `/` + `/dev` remounted read-only, the cwd + the status
descriptor; no mount follows the remounts. -/
theorem ops_finish (s : Spec) :
    ∃ pre,
      ops s = pre ++ [.remountRo "/", .remountRo "/dev", .chdir "/fvdep/src", .jsonStatusFd 3] ∧
        ∀ o ∈ pre, ∀ d, o ≠ .remountRo d := by
  refine ⟨isolation ++ envOps s ++ mounts s, by simp [ops, finish], ?_⟩
  intro o ho d hod
  subst hod
  simp [isolation, envOps, mounts] at ho

theorem mount_path_layout (m : Mount) : m.path ∈ layout := by cases m <;> simp [Mount.path, layout]

/-- Every destination `o` names lies in the layout. -/
def destOk (o : Op) : Bool := (dest? o).all fun d => decide (d ∈ layout)

/-- R1 (e): every destination an operation names lies in the layout. -/
theorem ops_dest (s : Spec) : ∀ o ∈ ops s, ∀ d, dest? o = some d → d ∈ layout := by
  have h : (ops s).all destOk = true := by
    simp [ops, isolation, envOps, mounts, finish, List.all_append, List.all_map, destOk, dest?,
      layout, Function.comp_def]
    intro _ m _
    cases m <;> simp [Mount.path]
  intro o ho d hd
  have := (List.all_eq_true.mp h) o ho
  simp [destOk, hd] at this
  exact this

/-- R6: the outcome precedence. -/
theorem classify_exact (lines : List StatusLine) (killed : Bool) (e : String) :
    (∀ n, classify lines killed e = .exited n ↔ lines.filterMap exitCodeOf = [n]) ∧
      (classify lines killed e = .protocol ↔ 2 ≤ (lines.filterMap exitCodeOf).length) ∧
      (classify lines killed e = .timedOut ↔ lines.filterMap exitCodeOf = [] ∧ killed = true) ∧
      ∀ d,
        classify lines killed e = .setupFailed d ↔
          lines.filterMap exitCodeOf = [] ∧ killed = false ∧ d = e := by
  unfold classify
  cases h : lines.filterMap exitCodeOf with
  | nil => cases killed <;> simp [eq_comm]
  | cons n t =>
    cases t with
    | nil => simp
    | cons m t => simp

end FvdepAudit.Sandbox.Proof
