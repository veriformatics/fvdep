import FvdepAudit.Registry.Spec

/-! U7 Part B B5's measure, written apart from the countdown: a walk's expanded size over C2's
read-through facts (`RootDef`, `EntryDef`: the registry module's definitions + `<M>.entry` values,
each unfolded once per path). -/

namespace FvdepAudit.Index.Budget.Spec

open Lean FvdepCore.Index.Registry

/-- The value the walk unfolds at `c` (`RootDef` or `EntryDef`, decided): `c` not being unfolded, a
definition named `c` declared in the registry module, or `c = <M>.entry` declared in `M`. -/
def unfoldS (F : Facts) (p : List Name) (c : Name) : Option Expr :=
  if c ∈ p then none
  else
    match F.decls.find? (·.name == c) with
    | some d =>
      if d.kind = .defn ∧ (d.module = `Fvdep.Registry ∨ c = .str d.module "entry") then d.value
      else none
    | none => none

theorem unfoldS_fresh {F : Facts} {p : List Name} {c : Name} {x : Expr}
    (h : unfoldS F p c = some x) : fresh F (c :: p) < fresh F p := by
  unfold unfoldS at h
  split at h
  · cases h
  · rename_i hp
    split at h
    · rename_i d hd
      have hmem := List.mem_of_find?_eq_some hd
      have hname : d.name = c := by simpa using List.find?_some hd
      unfold fresh
      apply filter_lt F.decls _ _ _ d hmem
      · simp [hname, hp]
      · simp [hname]
      · intro y _ hy
        simp only [List.mem_cons, not_or, decide_eq_true_eq] at hy ⊢
        exact hy.2
    · cases h

/-- B5: the walk's expanded size — every node counted at every use: a `let` value at each of its
variables, an unfolded value (`unfoldS`) at each reference. -/
def sizeF (F : Facts) (e : Expr) (env : List Expr) (p : List Name) : Nat :=
  match e with
  | .mdata _ b => 1 + sizeF F b env p
  | .letE _ _ v b _ => 1 + sizeF F b (v :: env) p
  | .bvar i =>
    match hv : env[i]? with
    | some v =>
      have := env_le hv
      1 + sizeF F v (env.drop (i + 1)) p
    | none => 1
  | .app f a => 1 + sizeF F f env p + sizeF F a env p
  | .const c _ =>
    match hu : unfoldS F p c with
    | some v =>
      have := unfoldS_fresh hu
      1 + sizeF F v [] (c :: p)
    | none => 1
  | _ => 1
termination_by (fresh F p, sizeOf e + envSize env)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; assumption)
    | (apply Prod.Lex.right; simp; omega)

end FvdepAudit.Index.Budget.Spec
