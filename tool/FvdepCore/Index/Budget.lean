import FvdepCore.Index.Registry

/-! U7 Part B B5 (contract `docs/contracts/U7-judge.md`): the per-walk decode budget = U5b E5's
countdown extended with C2's read-through facts. A walk over candidate expressions (a registry
list's C2 decode, an entry's `ProofsAt` decode) runs under its own countdown: every node counted at
every use — a `let` value at each of its variables, an `<M>.entry` value or a registry-module
definition at each reference (once per path, as C2 unfolds: no DAG memo); past the budget the walk
is refused (the candidate's own construction), never a pass. Pure. -/

namespace FvdepCore.Index.Registry

open Lean

/-- The value the walk unfolds at `c` (C2's read-through facts: `rootDef?` ∪ `entryDef?`): a
definition of the registry module, or `<M>.entry` declared in `M` — `c` not being unfolded. -/
def unfold? (F : Facts) (p : List Name) (c : Name) : Option Expr :=
  valueOf? F p c fun d => d.module == rootModule || c == .str d.module "entry"

theorem unfold_fresh {F : Facts} {p : List Name} {c : Name} {x : Expr}
    (h : unfold? F p c = some x) : fresh F (c :: p) < fresh F p := valueOf_fresh h

/-- B5's countdown: `k` minus the walk's expanded size, or `none` past `k`. -/
def withinF (F : Facts) (k : Nat) (e : Expr) (env : List Expr) (p : List Name) : Option Nat :=
  match k with
  | 0 => none
  | k + 1 =>
    match e with
    | .mdata _ b => withinF F k b env p
    | .letE _ _ v b _ => withinF F k b (v :: env) p
    | .bvar i =>
      match hv : env[i]? with
      | some v =>
        have := env_le hv
        withinF F k v (env.drop (i + 1)) p
      | none => some k
    | .app f a =>
      match withinF F k f env p with
      | some k' => withinF F k' a env p
      | none => none
    | .const c _ =>
      match hu : unfold? F p c with
      | some v =>
        have := unfold_fresh hu
        withinF F k v [] (c :: p)
      | none => some k
    | _ => some k
termination_by (fresh F p, sizeOf e + envSize env)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; assumption)
    | (apply Prod.Lex.right; simp; omega)

end FvdepCore.Index.Registry
