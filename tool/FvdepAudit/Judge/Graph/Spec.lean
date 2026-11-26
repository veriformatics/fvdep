import FvdepAudit.Judge.Statement.Spec
import FvdepCore.Judge.Axioms
import FvdepCore.Judge.Graph

/-! Specs for the graph + axiom steps (contract `docs/contracts/U7-judge.md` G1–G6, A1–A2), written
from the contract apart from `FvdepCore.Judge.{Graph,Axioms}`'s code, over the exports' denoted
tables (left = the trusted export). G1's root inventory = reviewed data (`graphRoots`). -/

namespace FvdepAudit.Judge.Graph.Spec

open FvdepCore.Export FvdepCore.Judge FvdepAudit.Judge.Spec FvdepAudit.Judge.Statement.Spec

/-- G2: an expression's constants (Lean's `getUsedConstants`: every `const`'s name, every `proj`'s
structure name). -/
def exprConsts : Lean.Expr → List Lean.Name
  | .const c _ => [c]
  | .proj s _ e => s :: exprConsts e
  | .app f a => exprConsts f ++ exprConsts a
  | .lam _ t b _ => exprConsts t ++ exprConsts b
  | .forallE _ t b _ => exprConsts t ++ exprConsts b
  | .letE _ t v b _ => exprConsts t ++ exprConsts v ++ exprConsts b
  | .mdata _ e => exprConsts e
  | _ => []

/-- A constant of expression `i` of `t`. -/
def ConstOf (t : Tables) (i : Nat) (c : Lean.Name) : Prop :=
  ∃ x, t.exprs[i]? = some x ∧ c ∈ exprConsts x

/-- G2: `c` is a use of constant `e` of `t` (Lake's `runForUsedConsts`: the type + value, an
inductive's constructors + `all`, a constructor's inductive, a recursor's rule constructors +
right sides). -/
def Uses (t : Tables) : Entry → Lean.Name → Prop
  | .axiom _ _ _ ty, c => ConstOf t ty c
  | .defn _ _ _ _ _ ty v, c => ConstOf t ty c ∨ ConstOf t v c
  | .thm _ _ _ ty v, c => ConstOf t ty c ∨ ConstOf t v c
  | .opaque _ _ _ _ ty v, c => ConstOf t ty c ∨ ConstOf t v c
  | .quot _ _ _ ty, c => ConstOf t ty c
  | .induct x, c => ConstOf t x.type c ∨ ∃ i ∈ x.ctors ++ x.all, t.names[i]? = some c
  | .ctor k, c => ConstOf t k.type c ∨ t.names[k.induct]? = some c
  | .recursor r, c =>
    ConstOf t r.type c ∨ ∃ q ∈ r.rules, t.names[q.ctor]? = some c ∨ ConstOf t q.rhs c

/-- G3: the names `t` reaches from `roots` through its constants' uses. -/
inductive Reach (t : Tables) (roots : List Lean.Name) : Lean.Name → Prop
  | root (c : Lean.Name) : c ∈ roots → Reach t roots c
  |
  use (c c' : Lean.Name) (e : Entry) :
    Reach t roots c → Named t c e → Uses t e c' → Reach t roots c'

/-- G3: every name e1 reaches from G1's roots is a constant of e1 + of e2, field for field. -/
def GraphHolds (t1 t2 : Tables) (r : Request) : Prop :=
  ∀ c, Reach t1 (graphRoots r) c → ∃ e1 e2, Named t1 c e1 ∧ Named t2 c e2 ∧ EntryEq t1 t2 e1 e2

/-- G5: no `opaque` constant e1 reaches outside the reviewed list. -/
def OpaqueHolds (t1 : Tables) (r : Request) (opaques : List Lean.Name) : Prop :=
  ∀ c,
    Reach t1 (graphRoots r) c →
      ∀ all u lps i ty v, Named t1 c (.opaque all u lps i ty v) → c ∈ opaques

/-- G6: every name the proof reaches in e2 is a constant of e2. -/
def ProofHolds (t2 : Tables) (r : Request) : Prop := ∀ c, Reach t2 [r.proof] c → ∃ e, Named t2 c e

/-- G6: an axiom the proof reaches in e2. -/
def ReachedAxiom (t2 : Tables) (r : Request) (c : Lean.Name) : Prop :=
  Reach t2 [r.proof] c ∧ ∃ u lps i ty, Named t2 c (.axiom u lps i ty)

end FvdepAudit.Judge.Graph.Spec
