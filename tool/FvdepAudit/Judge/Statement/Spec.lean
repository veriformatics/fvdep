import FvdepAudit.Judge.Spec
import FvdepCore.Judge.Statement

/-! Specs for the statement step (contract `docs/contracts/U7-judge.md` S1–S4), written from the
contract apart from `FvdepCore.Judge.Statement`'s code, over the two exports' denoted tables (left
= the trusted export). -/

namespace FvdepAudit.Judge.Statement.Spec

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules FvdepAudit.Judge.Spec

/-- X6: `e` is one of declaration record `d`'s constants, every field as the record gives it: a
single declaration's own fields; an inductive block's type, constructor or recursor record. -/
def EntryOf : DeclF → Entry → Prop
  | .axiom u lps n ty, e => e = .axiom u lps n ty
  | .defn all h lps n s ty v, e => e = .defn all h lps n s ty v
  | .thm all lps n ty v, e => e = .thm all lps n ty v
  | .opaque all u lps n ty v, e => e = .opaque all u lps n ty v
  | .quot q lps n ty, e => e = .quot q lps n ty
  | .induct cs rs ts, e =>
    (∃ x ∈ ts, e = .induct x) ∨ (∃ c ∈ cs, e = .ctor c) ∨ ∃ r ∈ rs, e = .recursor r

/-- A constant of `t` named `n`: one of a read declaration record's constants (X6), its name record
denoting `n` (X8: at most one per name). -/
def Named (t : Tables) (n : Lean.Name) (e : Entry) : Prop :=
  (∃ d ∈ t.rawDecls.toList, EntryOf d e) ∧ t.names[e.name]? = some n

/-- S1: a safe definition of `t` without level parameters, named `n`, of type `T`. -/
def SafeDefn (t : Tables) (n : Lean.Name) (T : Lean.Expr) : Prop :=
  ∃ all h i ty v, Named t n (.defn all h [] i .safe ty v) ∧ t.exprs[ty]? = some T

/-- S2 + S3's closedness: no loose bound variable under `d` binders, no free variable or
metavariable. -/
def Closed : Lean.Expr → Nat → Prop
  | .bvar k, d => k < d
  | .fvar _, _ => False
  | .mvar _, _ => False
  | .app f a, d => Closed f d ∧ Closed a d
  | .lam _ t b _, d => Closed t d ∧ Closed b (d + 1)
  | .forallE _ t b _, d => Closed t d ∧ Closed b (d + 1)
  | .letE _ t v b _, d => Closed t d ∧ Closed v d ∧ Closed b (d + 1)
  | .mdata _ e, d => Closed e d
  | .proj _ _ e, d => Closed e d
  | _, _ => True

/-- S1 + S2, the trusted side: the template's type `T` — the spec's type (fn), or the codomain of
the ABI shape's type, a closed nondependent arrow `A → T` (abi); the spec + the shape safe
definitions of e1 without level parameters. Part B: an obligation (`prop`) = the proposition `spec`
a safe level-free definition of type `T = Prop`; a compat = `T` the new spec's (`impl`'s) type,
both specs safe level-free definitions. -/
def Target (t1 : Tables) (r : Request) (T : Lean.Expr) : Prop :=
  if r.kind = .prop then SafeDefn t1 r.spec T ∧ T = .sort .zero
  else
    if r.kind = .compat then SafeDefn t1 r.impl T ∧ ∃ S, SafeDefn t1 r.spec S
    else
      match r.abi with
      | none => SafeDefn t1 r.spec T
      | some s =>
        (∃ S, SafeDefn t1 r.spec S) ∧
          ∃ n A bi, SafeDefn t1 s (.forallE n A T bi) ∧ Closed A 0 ∧ Closed T 0

/-- S3: the template `@Eq.{u} T impl spec` (fn) / `@Eq.{u} T impl (shape spec)` (abi); Part B
(B7): an obligation's (`prop`) = the proposition constant itself, a compat's = `@Eq.{u} T new old`
(`impl` = new, `spec` = old; no ABI shape). -/
def template (r : Request) (T : Lean.Expr) (u : Lean.Level) : Lean.Expr :=
  if r.kind = .prop then .const r.spec []
  else
    .app (.app (.app (.const `Eq [u]) T) (.const r.impl []))
      (if r.kind = .compat then .const r.spec []
      else
        match r.abi with
        | none => .const r.spec []
        | some s => .app (.const s []) (.const r.spec []))

/-- S4's trusted data, whose absence = infrastructure: part A = a target type (every trusted-side
fault); Part B (B7) = the kind's roots present in e1 (`prop`: `spec`; `compat`: `impl` + `spec`) —
a present root of an unsupported form is the statement's mismatch. -/
def Trusted (t1 : Tables) (r : Request) : Prop :=
  if r.kind = .eq then ∃ T, Target t1 r T
  else (∃ e, Named t1 r.spec e) ∧ (r.kind = .compat → ∃ e, Named t1 r.impl e)

/-- S4: the template holds — the trusted side's `T`, the implementation a safe definition of e1
without level parameters (part A's kind `eq`), the proof's name no constant of e1, and e2's proof a
theorem without level parameters whose type is the template up to U4's alpha-equivalence, for the
level `u` its `Eq` carries. -/
def Holds (t1 t2 : Tables) (r : Request) : Prop :=
  ∃ T,
    Target t1 r T ∧
      (r.kind = .eq → ∃ I, SafeDefn t1 r.impl I) ∧
      (∀ e, ¬Named t1 r.proof e) ∧
      ∃ all i ty v P u,
        Named t2 r.proof (.thm all [] i ty v) ∧
          t2.exprs[ty]? = some P ∧ alphaEq (template r T u) P = true

end FvdepAudit.Judge.Statement.Spec
