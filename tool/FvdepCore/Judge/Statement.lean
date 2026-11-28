import FvdepCore.Judge.Template
import FvdepCore.Judge.View

/-! U7 S (contract `docs/contracts/U7-judge.md` S1–S4): e2 holds the proof constant as a theorem
whose type is the template equation over e1's trusted constants — fn `@Eq.{u} T impl spec` (T =
the spec's type), abi `@Eq.{u} T impl (shape spec)` (T = the shape's codomain); u = the level the
proof's own `Eq` carries (the kernels pin it). One total order (S4): the trusted side's faults =
infrastructure, the rest = the solution's mismatch; the readers' refusals come first (J). Pure. -/

namespace FvdepCore.Judge

open FvdepCore.Export

/-- S's request (U3 T3's constant names) + its kind (Part B B7): `eq` = part A's (`impl` the
implementation, `abi` the ABI shape: shape `abi` alone); `prop` = an obligation, the proposition
`spec` (`impl` + `abi` unread); `compat` = the new spec `impl`, the old `spec` (`abi` unread). -/
structure Request where
  impl : Lean.Name
  spec : Lean.Name
  proof : Lean.Name
  abi : Option Lean.Name
  kind : Kind := .eq
  deriving DecidableEq, Repr

/-- A stage's outcome (S, G): the solution meets it, fails it, the trusted side broke (each with
its cause: J4's detail line), or the work budget ran out first (no verdict: J counts it a failure,
detail `the comparison passes its work budget`). -/
inductive Outcome where
  | matched
  | mismatch (cause : String)
  | infra (cause : String)
  | exhausted
  deriving DecidableEq, Repr

/-- A safe definition without level parameters: its type's index. -/
def safeType? : Option Entry → Option Nat
  | some (.defn _ _ [] _ .safe ty _) => some ty
  | _ => none

/-- Record `i`'s loose bound-variable range, its children's read from `r`. -/
def rangeOf (t : Tables) (r : Array Nat) (i : Nat) : Nat :=
  match t.rawExprs[i]? with
  | some (.bvar k) => k + 1
  | some (.app f a) => max (r.getD f 0) (r.getD a 0)
  | some (.lam _ ty b _) => max (r.getD ty 0) (r.getD b 0 - 1)
  | some (.forallE _ ty b _) => max (r.getD ty 0) (r.getD b 0 - 1)
  | some (.letE _ ty v b _) => max (max (r.getD ty 0) (r.getD v 0)) (r.getD b 0 - 1)
  | some (.proj _ _ e) => r.getD e 0
  | _ => 0

/-- Each expression's loose bound-variable range up to index `upto` (one pass: a record names
earlier records alone). -/
def bvarRanges (t : Tables) (upto : Nat) : Array Nat :=
  (List.range (upto + 1)).foldl (fun r i => r.push (rangeOf t r i)) #[]

/-- S2: an ABI shape's type, a closed nondependent arrow `A → B`: B's index. -/
def arrowCodomain? (t : Tables) (ty : Nat) : Option Nat :=
  match t.rawExprs[ty]? with
  | some (.forallE _ a b _) =>
    let r := bvarRanges t (max a b)
    if r.getD a 1 == 0 && r.getD b 1 == 0 then some b else none
  | _ => none

/-- A theorem's level parameters + type index. -/
def thmOf? : Entry → Option (List Nat × Nat)
  | .thm _ lps _ ty _ => some (lps, ty)
  | _ => none

/-- Record `i` of `t` is `const n []`, `n` naming `c`. -/
def constIs (t : Tables) (i : Nat) (c : Lean.Name) : Bool :=
  match t.rawExprs[i]? with
  | some (.const n []) => t.names[n]? == some c
  | _ => false

/-- S3: a type `@Eq.{u} a1 a2 a3` (one level): `(a1, a2, a3)`. -/
def eqParts? (t : Tables) (ty : Nat) : Option (Nat × Nat × Nat) :=
  match t.rawExprs[ty]? with
  | some (.app f3 a3) =>
    match t.rawExprs[f3]? with
    | some (.app f2 a2) =>
      match t.rawExprs[f2]? with
      | some (.app f1 a1) =>
        match t.rawExprs[f1]? with
        | some (.const n [_]) => if t.names[n]? == some `Eq then some (a1, a2, a3) else none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- S3's right side (record `i` of `t`): `spec` (fn, compat) or `shape spec` (abi). -/
def rhsIs (t : Tables) (i : Nat) (r : Request) : Bool :=
  if r.kind == .compat then constIs t i r.spec
  else
    match r.abi with
    | none => constIs t i r.spec
    | some s =>
      match t.rawExprs[i]? with
      | some (.app g x) => constIs t g s && constIs t x r.spec
      | _ => false

/-- Record `i` of `t` is `Sort 0`: a sort whose level record is the zero record (`none`; every
`LevelF` denotes a nonzero level). -/
def isProp (t : Tables) (i : Nat) : Bool :=
  match t.rawExprs[i]? with
  | some (.sort l) =>
    match t.rawLevels[l]? with
    | some none => true
    | _ => false
  | _ => false

/-- S's trusted side (S1 + S2): the target type T's index in e1, or the cause. -/
def target (v1 : View) (r : Request) : Except String Nat :=
  match v1.byName[r.spec]? with
  | none => .error s!"the trusted export lacks {r.spec}"
  | some e =>
    match safeType? (some e) with
    | none => .error s!"the statement form is outside v1: {r.spec}"
    | some specTy =>
      match r.abi with
      | none => .ok specTy
      | some s =>
        match v1.byName[s]? with
        | none => .error s!"the trusted export lacks {s}"
        | some e' =>
          match safeType? (some e') >>= arrowCodomain? v1.t with
          | none => .error s!"the statement form is outside v1: {s}"
          | some b => .ok b

/-- Part B's candidate roots in e1 (B7): T's index — `prop`: the obligation `spec` a safe
definition without level parameters of type `Prop`; `compat`: both specs safe definitions without
level parameters, T = the new spec's (`impl`'s) type — else the stage's outcome: an absent root =
infrastructure (B4 checked it present), a present root outside the kind's form = the statement's
mismatch (the candidate's own construction). -/
def roots (v1 : View) (r : Request) : Except Outcome Nat :=
  if r.kind == .prop then
    match v1.byName[r.spec]? with
    | none => .error (.infra s!"the trusted export lacks {r.spec}")
    | some e =>
      match safeType? (some e) with
      | none => .error (.mismatch (notProp r.spec))
      | some ty => if isProp v1.t ty then .ok ty else .error (.mismatch (notProp r.spec))
  else
    match v1.byName[r.impl]? with
    | none => .error (.infra s!"the trusted export lacks {r.impl}")
    | some en =>
      match v1.byName[r.spec]? with
      | none => .error (.infra s!"the trusted export lacks {r.spec}")
      | some eo =>
        match safeType? (some en) with
        | none => .error (.mismatch (notSafe r.impl))
        | some ty =>
          if (safeType? (some eo)).isNone then .error (.mismatch (notSafe r.spec)) else .ok ty
where
  notProp (n : Lean.Name) : String :=
    s!"the obligation {n} is not a safe definition of type Prop without level parameters"
  notSafe (n : Lean.Name) : String :=
    s!"the spec {n} is not a safe definition without level parameters"

/-- S4's first stages: T's index, else the stage's outcome — part A: the trusted side (`target`: a
fault = infrastructure), then the implementation a safe definition of e1 without level parameters
(else the solution's mismatch); part B: `roots`. -/
def front (v1 : View) (r : Request) : Except Outcome Nat :=
  if r.kind == .eq then
    match target v1 r with
    | .error why => .error (.infra why)
    | .ok tT =>
      match v1.byName[r.impl]? with
      | none => .error (.mismatch s!"the implementation {r.impl} is missing")
      | some e =>
        if (safeType? (some e)).isNone then
          .error
            (.mismatch
              s!"the implementation {r.impl} is not a safe definition without level parameters")
        else .ok tT
  else roots v1 r

/-- S4's solution side: e2's proof a theorem without level parameters whose name is no constant of
e1 — its type's index, else the mismatch's cause. -/
def solution (v1 v2 : View) (r : Request) : Except String Nat :=
  match v2.byName[r.proof]? with
  | none => .error s!"the solution lacks {r.proof}"
  | some p =>
    match thmOf? p with
    | none => .error s!"the proof {r.proof} is not a theorem"
    | some (lps, ty) =>
      if !lps.isEmpty then .error s!"the proof {r.proof} has level parameters"
      else
        if v1.byName.contains r.proof then
          .error s!"the proof's name {r.proof} is a trusted constant"
        else .ok ty

/-- S4 on two exports the reader accepted, the run's fuel + memo threaded on to G: `prop` = the
theorem's type the obligation constant itself; `eq` + `compat` = the equation, T compared by
`eqExpr`. -/
def statement (v1 v2 : View) (r : Request) (fuel : Nat) (seen : Std.HashSet Pair) :
    Outcome × Nat × Std.HashSet Pair :=
  match front v1 r with
  | .error o => (o, fuel, seen)
  | .ok tT =>
    match solution v1 v2 r with
    | .error why => (.mismatch why, fuel, seen)
    | .ok ty =>
      if r.kind == .prop then
        if constIs v2.t ty r.spec then (.matched, fuel, seen)
        else (.mismatch "the proof does not prove the required statement", fuel, seen)
      else
        match eqParts? v2.t ty with
        | none => (.mismatch "the proof's type is not an equation", fuel, seen)
        | some (a1, a2, a3) =>
          if !(constIs v2.t a2 r.impl && rhsIs v2.t a3 r) then
            (.mismatch "the proof does not prove the required statement", fuel, seen)
          else
            match eqExpr v1.t tT v2.t a1 fuel seen with
            | (.equal, f, s) => (.matched, f, s)
            | (.differ, f, s) => (.mismatch "the proof does not prove the required statement", f, s)
            | (.exhausted, f, s) => (.exhausted, f, s)

end FvdepCore.Judge
