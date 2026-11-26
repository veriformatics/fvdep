import FvdepCore.Judge.View

/-! U7 S (contract `docs/contracts/U7-judge.md` S1–S4): e2 holds the proof constant as a theorem
whose type is the template equation over e1's trusted constants — fn `@Eq.{u} T impl spec` (T =
the spec's type), abi `@Eq.{u} T impl (shape spec)` (T = the shape's codomain); u = the level the
proof's own `Eq` carries (the kernels pin it). One total order (S4): the trusted side's faults =
infrastructure, the rest = the solution's mismatch; the readers' refusals come first (J). Pure. -/

namespace FvdepCore.Judge

open FvdepCore.Export

/-- S's request (U3 T3's constant names); `abi` = the ABI shape constant (shape `abi` alone). -/
structure Request where
  impl : Lean.Name
  spec : Lean.Name
  proof : Lean.Name
  abi : Option Lean.Name
  deriving DecidableEq, Repr

/-- A stage's outcome (S, G): the solution meets it, fails it, or the trusted side broke; each
with its cause (J4's detail line). -/
inductive Outcome where
  | matched
  | mismatch (cause : String)
  | infra (cause : String)
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

/-- S3's right side (record `i` of `t`): `spec` (fn) or `shape spec` (abi). -/
def rhsIs (t : Tables) (i : Nat) (r : Request) : Bool :=
  match r.abi with
  | none => constIs t i r.spec
  | some s =>
    match t.rawExprs[i]? with
    | some (.app g x) => constIs t g s && constIs t x r.spec
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

/-- S4 on two exports the reader accepted, the run's fuel + memo threaded on to G. -/
def statement (v1 v2 : View) (r : Request) (fuel : Nat) (seen : Std.HashSet Pair) :
    Outcome × Nat × Std.HashSet Pair :=
  match target v1 r with
  | .error why => (.infra why, fuel, seen)
  | .ok tT =>
    match v1.byName[r.impl]? with
    | none => (.mismatch s!"the implementation {r.impl} is missing", fuel, seen)
    | some e =>
      if (safeType? (some e)).isNone then
        (.mismatch
            s!"the implementation {r.impl} is not a safe definition without level parameters",
          fuel, seen)
      else
        match v2.byName[r.proof]? with
        | none => (.mismatch s!"the solution lacks {r.proof}", fuel, seen)
        | some p =>
          match thmOf? p with
          | none => (.mismatch s!"the proof {r.proof} is not a theorem", fuel, seen)
          | some (lps, ty) =>
            if !lps.isEmpty then
              (.mismatch s!"the proof {r.proof} has level parameters", fuel, seen)
            else
              if v1.byName.contains r.proof then
                (.mismatch s!"the proof's name {r.proof} is a trusted constant", fuel, seen)
              else
                match eqParts? v2.t ty with
                | none => (.mismatch "the proof's type is not an equation", fuel, seen)
                | some (a1, a2, a3) =>
                  if !(constIs v2.t a2 r.impl && rhsIs v2.t a3 r) then
                    (.mismatch "the proof does not prove the required statement", fuel, seen)
                  else
                    match eqExpr v1.t tT v2.t a1 fuel seen with
                    | (.equal, f, s) => (.matched, f, s)
                    | (.differ, f, s) =>
                      (.mismatch "the proof does not prove the required statement", f, s)
                    | (.exhausted, f, s) =>
                      (.mismatch "the comparison passes its work budget", f, s)

end FvdepCore.Judge
