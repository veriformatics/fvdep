import FvdepCore.Judge.Statement

/-! U7 G (contract `docs/contracts/U7-judge.md` G1–G6): the constant graph. From the template's
constants + the mandatory inventory, every constant e1 reaches (Lake's `runForUsedConsts` over
the raw records) must be declared in e2 field for field (`declEq`); then no reached `opaque`
outside the reviewed toolchain list (G5); then the proof's own closure in e2 fully declared, its
axioms recorded (G6). Worklists last in, first out (Lake's comparator); one fuel + memo with S.
Pure. -/

namespace FvdepCore.Judge

open FvdepCore.Export

/-- G1's mandatory inventory (reviewed data, Lean 4.35's comparator): the quotient family, the
allowlisted axioms, `primitiveTargets`. -/
def mandatory : List Lean.Name :=
  [`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `propext, `Classical.choice, `Quot.sound, `Nat.add,
    `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod, `Nat.beq, `Nat.ble, `Nat.land,
    `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight, `String.ofList, `Char.ofNat, `List,
    `eagerReduce, `Nat, `String, `String.mk, `Char, `optParam, `autoParam, `semiOutParam, `outParam]

/-- G1: the roots — the template's constants (T's join through the spec's, the new spec's or the
shape's type; Part B B7: an obligation's = its proposition constant alone, a compat's = `Eq`, new,
old), then the mandatory inventory. -/
def graphRoots (r : Request) : List Lean.Name :=
  if r.kind == .prop then r.spec :: mandatory
  else
    if r.kind == .compat then [`Eq, r.impl, r.spec] ++ mandatory
    else [`Eq, r.impl, r.spec] ++ r.abi.toList ++ mandatory

/-- One expression record's constants (a `const`'s name, a `proj`'s structure name) +
children. -/
def exprStep (t : Tables) (i : Nat) : List Nat × List Nat :=
  match t.rawExprs[i]? with
  | some (.const n _) => ([n], [])
  | some (.proj s _ e) => ([s], [e])
  | some (.app f a) => ([], [f, a])
  | some (.lam _ ty b _) => ([], [ty, b])
  | some (.forallE _ ty b _) => ([], [ty, b])
  | some (.letE _ ty v b _) => ([], [ty, v, b])
  | _ => ([], [])

/-- G2: a constant's uses — its direct names + the expressions to scan (Lake's
`runForUsedConsts`: type + value, an inductive's constructors + `all`, a constructor's
inductive, a recursor's rule constructors + right sides). -/
def entryUses : Entry → List Nat × List Nat
  | .axiom _ _ _ ty => ([], [ty])
  | .defn _ _ _ _ _ ty v => ([], [ty, v])
  | .thm _ _ _ ty v => ([], [ty, v])
  | .opaque _ _ _ _ ty v => ([], [ty, v])
  | .quot _ _ _ ty => ([], [ty])
  | .induct x => (x.ctors ++ x.all, [x.type])
  | .ctor c => ([c.induct], [c.type])
  | .recursor r => (r.rules.map (·.ctor), r.type :: r.rules.map (·.rhs))

/-- The constants (name indices) under the expressions `todo`, each expression once per export
(`seen`), one unit of fuel per expression taken: the names found (newest first), the fuel left +
the expressions seen; `none` = out of fuel. -/
def collect (t : Tables) :
    Nat → List Nat → Std.HashSet Nat → List Nat → Option (List Nat × Nat × Std.HashSet Nat)
  | fuel, [], seen, acc => some (acc, fuel, seen)
  | 0, _ :: _, _, _ => none
  | fuel + 1, i :: rest, seen, acc =>
    if seen.contains i then collect t fuel rest seen acc
    else
      let (ns, kids) := exprStep t i
      collect t fuel (kids ++ rest) (seen.insert i) (ns ++ acc)

/-- A constant's used names, denoted in `t` (an unbound index drops out), after its expressions
were scanned. -/
def usesOf (t : Tables) (e : Entry) (fuel : Nat) (seen : Std.HashSet Nat) :
    Option (List Lean.Name × Nat × Std.HashSet Nat) :=
  let (ns, roots) := entryUses e
  match collect t fuel roots seen [] with
  | none => none
  | some (found, f, s) => some ((ns ++ found).filterMap (t.names[·]?), f, s)

/-- G3's walk state. -/
structure Walk where
  todo : List Lean.Name
  checked : Std.HashSet Lean.Name
  /-- The closure so far, newest first (G5 reads it). -/
  order : List Lean.Name
  /-- e1's expressions already scanned for constants. -/
  seen : Std.HashSet Nat
  fuel : Nat
  memo : Std.HashSet Pair

/-- G3, at most `steps` names (one unit of fuel each): each name not yet checked — missing in e1
= infrastructure, missing in e2 or not `declEq` = mismatch — then its uses (in e1) join. -/
def graphWalk (v1 v2 : View) : Nat → Walk → Outcome × Walk
  | 0, w => if w.todo.isEmpty then (.matched, w) else (.exhausted, w)
  | steps + 1, w =>
    match w.todo with
    | [] => (.matched, w)
    | c :: rest =>
      match w.fuel with
      | 0 => (.exhausted, w)
      | fuel + 1 =>
        if w.checked.contains c then
          graphWalk v1 v2 steps
            { w with
              todo := rest, fuel }
        else
          match v1.byName[c]? with
          | none =>
            (.infra s!"the trusted export lacks {c}",
              { w with
                todo := rest, fuel })
          | some e1 =>
            match v2.byName[c]? with
            | none =>
              (.mismatch s!"the solution lacks {c}",
                { w with
                  todo := rest, fuel })
            | some e2 =>
              match declEq v1.t e1 v2.t e2 fuel w.memo with
              | (.differ, f, m) =>
                (.mismatch s!"the solution redefines {c}",
                  { w with
                    todo := rest, fuel := f, memo := m })
              | (.exhausted, f, m) =>
                (.exhausted,
                  { w with
                    todo := rest, fuel := f, memo := m })
              | (.equal, f, m) =>
                match usesOf v1.t e1 f w.seen with
                | none =>
                  (.exhausted,
                    { w with
                      todo := rest, fuel := 0, memo := m })
                | some (ns, f', s') =>
                  graphWalk v1 v2 steps
                    { todo := ns ++ rest
                      checked := w.checked.insert c
                      order := c :: w.order
                      seen := s'
                      fuel := f'
                      memo := m }

/-- G5's refusal text. -/
def opaqueCause (c : Lean.Name) : String :=
  s!"the checked declaration graph reaches {c}, an opaque definition outside this profile's " ++
    "exceptions"

/-- G5: the first name (in `cs`' order) of an `opaque` constant of e1 outside the reviewed list. -/
def firstOpaque (v1 : View) (allowed : List Lean.Name) : List Lean.Name → Option Lean.Name
  | [] => none
  | c :: cs =>
    match v1.byName[c]? with
    | some (.opaque ..) => if allowed.contains c then firstOpaque v1 allowed cs else some c
    | _ => firstOpaque v1 allowed cs

/-- G6's walk state (in e2). -/
structure ProofWalk where
  todo : List Lean.Name
  checked : Std.HashSet Lean.Name
  /-- The axioms reached, newest first. -/
  axioms : List Lean.Name
  seen : Std.HashSet Nat
  fuel : Nat

/-- G6: the axioms after checking `c` (its constant `e`): `c` joins when `e` is an axiom. -/
def recordAxiom (c : Lean.Name) : Entry → List Lean.Name → List Lean.Name
  | .axiom .., ax => c :: ax
  | _, ax => ax

/-- G6: the proof's closure in e2 — every reached name declared there, each axiom recorded. -/
def proofWalk (v2 : View) : Nat → ProofWalk → Outcome × ProofWalk
  | 0, w => if w.todo.isEmpty then (.matched, w) else (.exhausted, w)
  | steps + 1, w =>
    match w.todo with
    | [] => (.matched, w)
    | c :: rest =>
      match w.fuel with
      | 0 => (.exhausted, w)
      | fuel + 1 =>
        if w.checked.contains c then
          proofWalk v2 steps
            { w with
              todo := rest, fuel }
        else
          match v2.byName[c]? with
          | none =>
            (.mismatch s!"the solution lacks {c}",
              { w with
                todo := rest, fuel })
          | some e =>
            match usesOf v2.t e fuel w.seen with
            | none =>
              (.exhausted,
                { w with
                  todo := rest, fuel := 0 })
            | some (ns, f, s) =>
              proofWalk v2 steps
                { todo := ns ++ rest
                  checked := w.checked.insert c
                  axioms := recordAxiom c e w.axioms
                  seen := s
                  fuel := f }

/-- G3's start: G1's roots to check, nothing seen. -/
def walkStart (r : Request) (fuel : Nat) (memo : Std.HashSet Pair) : Walk :=
  { todo := graphRoots r, checked := {}, order := [], seen := {}, fuel, memo }

/-- G6's start: the proof constant to check, nothing seen. -/
def proofStart (r : Request) (fuel : Nat) : ProofWalk :=
  { todo := [r.proof], checked := {}, axioms := [], seen := {}, fuel }

/-- G: G3, then G5, then G6 (the first failure named); on a pass the axioms G6 recorded, in first
reach order (A's input); the fuel + memo left. -/
def graph (v1 v2 : View) (r : Request) (opaques : List Lean.Name) (fuel : Nat)
    (memo : Std.HashSet Pair) : Outcome × List Lean.Name × Nat × Std.HashSet Pair :=
  match graphWalk v1 v2 (fuel + 1) (walkStart r fuel memo) with
  | (.matched, w) =>
    match firstOpaque v1 opaques w.order.reverse with
    | some c => (.mismatch (opaqueCause c), [], w.fuel, w.memo)
    | none =>
      match proofWalk v2 (w.fuel + 1) (proofStart r w.fuel) with
      | (.matched, p) => (.matched, p.axioms.reverse, p.fuel, w.memo)
      | (o, p) => (o, [], p.fuel, w.memo)
  | (o, w) => (o, [], w.fuel, w.memo)

end FvdepCore.Judge
