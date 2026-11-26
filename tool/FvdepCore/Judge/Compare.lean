import FvdepCore.Export
import Std.Data.HashSet

/-! U7 X7 (contract `docs/contracts/U7-judge.md`): one export's constants vs another's, over their
raw records (U7 X6). Names, levels + expressions are compared by index pairs, each pair once per
judge run (a memo shared by every comparison of the run), one unit of the work budget per pair
taken; binder names, binder info + a `letE`'s `nondep` flag are never compared (U4's
alpha-equivalence over the denoted terms), every other field exactly. A record names only earlier
records, so a pair accepted on the way is never circular. An untrusted export's shared DAG never
reaches an unbounded walk, and running out is never a pass. Pure. -/

namespace FvdepCore.Judge

open FvdepCore.Export

/-- Two names, levels or expressions still to compare, by index (left = the trusted export). -/
inductive Pair where
  | name (i j : Nat)
  | level (i j : Nat)
  | expr (i j : Nat)
  deriving DecidableEq, Hashable, Repr

/-- A comparison's outcome. -/
inductive Cmp where
  | equal
  | differ
  | exhausted
  deriving DecidableEq, Repr

/-- Two index lists as pairs (`none` = the lengths differ). -/
def zipPairs (mk : Nat → Nat → Pair) : List Nat → List Nat → Option (List Pair)
  | [], [] => some []
  | a :: as, b :: bs => (zipPairs mk as bs).map (mk a b :: ·)
  | _, _ => none

/-- Two name records' heads (index 0 = the predefined anonymous name: `none`): `none` = they
differ here, else the pairs that decide. -/
def nameHeads : Option NameF → Option NameF → Option (List Pair)
  | none, none => some []
  | some (.str p s), some (.str q s') => if s == s' then some [.name p q] else none
  | some (.num p k), some (.num q k') => if k == k' then some [.name p q] else none
  | _, _ => none

/-- Two level records' heads (index 0 = the predefined zero: `none`). -/
def levelHeads : Option LevelF → Option LevelF → Option (List Pair)
  | none, none => some []
  | some (.succ a), some (.succ b) => some [.level a b]
  | some (.max a b), some (.max c d) => some [.level a c, .level b d]
  | some (.imax a b), some (.imax c d) => some [.level a c, .level b d]
  | some (.param a), some (.param b) => some [.name a b]
  | _, _ => none

/-- Two expression records' heads (binder names, binder info + `nondep` never read). -/
def exprHeads : ExprF → ExprF → Option (List Pair)
  | .bvar a, .bvar b => if a == b then some [] else none
  | .sort a, .sort b => some [.level a b]
  | .const a us, .const b vs => (zipPairs .level us vs).map (.name a b :: ·)
  | .app f a, .app g b => some [.expr f g, .expr a b]
  | .lam _ t b _, .lam _ t' b' _ => some [.expr t t', .expr b b']
  | .forallE _ t b _, .forallE _ t' b' _ => some [.expr t t', .expr b b']
  | .letE _ t v b _, .letE _ t' v' b' _ => some [.expr t t', .expr v v', .expr b b']
  | .proj s i e, .proj s' i' e' => if i == i' then some [.name s s', .expr e e'] else none
  | .natVal a, .natVal b => if a == b then some [] else none
  | .strVal a, .strVal b => if a == b then some [] else none
  | _, _ => none

/-- A pair's heads, read from the two tables' records (an unbound index = a difference). -/
def heads (t1 t2 : Tables) : Pair → Option (List Pair)
  | .name i j =>
    match t1.rawNames[i]?, t2.rawNames[j]? with
    | some a, some b => nameHeads a b
    | _, _ => none
  | .level i j =>
    match t1.rawLevels[i]?, t2.rawLevels[j]? with
    | some a, some b => levelHeads a b
    | _, _ => none
  | .expr i j =>
    match t1.rawExprs[i]?, t2.rawExprs[j]? with
    | some a, some b => exprHeads a b
    | _, _ => none

/-- The worklist under `fuel` (one unit per pair taken) over the pairs accepted so far: the
outcome, the fuel left + the accepted pairs (a difference ends the run's comparisons, so its memo
is never read again). -/
def walk (t1 t2 : Tables) : Nat → List Pair → Std.HashSet Pair → Cmp × Nat × Std.HashSet Pair
  | fuel, [], seen => (.equal, fuel, seen)
  | 0, _ :: _, seen => (.exhausted, 0, seen)
  | fuel + 1, p :: rest, seen =>
    if seen.contains p then walk t1 t2 fuel rest seen
    else
      match heads t1 t2 p with
      | some kids => walk t1 t2 fuel (kids ++ rest) (seen.insert p)
      | none => (.differ, fuel, seen)

/-- X7: expression `i` of `t1` vs expression `j` of `t2`. -/
def eqExpr (t1 : Tables) (i : Nat) (t2 : Tables) (j : Nat) (fuel : Nat) (seen : Std.HashSet Pair) :
    Cmp × Nat × Std.HashSet Pair := walk t1 t2 fuel [.expr i j] seen

/-! ## Constants (X6 + `declEq`) -/

/-- X6: one constant of a declaration record with every field the record gives it (references =
indices; an inductive block's types, constructors + recursors apart). -/
inductive Entry where
  | «axiom» (isUnsafe : Bool) (levelParams : List Nat) (name type : Nat)
  |
  defn (all : List Nat) (hints : Hints) (levelParams : List Nat) (name : Nat) (safety : Safety)
    (type value : Nat)
  | thm (all levelParams : List Nat) (name type value : Nat)
  | «opaque» (all : List Nat) (isUnsafe : Bool) (levelParams : List Nat) (name type value : Nat)
  | quot (kind : QuotKind) (levelParams : List Nat) (name type : Nat)
  | induct (x : TypeF)
  | ctor (c : CtorF)
  | recursor (r : RecF)
  deriving DecidableEq, Repr

/-- X6: a record's constants (an inductive block: its types, then constructors, then recursors). -/
def entries : DeclF → List Entry
  | .axiom u lps n ty => [.axiom u lps n ty]
  | .defn all h lps n s ty v => [.defn all h lps n s ty v]
  | .thm all lps n ty v => [.thm all lps n ty v]
  | .opaque all u lps n ty v => [.opaque all u lps n ty v]
  | .quot q lps n ty => [.quot q lps n ty]
  | .induct cs rs ts => ts.map .induct ++ cs.map .ctor ++ rs.map .recursor

/-- Name pairs of two lists of the same length. -/
def namePairs (as bs : List Nat) : List Pair := (as.zip bs).map fun p => .name p.1 p.2

/-- Two constants' exact parts agree: the kind, every flag, number, hint, safety + quotient kind,
every list's length + each recursor rule's `nfields`. -/
def fieldsMatch : Entry → Entry → Bool
  | .axiom u lps _ _, .axiom u' lps' _ _ => u == u' && lps.length == lps'.length
  | .defn all h lps _ s _ _, .defn all' h' lps' _ s' _ _ =>
    all.length == all'.length && h == h' && lps.length == lps'.length && s == s'
  | .thm all lps _ _ _, .thm all' lps' _ _ _ =>
    all.length == all'.length && lps.length == lps'.length
  | .opaque all u lps _ _ _, .opaque all' u' lps' _ _ _ =>
    all.length == all'.length && u == u' && lps.length == lps'.length
  | .quot q lps _ _, .quot q' lps' _ _ => q == q' && lps.length == lps'.length
  | .induct x, .induct y =>
    x.all.length == y.all.length && x.ctors.length == y.ctors.length && x.isRec == y.isRec &&
      x.isReflexive == y.isReflexive &&
      x.isUnsafe == y.isUnsafe &&
      x.levelParams.length == y.levelParams.length &&
      x.numIndices == y.numIndices &&
      x.numNested == y.numNested &&
      x.numParams == y.numParams
  | .ctor c, .ctor d =>
    c.cidx == d.cidx && c.isUnsafe == d.isUnsafe && c.levelParams.length == d.levelParams.length &&
      c.numFields == d.numFields &&
      c.numParams == d.numParams
  | .recursor r, .recursor s =>
    r.all.length == s.all.length && r.isUnsafe == s.isUnsafe && r.k == s.k &&
      r.levelParams.length == s.levelParams.length &&
      r.numIndices == s.numIndices &&
      r.numMinors == s.numMinors &&
      r.numMotives == s.numMotives &&
      r.numParams == s.numParams &&
      r.rules.length == s.rules.length &&
      (r.rules.zip s.rules).all fun p => p.1.nfields == p.2.nfields
  | _, _ => false

/-- Two constants' name + expression pairs (meaningful once `fieldsMatch` holds). -/
def pairsOf : Entry → Entry → List Pair
  | .axiom _ lps n ty, .axiom _ lps' n' ty' => namePairs lps lps' ++ [.name n n', .expr ty ty']
  | .defn all _ lps n _ ty v, .defn all' _ lps' n' _ ty' v' =>
    namePairs all all' ++ namePairs lps lps' ++ [.name n n', .expr ty ty', .expr v v']
  | .thm all lps n ty v, .thm all' lps' n' ty' v' =>
    namePairs all all' ++ namePairs lps lps' ++ [.name n n', .expr ty ty', .expr v v']
  | .opaque all _ lps n ty v, .opaque all' _ lps' n' ty' v' =>
    namePairs all all' ++ namePairs lps lps' ++ [.name n n', .expr ty ty', .expr v v']
  | .quot _ lps n ty, .quot _ lps' n' ty' => namePairs lps lps' ++ [.name n n', .expr ty ty']
  | .induct x, .induct y =>
    namePairs x.all y.all ++ namePairs x.ctors y.ctors ++ namePairs x.levelParams y.levelParams ++
      [.name x.name y.name, .expr x.type y.type]
  | .ctor c, .ctor d =>
    namePairs c.levelParams d.levelParams ++
      [.name c.induct d.induct, .name c.name d.name, .expr c.type d.type]
  | .recursor r, .recursor s =>
    namePairs r.all s.all ++ namePairs r.levelParams s.levelParams ++
      ((r.rules.zip s.rules).flatMap fun p => [.name p.1.ctor p.2.ctor, .expr p.1.rhs p.2.rhs]) ++
      [.name r.name s.name, .expr r.type s.type]
  | _, _ => []

/-- X7 `declEq`: constant `e` of `t1` vs constant `e'` of `t2`. -/
def declEq (t1 : Tables) (e : Entry) (t2 : Tables) (e' : Entry) (fuel : Nat)
    (seen : Std.HashSet Pair) : Cmp × Nat × Std.HashSet Pair :=
  if fieldsMatch e e' then walk t1 t2 fuel (pairsOf e e') seen else (.differ, fuel, seen)

end FvdepCore.Judge
