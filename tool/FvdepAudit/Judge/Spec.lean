import FvdepAudit.Export.Spec
import FvdepCore.Index.Rules
import FvdepCore.Judge.Compare

/-! Specs for the judge's comparisons (contract `docs/contracts/U7-judge.md` X7), written from the
contract apart from `FvdepCore.Judge.Compare`'s code: what a pair + a pair of constants mean over
the two exports' denoted tables (left = the trusted export), with no budget + no memo. -/

namespace FvdepAudit.Judge.Spec

open FvdepCore.Export FvdepCore.Judge FvdepCore.Index.Rules

/-- X7: a pair's meaning — two names equal, two levels equal as written (U4's `levelEq`), two
expressions alpha-equivalent (U4's `alphaEq`: binder names, binder info + a `letE`'s `nondep`
ignored), each read from its own export's tables (an index outside its table = unequal). -/
def PairEq (t1 t2 : Tables) : Pair → Prop
  | .name i j => ∃ x, t1.names[i]? = some x ∧ t2.names[j]? = some x
  | .level i j => ∃ x y, t1.levels[i]? = some x ∧ t2.levels[j]? = some y ∧ levelEq x y = true
  | .expr i j => ∃ x y, t1.exprs[i]? = some x ∧ t2.exprs[j]? = some y ∧ alphaEq x y = true

/-- Two lists of name references: equal lengths, pairwise one name. -/
def NamesEq (t1 t2 : Tables) (as bs : List Nat) : Prop :=
  as.length = bs.length ∧ ∀ p ∈ as.zip bs, PairEq t1 t2 (.name p.1 p.2)

/-- Two recursor rule lists: equal lengths; pairwise the constructor (one name), `nfields` + the
right side (alpha-equivalent). -/
def RulesEq (t1 t2 : Tables) (rs ss : List RuleF) : Prop :=
  rs.length = ss.length ∧
    ∀ p ∈ rs.zip ss,
      PairEq t1 t2 (.name p.1.ctor p.2.ctor) ∧
        p.1.nfields = p.2.nfields ∧ PairEq t1 t2 (.expr p.1.rhs p.2.rhs)

/-- X7 `declEq`'s meaning: the same kind + every field the record gives the constant (X6) — names
one name, expressions alpha-equivalent, flags, numbers, hints, safety + the quotient kind
equal. -/
def EntryEq (t1 t2 : Tables) : Entry → Entry → Prop
  | .axiom u lps n ty, .axiom u' lps' n' ty' =>
    u = u' ∧ NamesEq t1 t2 lps lps' ∧ PairEq t1 t2 (.name n n') ∧ PairEq t1 t2 (.expr ty ty')
  | .defn all h lps n s ty v, .defn all' h' lps' n' s' ty' v' =>
    NamesEq t1 t2 all all' ∧
      h = h' ∧
      NamesEq t1 t2 lps lps' ∧
      PairEq t1 t2 (.name n n') ∧ s = s' ∧ PairEq t1 t2 (.expr ty ty') ∧ PairEq t1 t2 (.expr v v')
  | .thm all lps n ty v, .thm all' lps' n' ty' v' =>
    NamesEq t1 t2 all all' ∧
      NamesEq t1 t2 lps lps' ∧
      PairEq t1 t2 (.name n n') ∧ PairEq t1 t2 (.expr ty ty') ∧ PairEq t1 t2 (.expr v v')
  | .opaque all u lps n ty v, .opaque all' u' lps' n' ty' v' =>
    NamesEq t1 t2 all all' ∧
      u = u' ∧
      NamesEq t1 t2 lps lps' ∧
      PairEq t1 t2 (.name n n') ∧ PairEq t1 t2 (.expr ty ty') ∧ PairEq t1 t2 (.expr v v')
  | .quot q lps n ty, .quot q' lps' n' ty' =>
    q = q' ∧ NamesEq t1 t2 lps lps' ∧ PairEq t1 t2 (.name n n') ∧ PairEq t1 t2 (.expr ty ty')
  | .induct x, .induct y =>
    NamesEq t1 t2 x.all y.all ∧
      NamesEq t1 t2 x.ctors y.ctors ∧
      x.isRec = y.isRec ∧
      x.isReflexive = y.isReflexive ∧
      x.isUnsafe = y.isUnsafe ∧
      NamesEq t1 t2 x.levelParams y.levelParams ∧
      PairEq t1 t2 (.name x.name y.name) ∧
      x.numIndices = y.numIndices ∧
      x.numNested = y.numNested ∧ x.numParams = y.numParams ∧ PairEq t1 t2 (.expr x.type y.type)
  | .ctor c, .ctor d =>
    c.cidx = d.cidx ∧
      PairEq t1 t2 (.name c.induct d.induct) ∧
      c.isUnsafe = d.isUnsafe ∧
      NamesEq t1 t2 c.levelParams d.levelParams ∧
      PairEq t1 t2 (.name c.name d.name) ∧
      c.numFields = d.numFields ∧ c.numParams = d.numParams ∧ PairEq t1 t2 (.expr c.type d.type)
  | .recursor r, .recursor s =>
    NamesEq t1 t2 r.all s.all ∧
      r.isUnsafe = s.isUnsafe ∧
      r.k = s.k ∧
      NamesEq t1 t2 r.levelParams s.levelParams ∧
      PairEq t1 t2 (.name r.name s.name) ∧
      r.numIndices = s.numIndices ∧
      r.numMinors = s.numMinors ∧
      r.numMotives = s.numMotives ∧
      r.numParams = s.numParams ∧ RulesEq t1 t2 r.rules s.rules ∧ PairEq t1 t2 (.expr r.type s.type)
  | _, _ => False

end FvdepAudit.Judge.Spec
