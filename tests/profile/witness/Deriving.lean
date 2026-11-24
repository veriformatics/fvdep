/-! Q1 (K4's deriving handlers): each admitted class on a recursive, a nested + a mutual type —
`Repr`, `BEq`, `Hashable` + `Ord` take their `partial` branch on the nested + mutual ones (`Ord` on
any recursion), `DecidableEq` emits total structural definitions on a mutual type + Lean declines it
on a nested one, `Inhabited` builds no recursive function (U7's graph check refuses an
implementation reaching a `partial` helper; the profile admits the source). -/

namespace Witness.Deriving

inductive Chain where
  | stop
  | link (n : Nat) (rest : Chain)
  deriving DecidableEq, Repr, BEq, Hashable, Ord, Inhabited

-- `DecidableEq` has no nested branch: Lean 4.35 refuses it here (`None of the deriving handlers for
-- class `DecidableEq` applied to `Rose``), a compile error, never an unsafe admit.
inductive Rose where
  | node (label : Nat) (kids : List Rose)
  deriving Repr, BEq, Hashable, Ord, Inhabited

mutual
  inductive Even where
    | zero
    | succ (o : Odd)
    deriving DecidableEq, Repr, BEq, Hashable, Ord, Inhabited

  inductive Odd where
    | succ (e : Even)
    deriving DecidableEq, Repr, BEq, Hashable, Ord, Inhabited
end

end Witness.Deriving
