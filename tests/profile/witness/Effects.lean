namespace Witness.Effects

def bindForms (v : Option Nat) : Option Nat := do
  let a ← some 1; let b <- some 2
  let mut total ← some (a + b)
  total ← some (total + 1)
  let some c ← some v | return 0
  let (d, e) <- some (c, total)
  let mut some f := v | return 0
  f := f + d
  have inc := f + e
  return inc + (← some 1) + (<- some 2)

private def witnessedElement (xs : List Nat) (x : Nat) (_ : x ∈ xs) : Nat := x

def loopForms (xs ys : List Nat) : Id Nat := do
  let mut total := 0
  for x in xs, y in ys do
    if x == 0 then continue
    if y == 0 then break
    unless x == y do
      total := total + x + y
  for hx : x in xs do
    if h : x < 4 then
      total := total + (Fin.mk x h).val
    else
      total := total + witnessedElement xs x hx
  return total

def conditionForms (v : Option Nat) : Option Nat := do
  if let some a := v then
    if let some b ← some v then
      return a + b
    else
      return a
  else if let some c <- some v then
    return c
  else
    return 0

def matchForms (x y : Option Nat) : Option Nat := do
  do
    match x, y with
    | some a, some b => pure (a + b)
    | _, _ => pure 0

end Witness.Effects
