import Std.Data.HashSet

namespace Witness.Operators

def arithmetic (a b : Nat) : Nat := ((a + b - a) * a / b) % (b ^ 2)
def bits (a b : UInt8) : UInt8 := ~~~ (((a &&& b) ||| (a ^^^ b)) <<< 1 >>> 2)
def negate (a : Int) : Int := -a
def booleans (a b : Nat) : Bool := !(a == b) && (a != b) || false

def stringLiteral : String := "text"
def charLiteral : Char := 'a'
def scientificLiteral : Float := 1.25e2

def prepend (xs : List Nat) : List Nat := (0 :: xs) ++ [1, 2]
def arrayLiteral : Array Nat := #[1, 2]
def indexForms (xs : Array Nat) (i : Nat) (h : i < xs.size) :
    Nat × Nat × Option Nat × Nat := (xs[i], xs[i]!, xs[i]?, xs[i]'h)

def collections : Std.HashSet Nat × Std.HashSet Nat × Std.HashSet Nat := ({}, {1, 2}, ∅)
def bounded : Type := {n : Nat // n < 5}

def pipes (x : Nat) : Nat := id <| ((Nat.succ ∘ Nat.succ) $ (x |> Nat.succ))
def alternatives (x y : Option Nat) : Option Nat := x <|> y
def bind (x : Option Nat) : Option Nat := x >>= fun a => some (a + 1)
def mapped (x : Option Nat) : Option Nat := Nat.succ <$> x
def applicative (x y : Option Nat) : Option Nat := (some Nat.succ <*> x) <* (x *> y)
structure Step where
  result : Option Nat

instance : AndThen Step where
  andThen x y := ⟨x.result >>= fun _ => (y ()).result⟩

def sequence (x y : Step) : Step := x >> y
def coerce (a : Nat) : Int := ↑a

end Witness.Operators
