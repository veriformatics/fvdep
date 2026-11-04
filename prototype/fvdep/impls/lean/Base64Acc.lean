import Fvdep.Base64.V1_0_0
/-!
Example implementation in Lean: accumulator-passing base64 encoder (tail-recursive, so no
stack growth on large inputs). `conforms` proves it equals the spec's `encode` on every
input ⇒ it inherits every spec obligation. `fvdep check --lang lean` audits `conforms`.
-/
namespace Base64Acc
open Fvdep.Base64.V1_0_0 (sym)

def chunk (n : Nat) : List Char := [sym (n / 262144), sym (n / 4096 % 64), sym (n / 64 % 64), sym (n % 64)]

def go : List Nat → List Char → List Char
  | a :: b :: c :: rest, acc => go rest (acc ++ chunk (a * 65536 + b * 256 + c))
  | [a, b], acc =>
    let n := a * 65536 + b * 256
    acc ++ [sym (n / 262144), sym (n / 4096 % 64), sym (n / 64 % 64), '=']
  | [a], acc =>
    let n := a * 65536
    acc ++ [sym (n / 262144), sym (n / 4096 % 64), '=', '=']
  | [], acc => acc

def encode (bs : List Nat) : List Char := go bs []

theorem go_eq (bs : List Nat) (acc : List Char) :
    go bs acc = acc ++ Fvdep.Base64.V1_0_0.encode bs := by
  induction bs, acc using go.induct with
  | case1 a b c rest acc ih => rw [go, ih]; simp [chunk, Fvdep.Base64.V1_0_0.encode]
  | _ => simp [go, Fvdep.Base64.V1_0_0.encode]

theorem conforms : ∀ bs, encode bs = Fvdep.Base64.V1_0_0.encode bs := by
  intro bs; simp [encode, go_eq]

end Base64Acc
