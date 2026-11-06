import Fvdep.Base64.Decode.V1_0_0
/-!
Example implementation in Lean: accumulator-passing base64 encoder + decoder (tail-recursive,
so no stack growth on large inputs). `conforms` / `decode_conforms` prove each equal to its
spec module on every input ⇒ each inherits every obligation of that module.
`fvdep check base64.encode@1.0.0 --lean impls/lean:Base64Acc --impl Base64Acc.encode
--proof Base64Acc.conforms` delivers the encoder.
-/
namespace Base64Acc
open Fvdep.Base64.Encode.V1_0_0 (sym)
open Fvdep.Base64.Decode.V1_0_0 (quad final)

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
    go bs acc = acc ++ Fvdep.Base64.Encode.V1_0_0.encode bs := by
  induction bs, acc using go.induct with
  | case1 a b c rest acc ih => rw [go, ih]; simp [chunk, Fvdep.Base64.Encode.V1_0_0.encode]
  | _ => simp [go, Fvdep.Base64.Encode.V1_0_0.encode]

theorem conforms : ∀ bs, encode bs = Fvdep.Base64.Encode.V1_0_0.encode bs := by
  intro bs; simp [encode, go_eq]

def goD : List Char → List Nat → Option (List Nat)
  | [], acc => some acc
  | c0 :: c1 :: c2 :: c3 :: rest, acc =>
    if rest = [] then (final c0 c1 c2 c3).map (acc ++ ·)
    else match quad c0 c1 c2 c3 with
      | some q => goD rest (acc ++ q)
      | none => none
  | _, _ => none

def decode (s : List Char) : Option (List Nat) := goD s []

theorem goD_eq (s : List Char) (acc : List Nat) :
    goD s acc = (Fvdep.Base64.Decode.V1_0_0.decode s).map (acc ++ ·) := by
  induction s, acc using goD.induct with
  | case1 acc => simp [goD, Fvdep.Base64.Decode.V1_0_0.decode]
  | case2 c0 c1 c2 c3 acc => simp [goD, Fvdep.Base64.Decode.V1_0_0.decode]
  | case3 c0 c1 c2 c3 rest acc h q hq ih =>
    simp only [goD, h, ite_false, hq, ih, Fvdep.Base64.Decode.V1_0_0.decode, Option.bind_eq_bind,
      Option.bind_some]
    cases Fvdep.Base64.Decode.V1_0_0.decode rest <;> simp
  | case4 c0 c1 c2 c3 rest acc h hq =>
    simp [goD, Fvdep.Base64.Decode.V1_0_0.decode, h, hq]
  | case5 s acc h1 h2 =>
    match s, h1, h2 with
    | [], h, _ => exact absurd rfl h
    | [_], _, _ | [_, _], _, _ | [_, _, _], _, _ => simp [goD, Fvdep.Base64.Decode.V1_0_0.decode]
    | _ :: _ :: _ :: _ :: _, _, h => exact absurd rfl (h _ _ _ _ _)

theorem decode_conforms : ∀ s, decode s = Fvdep.Base64.Decode.V1_0_0.decode s := by
  intro s; cases h : Fvdep.Base64.Decode.V1_0_0.decode s <;> simp [decode, goD_eq, h]

end Base64Acc
