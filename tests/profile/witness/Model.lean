/-! Q1: a profile model's shape (U10's phase-1 form, proof-free: Decisions U6) — a literal port of a
package's decoder over the contract's types, its deviations as plain code. -/

namespace Witness.Model

def val (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else
    if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
    else
      if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
      else
        if c = '+' then some 62
        else if c = '/' then some 63 else none

def rev (c : Char) : Nat :=
  match val c with
  | some i => i
  | none => if c = '-' then 62 else if c = '_' then 63 else 0

def get (s : List Char) (i : Nat) : Nat := (s[i]?.map rev).getD 0

def decode (s : List Char) : Option (List Nat) :=
  let len := s.length
  if len % 4 ≠ 0 then none
  else
    let validLen := (s.idxOf? '=').getD len
    let ph := if validLen = len then 0 else 4 - validLen % 4
    if (validLen + ph) * 3 / 4 < ph then none
    else
      let size := (validLen + ph) * 3 / 4 - ph
      let full := if ph > 0 then validLen - 4 else validLen
      let groups := (full + 3) / 4
      let body :=
        (List.range groups).flatMap fun g =>
          let i := 4 * g
          let t := get s i * 262144 + get s (i + 1) * 4096 + get s (i + 2) * 64 + get s (i + 3)
          [t / 65536 % 256, t / 256 % 256, t % 256]
      some ((body ++ List.replicate size 0).take size)

end Witness.Model
