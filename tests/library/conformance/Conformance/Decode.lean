/-! An independent `base64.decode@1.0.0` implementation over the C ABI (contract U4 A8, shape
`abi`): bytes → UTF-8 text → strict decoding; each byte from its own symbol bits (no 24-bit word),
symbol values by character ranges. Imports Init alone. -/

namespace Conformance.Decode

/-- The 6-bit value of a §4 Table 1 symbol; `none` for every other character. -/
def val (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 71)
  else if 48 ≤ n ∧ n ≤ 57 then some (n + 4)
  else if n = 43 then some 62
  else if n = 47 then some 63
  else none

/-- Four symbol values → three bytes. -/
def bytes3 (i0 i1 i2 i3 : Nat) : List UInt8 :=
  [UInt8.ofNat (i0 * 4 + i1 / 16), UInt8.ofNat (i1 % 16 * 16 + i2 / 4),
    UInt8.ofNat (i2 % 4 * 64 + i3)]

/-- Groups of four symbols; only the last may end `xx==` (one byte) or `xxx=` (two bytes), its
unused low bits zero. -/
def chars : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest => do
    let i0 ← val c0
    let i1 ← val c1
    if rest.isEmpty && c3 == '=' then
      if c2 == '=' then
        if i1 % 16 = 0 then some [UInt8.ofNat (i0 * 4 + i1 / 16)] else none
      else do
        let i2 ← val c2
        if i2 % 4 = 0 then
          some [UInt8.ofNat (i0 * 4 + i1 / 16), UInt8.ofNat (i1 % 16 * 16 + i2 / 4)]
        else none
    else do
      let i2 ← val c2
      let i3 ← val c3
      let t ← chars rest
      some (bytes3 i0 i1 i2 i3 ++ t)
  | _ => none

/-- The exported function: input bytes that are not UTF-8 are rejected. -/
def decode (b : ByteArray) : Option ByteArray :=
  match String.fromUTF8? b with
  | some s => (chars s.toList).map fun l => ⟨l.toArray⟩
  | none => none

end Conformance.Decode
