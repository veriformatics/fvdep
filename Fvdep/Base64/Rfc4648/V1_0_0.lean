/-! RFC 4648 base64 as fvdep's launch specs read it (shared by `base64.encode`, `base64.decode`,
`base64.encode_url`, `base64.decode_url` 1.0.0): the alphabets (§4 Table 1, §5 Table 2), the
encoding (§4, zero bits filling the last symbol §3.5), strict decoding (§3.2 padding required, §3.3
characters outside the alphabet rejected, §3.5 canonical: the filling bits must be zero) and §4's
bit-group description written apart (`encodeBits`, the encoders' `bits` obligation). -/

namespace Fvdep.Base64.Rfc4648.V1_0_0

/-- §4 Table 1: the symbols for the values 0–63. -/
def standard : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

/-- §5 Table 2 ("URL and Filename safe"): Table 1 with `-` for 62 and `_` for 63. -/
def url : List Char := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList

/-- The symbol for a 6-bit value (`=` never occurs: callers pass values below 64). -/
def symbol (alphabet : List Char) (i : Nat) : Char := alphabet.getD i '='

/-- The 6-bit value of an alphabet symbol; `none` for any other character, `=` included. -/
def value (alphabet : List Char) (c : Char) : Option Nat := alphabet.idxOf? c

/-- §4: each 3-byte group = 24 bits n (first byte highest) → the symbols of its four 6-bit groups,
highest first (262144 = 2^18, 4096 = 2^12); a final 2-byte group → three symbols + `=`, a final byte
→ two symbols + `==`, zero bits filling the last symbol. -/
def encodeWith (alphabet : List Char) : List UInt8 → List Char
  | a :: b :: c :: rest =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    symbol alphabet (n / 262144) ::
      symbol alphabet (n / 4096 % 64) ::
      symbol alphabet (n / 64 % 64) :: symbol alphabet (n % 64) :: encodeWith alphabet rest
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [symbol alphabet (n / 262144), symbol alphabet (n / 4096 % 64), symbol alphabet (n / 64 % 64),
      '=']
  | [a] =>
    let n := a.toNat * 65536
    [symbol alphabet (n / 262144), symbol alphabet (n / 4096 % 64), '=', '=']
  | [] => []

/-- Four symbols → the three bytes of their 24 bits. -/
def quad (alphabet : List Char) (c0 c1 c2 c3 : Char) : Option (List UInt8) := do
  let i0 ← value alphabet c0
  let i1 ← value alphabet c1
  let i2 ← value alphabet c2
  let i3 ← value alphabet c3
  let n := i0 * 262144 + i1 * 4096 + i2 * 64 + i3
  some [(n / 65536).toUInt8, (n / 256 % 256).toUInt8, (n % 256).toUInt8]

/-- The last group: `xx==` → one byte (the second symbol's low 4 bits must be zero), `xxx=` → two
bytes (the third symbol's low 2 bits must be zero), else four symbols. -/
def final (alphabet : List Char) (c0 c1 c2 c3 : Char) : Option (List UInt8) :=
  if c3 = '=' then
    if c2 = '=' then do
      let i0 ← value alphabet c0
      let i1 ← value alphabet c1
      if i1 % 16 = 0 then
        some [(i0 * 4 + i1 / 16).toUInt8]
      else
        none
    else do
      let i0 ← value alphabet c0
      let i1 ← value alphabet c1
      let i2 ← value alphabet c2
      if i2 % 4 = 0 then
        let n := i0 * 4096 + i1 * 64 + i2
        some [(n / 1024).toUInt8, (n / 4 % 256).toUInt8]
      else
        none
  else quad alphabet c0 c1 c2 c3

/-- Strict decoding: groups of four, `=` only in the last group as `xx==` or `xxx=`, every other
character an alphabet symbol, the filling bits zero, nothing else (no whitespace, no line
breaks). -/
def decodeWith (alphabet : List Char) : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest =>
    if rest.isEmpty then final alphabet c0 c1 c2 c3
    else do
      let q ← quad alphabet c0 c1 c2 c3
      let t ← decodeWith alphabet rest
      some (q ++ t)
  | _ => none

/-! ## §4 written apart: the bit-group description -/

/-- A byte's 8 bits, most significant first. -/
def bitsOf (b : UInt8) : List Bool := (List.range 8).reverse.map fun i => b.toNat.testBit i

/-- The value of a bit list, its first bit most significant. -/
def valueOf (bits : List Bool) : Nat := bits.foldl (fun n bit => 2 * n + bit.toNat) 0

/-- Consecutive groups of 6 bits; the last group holds the remaining bits when fewer than 6
remain. -/
def sextets : List Bool → List (List Bool)
  | a :: b :: c :: d :: e :: f :: rest => [a, b, c, d, e, f] :: sextets rest
  | [] => []
  | short => [short]

/-- §4 as written: the input bits (bytes in order, each most significant bit first) in 6-bit groups,
zero bits added on the right to complete the last group; each group → its symbol; `=` added until
the output length is a multiple of 4. -/
def encodeBits (alphabet : List Char) (bytes : List UInt8) : List Char :=
  let groups := sextets (bytes.flatMap bitsOf)
  let symbols :=
    groups.map fun g => symbol alphabet (valueOf (g ++ List.replicate (6 - g.length) false))
  symbols ++ List.replicate ((4 - symbols.length % 4) % 4) '='

end Fvdep.Base64.Rfc4648.V1_0_0
