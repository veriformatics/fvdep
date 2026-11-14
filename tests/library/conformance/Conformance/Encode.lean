/-! An independent `base64.encode@1.0.0` implementation (contract U4 A8, shape `fn`): each output
symbol from its own byte bits (no 24-bit word), the alphabet by character ranges. Imports Init
alone. -/

namespace Conformance.Encode

/-- The §4 Table 1 symbol of a 6-bit value: `A`–`Z`, `a`–`z`, `0`–`9`, `+`, `/`. -/
def sym (i : Nat) : Char :=
  if i < 26 then Char.ofNat (65 + i)
  else if i < 52 then Char.ofNat (71 + i)
  else if i < 62 then Char.ofNat (i - 4)
  else if i = 62 then '+'
  else '/'

def encode : List UInt8 → List Char
  | a :: b :: c :: rest =>
    sym (a.toNat / 4) :: sym (a.toNat % 4 * 16 + b.toNat / 16) ::
      sym (b.toNat % 16 * 4 + c.toNat / 64) :: sym (c.toNat % 64) :: encode rest
  | [a, b] =>
    [sym (a.toNat / 4), sym (a.toNat % 4 * 16 + b.toNat / 16), sym (b.toNat % 16 * 4), '=']
  | [a] => [sym (a.toNat / 4), sym (a.toNat % 4 * 16), '=', '=']
  | [] => []

end Conformance.Encode
