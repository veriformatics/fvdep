import Fvdep.Base64.Rfc4648.V1_0_0

/-! Launch example (fvdep's qualification corpus, contract U6 Q; proved against the specs in U7):
base64 encoding + decoding by accumulator over byte triples + symbol quadruples, both alphabets. -/

namespace Launch.Base64

open Fvdep.Base64.Rfc4648.V1_0_0 (symbol quad final standard url)

/-- One 3-byte group's four symbols (the 24 bits, first byte highest). -/
def group (alphabet : List Char) (a b c : UInt8) : List Char :=
  let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
  [symbol alphabet (n / 262144), symbol alphabet (n / 4096 % 64), symbol alphabet (n / 64 % 64),
    symbol alphabet (n % 64)]

/-- The encoding of `bs` after the symbols already in `acc`. -/
def encodeAcc (alphabet : List Char) : List UInt8 → List Char → List Char
  | a :: b :: c :: rest, acc => encodeAcc alphabet rest (acc ++ group alphabet a b c)
  | [a, b], acc =>
    let n := a.toNat * 65536 + b.toNat * 256
    acc ++
      [symbol alphabet (n / 262144), symbol alphabet (n / 4096 % 64),
        symbol alphabet (n / 64 % 64), '=']
  | [a], acc =>
    let n := a.toNat * 65536
    acc ++ [symbol alphabet (n / 262144), symbol alphabet (n / 4096 % 64), '=', '=']
  | [], acc => acc

def encode (bs : List UInt8) : List Char := encodeAcc standard bs []

def encodeUrl (bs : List UInt8) : List Char := encodeAcc url bs []

/-- The bytes of `s` after the bytes already in `acc`: whole quadruples, the last one padded. -/
def decodeAcc (alphabet : List Char) : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc
  | [c0, c1, c2, c3], acc => (final alphabet c0 c1 c2 c3).map (acc ++ ·)
  | c0 :: c1 :: c2 :: c3 :: rest, acc =>
    match quad alphabet c0 c1 c2 c3 with
    | some q => decodeAcc alphabet rest (acc ++ q)
    | none => none
  | _, _ => none

def decode (s : List Char) : Option (List UInt8) := decodeAcc standard s []

def decodeUrl (s : List Char) : Option (List UInt8) := decodeAcc url s []

end Launch.Base64
