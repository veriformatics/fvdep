import FvdepCore.Hash.Frame

/-! Specs for hex + framing (contract `docs/contracts/U3-codecs.md` H1–H4), written from the
contract apart from `FvdepCore.Hash`'s code: the hex text (H1), the frame layout over bytes + its
domain (H2). `String` order = UTF-8 byte order (UTF-8 preserves scalar order), so "ascending path
bytes" = ascending `String`s. -/

namespace FvdepAudit.Hash.Spec

/-- One lowercase hex digit of `n < 16`. -/
def digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- H1: each byte → its two lowercase hex digits, high nibble first. -/
def hexSpec (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)])

/-- 8-byte big-endian: byte `k` from the right = `n / 256^k mod 256`. -/
def be8 (n : Nat) : List UInt8 := [7, 6, 5, 4, 3, 2, 1, 0].map fun k => (n / 256 ^ k % 256).toUInt8

/-- UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- Files in ascending path order, equal paths stable. -/
def byPath (fs : List (String × ByteArray)) : List (String × ByteArray) :=
  fs.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- One file's frame entry: `u64be(|path|) ++ path ++ u64be(|bytes|) ++ bytes`. -/
def entry (f : String × ByteArray) : List UInt8 :=
  be8 (utf8 f.1).length ++ utf8 f.1 ++ be8 f.2.size ++ f.2.data.toList

/-- H2's layout: tag length, tag, file count, then every file in path order. -/
def frameSpec (t : String) (fs : List (String × ByteArray)) : List UInt8 :=
  be8 (utf8 t).length ++ utf8 t ++ be8 fs.length ++ (byPath fs).flatMap entry

/-- H2: distinct paths; every length + the count below 2^64. -/
def FrameDomain (t : String) (fs : List (String × ByteArray)) : Prop :=
  (fs.map (·.1)).Nodup ∧
    (utf8 t).length < 2 ^ 64 ∧
    fs.length < 2 ^ 64 ∧ ∀ f ∈ fs, (utf8 f.1).length < 2 ^ 64 ∧ f.2.size < 2 ^ 64

end FvdepAudit.Hash.Spec
