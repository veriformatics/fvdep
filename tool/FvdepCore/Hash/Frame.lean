/-! Hex + length-prefixed framing (contract `docs/contracts/U3-codecs.md` H1–H3): pure; digests =
`FvdepIO.Hash.digest` over `frame`. -/

namespace FvdepCore.Hash

/-- One lowercase hex digit of `n < 16`. -/
def hexDigit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

/-- H1: each byte as two lowercase hex digits, high nibble first (digests: 32 bytes). -/
def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

/-- 8 bytes, big-endian (`n < 2^64` in `FrameDomain`; higher bits are cut). Shifts, not powers of
256: a folded literal ≥ 2^32 compiles to a GMP parse per evaluation. -/
def u64be (n : Nat) : ByteArray :=
  ⟨#[(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
      (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

/-- Files in ascending path order (`String` order = UTF-8 byte order), equal paths stable. -/
def sortByPath (files : List (String × ByteArray)) : List (String × ByteArray) :=
  files.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- H2: `u64be(|tag|) ++ tag ++ u64be(count) ++` per file in path order `u64be(|path|) ++ path ++
u64be(|bytes|) ++ bytes`; |x| = UTF-8 bytes. Appends to one unshared accumulator (linear). -/
def frame (tag : String) (files : List (String × ByteArray)) : ByteArray :=
  (sortByPath files).foldl
    (fun acc f => acc ++ u64be f.1.utf8ByteSize ++ f.1.toUTF8 ++ u64be f.2.size ++ f.2)
    (u64be tag.utf8ByteSize ++ tag.toUTF8 ++ u64be files.length)

/-- The number 8 big-endian bytes spell. -/
def be8Value (bs : List UInt8) : Nat := bs.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- A big-endian 8-byte number + the bytes after it. -/
def takeU64 : List UInt8 → Option (Nat × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (be8Value [b0, b1, b2, b3, b4, b5, b6, b7], rest)
  | _ => none

/-- The first `n` bytes + the rest, when `n` remain (cost: the bytes taken, never the rest). -/
def takeBytes (bs : List UInt8) (n : Nat) : Option (List UInt8 × List UInt8) :=
  let p := bs.splitAt n
  if p.1.length = n then some p else none

/-- The text these bytes encode, when they are valid UTF-8. -/
def text (bs : List UInt8) : Option String := String.fromUTF8? ⟨bs.toArray⟩

/-- `k` more files, each path strictly above `prev`, then no byte left; `acc` = the files read so
far, newest first (a loop: hostile counts + file numbers never deepen the stack). -/
def takeFiles :
    Nat →
      Option String → List UInt8 → List (String × ByteArray) → Option (List (String × ByteArray))
  | 0, _, bs, acc => if bs.isEmpty then some acc.reverse else none
  | k + 1, prev, bs, acc => do
    let (plen, bs) ← takeU64 bs
    let (pbytes, bs) ← takeBytes bs plen
    let path ← text pbytes
    if prev.all (· < path) then
      let (blen, bs) ← takeU64 bs
      let (bytes, bs) ← takeBytes bs blen
      takeFiles k (some path) bs ((path, ⟨bytes.toArray⟩) :: acc)
    else
      none

/-- H2 over the frame's byte list: the reference the proofs read; the shipped `unframe` = the same
steps over offsets, proven equal (`FvdepAudit.Hash.Proof.unframe_eq_list`). -/
def unframeList (b : ByteArray) : Option (String × List (String × ByteArray)) := do
  let (tlen, bs) ← takeU64 b.data.toList
  let (tbytes, bs) ← takeBytes bs tlen
  let tag ← text tbytes
  let (count, bs) ← takeU64 bs
  let files ← takeFiles count none bs []
  return (tag, files)

/-- `takeU64` at offset `i` of `b`: the number + the offset after it. -/
def readU64At (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if i + 8 ≤ b.size then some (be8Value (b.extract i (i + 8)).data.toList, i + 8) else none

/-- `takeBytes` at offset `i` of `b`: the `n` bytes + the offset after them (`b.size - i`
truncates, as `takeBytes` past the end: `n = 0` succeeds there). -/
def takeBytesAt (b : ByteArray) (i n : Nat) : Option (ByteArray × Nat) :=
  if n ≤ b.size - i then some (b.extract i (i + n), i + n) else none

/-- `takeFiles` at offset `i` of `b`. -/
def takeFilesAt (b : ByteArray) :
    Nat → Option String → Nat → List (String × ByteArray) → Option (List (String × ByteArray))
  | 0, _, i, acc => if b.size ≤ i then some acc.reverse else none
  | k + 1, prev, i, acc => do
    let (plen, i) ← readU64At b i
    let (pbytes, i) ← takeBytesAt b i plen
    let path ← String.fromUTF8? pbytes
    if prev.all (· < path) then
      let (blen, i) ← readU64At b i
      let (bytes, i) ← takeBytesAt b i blen
      takeFilesAt b k (some path) i ((path, bytes) :: acc)
    else
      none

/-- H2: the tag + files of exactly H2's layout (valid UTF-8, paths strictly ascending, every byte
consumed), else `none`. Reads offsets into `b`: memory = the frame + the decoded files, where the
byte list `unframeList` walks costs a list cell per byte (contract U5 L: a 17 MB export). -/
def unframe (b : ByteArray) : Option (String × List (String × ByteArray)) := do
  let (tlen, i) ← readU64At b 0
  let (tbytes, i) ← takeBytesAt b i tlen
  let tag ← String.fromUTF8? tbytes
  let (count, i) ← readU64At b i
  let files ← takeFilesAt b count none i []
  return (tag, files)

/-- H3: frame domains: the digests' + the step helper's output frame (contract U5 R8). -/
inductive Tag where
  | specClosure
  | implSources
  | proofSources
  | adapter
  | entry
  | step
  deriving Repr, DecidableEq

/-- H3: the domain tag a digest of this kind frames. -/
def Tag.spelling : Tag → String
  | .specClosure => "fvdep/spec-closure/1"
  | .implSources => "fvdep/impl-sources/1"
  | .proofSources => "fvdep/proof-sources/1"
  | .adapter => "fvdep/adapter/1"
  | .entry => "fvdep/entry/1"
  | .step => "fvdep/step/1"

/-- H3: `fvdep/adapter/1`'s `""` payload: `u64be(count) ++` per argument `u64be(|arg|) ++ arg`, argv
order, repeats kept. -/
def argvBytes (argv : List String) : ByteArray :=
  argv.foldl (fun acc a => acc ++ u64be a.utf8ByteSize ++ a.toUTF8) (u64be argv.length)

/-- H3: the argv entry + the first entry per distinct nonempty named path, in `named` order. -/
def adapterEntries (argv : List String) (named : List (String × ByteArray)) :
    List (String × ByteArray) :=
  ("", argvBytes argv) ::
    (named.filter (·.1 != "")).foldl (fun acc f => if acc.any (·.1 == f.1) then acc else acc ++ [f])
      []

end FvdepCore.Hash
