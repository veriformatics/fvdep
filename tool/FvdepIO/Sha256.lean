import FvdepCore.Hash.Frame

/-! SHA-256 by HACL*'s verified C (contract `docs/contracts/U3-codecs.md` S3; `c/fvdep_sha256.c`) +
the framed digests producers call (H3). Tested residue `hacl-sha256`: no Lean theorem covers the C.
The four `@[extern]` constants = the residue's boundary (ledger). -/

namespace FvdepIO.Hash

/-- SHA-256 of the bytes (32 bytes); a process abort at 2^61 bytes or more, never a digest. -/
@[extern "fvdep_sha256"]
opaque sha256 (input : @& ByteArray) : ByteArray

namespace Sha256

/-- HACL's eight initial chaining words (FFI boundary: callers use `State`). -/
@[extern "fvdep_sha256_init"]
opaque initState : Unit → ByteArray

/-- Hashes the whole blocks `data[off, off + len)` into the chaining state `h` (FFI boundary: `len`
a multiple of 64 + the span inside `data`, else the C side aborts). -/
@[extern "fvdep_sha256_absorb"]
opaque absorb (h : ByteArray) (data : @& ByteArray) (off len : USize) : ByteArray

/-- The digest from a chaining state, the < 64 trailing bytes + the byte count (FFI boundary: an
over-limit or inconsistent count aborts). -/
@[extern "fvdep_sha256_squeeze"]
opaque squeeze (h : @& ByteArray) (tail : @& ByteArray) (total : UInt64) : ByteArray

/-- Streaming state as a plain value: HACL's chaining words, the current partial block, every byte
count fed. No mutable object is shared (the C copies a shared state before writing). -/
structure State where private mk ::
  private h : ByteArray
  private tail : ByteArray
  private total : Nat

def init : State := ⟨initState (), .empty, 0⟩

/-- Feeds `data`: whole blocks go to HACL, the remainder waits in `tail`. -/
def update (s : State) (data : @& ByteArray) : State :=
  let total := s.total + data.size
  if s.tail.size + data.size < 64 then ⟨s.h, s.tail ++ data, total⟩
  else
    let fill := 64 - s.tail.size
    let (h, start) :=
      if s.tail.isEmpty then (s.h, 0) else (absorb s.h (s.tail ++ data.extract 0 fill) 0 64, fill)
    let whole := (data.size - start) / 64 * 64
    ⟨absorb h data start.toUSize whole.toUSize, data.extract (start + whole) data.size, total⟩

/-- `min n (2^64 − 1)`: a stream's byte count never wraps on its way to the C limit check (2^61),
so every over-limit stream aborts (law: `FvdepAudit.Hash.Proof.saturate_toNat`). -/
def saturate (n : Nat) : UInt64 :=
  if n < UInt64.size then n.toUInt64 else UInt64.ofNat (UInt64.size - 1)

def finish (s : State) : ByteArray := squeeze s.h s.tail (saturate s.total)

/-- SHA-256 of every chunk `read` returns until an empty one; a read error propagates (never a
digest of a prefix). -/
def ofReader (read : IO ByteArray) : IO ByteArray := do
  let mut s := init
  repeat
    let chunk ← read
    if chunk.isEmpty then
      break
    s := update s chunk
  return finish s

end Sha256

/-- SHA-256 of a file's bytes, read in 1 MiB chunks. -/
def sha256File (path : System.FilePath) : IO ByteArray :=
  IO.FS.withFile path .read fun h => Sha256.ofReader (h.read (1024 * 1024))

/-- H3: the digest a producer records = lowercase hex of SHA-256 over the framed files. -/
def digest (t : FvdepCore.Hash.Tag) (files : List (String × ByteArray)) : String :=
  FvdepCore.Hash.hex (sha256 (FvdepCore.Hash.frame t.spelling files))

end FvdepIO.Hash
