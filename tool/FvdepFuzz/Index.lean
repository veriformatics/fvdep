import FvdepCore.Index.Doc

/-! Fuzz target `index-decode` (contract U4 "Fuzz"): bytes → `decodeIndex`; an accepted index
re-encodes (it is well formed) to bytes that decode back to it; a violation panics. -/

namespace FvdepFuzz

open FvdepCore.Index

@[export fvdep_fuzz_index]
def indexTarget (b : ByteArray) : UInt8 :=
  match decodeIndex b with
  | .error _ => 0
  | .ok i =>
    match encodeIndex i with
    | .error _ => panic! "index-decode: an accepted index does not re-encode"
    | .ok bytes =>
      match decodeIndex bytes with
      | .ok j =>
        if j = i then 0 else panic! "index-decode: re-encoded bytes decode to another index"
      | .error _ => panic! "index-decode: re-encoded bytes are refused"

end FvdepFuzz
