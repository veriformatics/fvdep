import FvdepCore.Hash.Frame

/-! Fuzz target `unframe` (contract U3 "Fuzz"): bytes that unframe re-frame to themselves (H's
injectivity, over the compiled C); a violation panics. -/

namespace FvdepFuzz

open FvdepCore.Hash

@[export fvdep_fuzz_unframe]
def unframeTarget (b : ByteArray) : UInt8 :=
  match unframe b with
  | none => 0
  | some (tag, files) =>
    if (frame tag files).data == b.data then 0 else panic! "unframe: frame (unframe b) ≠ b"

end FvdepFuzz
