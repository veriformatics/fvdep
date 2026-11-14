import FvdepCore.Doc

/-! Fuzz target `lock-decode` (contract U3 "Fuzz"): a decoded lock encodes to bytes that decode
back to it (D's theorems, over the compiled C); a violation panics. The lock path carries the
long-digit + deep inputs whose cost the suites cannot bound (J5). -/

namespace FvdepFuzz

open FvdepCore.Doc

@[export fvdep_fuzz_lock]
def lockTarget (b : ByteArray) : UInt8 :=
  match decodeLock b with
  | .error _ => 0
  | .ok l =>
    match decodeLock (encodeLock l) with
    | .ok l' => if l' == l then 0 else panic! "lock-decode: decodeLock (encodeLock l) ≠ l"
    | .error _ => panic! "lock-decode: encodeLock l does not decode"

end FvdepFuzz
