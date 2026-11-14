import FvdepCore.Json

/-! Fuzz target `json-decode` (contract U3 "Fuzz"): the compiled decoder + printer on any input —
a decoded value prints to bytes that decode back to it (J's theorems, over the compiled C); a
violation panics, an abort under `LEAN_ABORT_ON_PANIC=1` = the engine's crash. -/

namespace FvdepFuzz

open FvdepCore.Json

@[export fvdep_fuzz_json]
def jsonTarget (b : ByteArray) : UInt8 :=
  match decode b with
  | .error _ => 0
  | .ok v =>
    match decode (print v) with
    | .ok w => if w == v then 0 else panic! "json-decode: decode (print v) ≠ v"
    | .error _ => panic! "json-decode: print v does not decode"

end FvdepFuzz
