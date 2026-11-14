import FvdepCore.Protocol

/-! Fuzz target `protocol-request` (contract U4 "Fuzz"): byte 0 picks a signature (the six launch
signatures + `mixed`, which reaches the `utf16`, `nat`, `int` decoders), the rest = a request line.
Decoded arguments carry the signature's types; their request re-encodes to a line that decodes to
them again; each one's `ok` reply line decodes to its reply object (B4's claims, over the compiled
C); a violation panics. -/

namespace FvdepFuzz

open FvdepCore.Protocol

def protocolSigs : Array Sig :=
  #[⟨"encode", [.bytes], .plain .text⟩, ⟨"decode", [.text], .option .bytes⟩,
    ⟨"encodeUrl", [.bytes], .plain .text⟩, ⟨"decodeUrl", [.text], .option .bytes⟩,
    ⟨"parse", [.text], .option .version⟩, ⟨"compare", [.version, .version], .plain .ordering⟩,
    ⟨"mixed", [.utf16, .nat, .int, .ordering], .option .nat⟩]

/-- Each argument's `ok` reply line, LF dropped, decodes to its reply object (the arguments came
from a request within J1, so each fits J1 again). -/
def repliesDecode : List Val → Bool
  | [] => true
  | x :: xs =>
    let line := encodeReply (.ok x)
    match FvdepCore.Json.decode (line.extract 0 (line.size - 1)) with
    | .ok v => v == replyValue (.ok x) && repliesDecode xs
    | .error _ => false

@[export fvdep_fuzz_protocol]
def protocolTarget (b : ByteArray) : UInt8 :=
  if b.size == 0 then 0
  else
    let sig :=
      protocolSigs.getD ((b.get! 0).toNat % protocolSigs.size) ⟨"encode", [.bytes], .plain .text⟩
    match decodeRequest sig (b.extract 1 b.size) with
    | .error _ => 0
    | .ok xs =>
      if xs.map Val.ty != sig.args then panic! "protocol-request: argument types ≠ the signature"
      else
        let line :=
          FvdepCore.Json.print (.obj [("args", .arr (xs.map encodeVal)), ("op", .str sig.op)])
        match decodeRequest sig line with
        | .ok ys =>
          if ys != xs then panic! "protocol-request: a re-encoded request decodes to other values"
          else
            if repliesDecode xs then 0
            else panic! "protocol-request: an argument's reply line does not decode to its object"
        | .error _ => panic! "protocol-request: a re-encoded request does not decode"

end FvdepFuzz
