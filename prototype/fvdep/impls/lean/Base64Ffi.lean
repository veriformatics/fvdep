import Base64Acc
import Fvdep.Abi
/-!
C exports of the proven `Base64Acc` encoder + decoder (`ffi/fvdep_base64.c` wraps them in a plain C API).
`encode_abi` / `decode_abi` prove each export equal to its spec module in fvdep's ABI shape
(`Fvdep.Abi.encoder` / `decoder`), so a Rust, Python or Node binding calls proven code.
-/
namespace Base64Ffi
open Fvdep

@[export fvdep_base64_encode]
def encode (b : ByteArray) : String := Abi.textOut (Base64Acc.encode (Abi.bytesIn b))

@[export fvdep_base64_decode]
def decode (s : String) : Option ByteArray := (Base64Acc.decode (Abi.textIn s)).map Abi.bytesOut

theorem encode_abi : encode = Abi.encoder Base64.Encode.V1_0_0.encode := by
  funext b; simp [encode, Abi.encoder, Base64Acc.conforms]

theorem decode_abi : decode = Abi.decoder Base64.Decode.V1_0_0.decode := by
  funext s; simp [decode, Abi.decoder, Base64Acc.decode_conforms]

end Base64Ffi
