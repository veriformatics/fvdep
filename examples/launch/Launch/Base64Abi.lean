import Fvdep.Abi.V1_0_0
import Launch.Base64

/-! Launch example, the C ABI shapes (`Fvdep.Abi.V1_0_0`): each base64 operation over bytes in and
bytes out, through the library's own shape (proved equal to the shape of its spec in U7). -/

namespace Launch.Base64Abi

def encode : ByteArray → ByteArray := Fvdep.Abi.V1_0_0.encoder Launch.Base64.encode

def encodeUrl : ByteArray → ByteArray := Fvdep.Abi.V1_0_0.encoder Launch.Base64.encodeUrl

def decode : ByteArray → Option ByteArray := Fvdep.Abi.V1_0_0.decoder Launch.Base64.decode

def decodeUrl : ByteArray → Option ByteArray := Fvdep.Abi.V1_0_0.decoder Launch.Base64.decodeUrl

end Launch.Base64Abi
