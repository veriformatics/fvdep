import Launch.Base64Abi
import Launch.Proof.Base64

/-! Launch proofs (contract U7 E): the C ABI variants = the library's shapes applied to the specs
(`@impl = Fvdep.Abi.V1_0_0.<shape> @spec`). -/

namespace Launch.Proof.Base64Abi

theorem encode_eq :
    Launch.Base64Abi.encode = Fvdep.Abi.V1_0_0.encoder Fvdep.Base64.Encode.V1_0_0.encode := by
  simp only [Launch.Base64Abi.encode, Launch.Proof.Base64.encode_eq]

theorem encodeUrl_eq :
    Launch.Base64Abi.encodeUrl =
      Fvdep.Abi.V1_0_0.encoder Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl := by
  simp only [Launch.Base64Abi.encodeUrl, Launch.Proof.Base64.encodeUrl_eq]

theorem decode_eq :
    Launch.Base64Abi.decode = Fvdep.Abi.V1_0_0.decoder Fvdep.Base64.Decode.V1_0_0.decode := by
  simp only [Launch.Base64Abi.decode, Launch.Proof.Base64.decode_eq]

theorem decodeUrl_eq :
    Launch.Base64Abi.decodeUrl =
      Fvdep.Abi.V1_0_0.decoder Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl := by
  simp only [Launch.Base64Abi.decodeUrl, Launch.Proof.Base64.decodeUrl_eq]

end Launch.Proof.Base64Abi
