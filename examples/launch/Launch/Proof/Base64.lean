import Launch.Base64
import Fvdep.Base64.Decode.V1_0_0
import Fvdep.Base64.DecodeUrl.V1_0_0
import Fvdep.Base64.Encode.V1_0_0
import Fvdep.Base64.EncodeUrl.V1_0_0

/-! Launch proofs (contract U7 E): the base64 accumulator implementations = the library's specs. -/

namespace Launch.Proof.Base64

open Fvdep.Base64.Rfc4648.V1_0_0

theorem encodeAcc_eq (alphabet : List Char) :
    ∀ (bs : List UInt8) (acc : List Char),
      Launch.Base64.encodeAcc alphabet bs acc = acc ++ encodeWith alphabet bs
  | a :: b :: c :: rest, acc => by
    rw [Launch.Base64.encodeAcc, encodeWith, encodeAcc_eq alphabet rest]
    simp [Launch.Base64.group]
  | [a, b], acc => by simp [Launch.Base64.encodeAcc, encodeWith]
  | [a], acc => by simp [Launch.Base64.encodeAcc, encodeWith]
  | [], acc => by simp [Launch.Base64.encodeAcc, encodeWith]

theorem decodeAcc_eq (alphabet : List Char) :
    ∀ (s : List Char) (acc : List UInt8),
      Launch.Base64.decodeAcc alphabet s acc = (decodeWith alphabet s).map (acc ++ ·)
  | [], acc => by simp [Launch.Base64.decodeAcc, decodeWith]
  | [c0, c1, c2, c3], acc => by simp [Launch.Base64.decodeAcc, decodeWith]
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest, acc => by
    have ih := decodeAcc_eq alphabet (c4 :: rest)
    cases hq : quad alphabet c0 c1 c2 c3 with
    | none => simp [Launch.Base64.decodeAcc, decodeWith, hq]
    | some q =>
      simp only [Launch.Base64.decodeAcc, hq, ih]
      simp only [decodeWith, hq, List.isEmpty_cons, Bool.false_eq_true, if_false]
      cases decodeWith alphabet (c4 :: rest) <;> simp
  | [c0], acc => by simp [Launch.Base64.decodeAcc, decodeWith]
  | [c0, c1], acc => by simp [Launch.Base64.decodeAcc, decodeWith]
  | [c0, c1, c2], acc => by simp [Launch.Base64.decodeAcc, decodeWith]

theorem encode_eq : Launch.Base64.encode = Fvdep.Base64.Encode.V1_0_0.encode := by
  funext bs
  simp [Launch.Base64.encode, Fvdep.Base64.Encode.V1_0_0.encode, encodeAcc_eq]

theorem encodeUrl_eq : Launch.Base64.encodeUrl = Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl := by
  funext bs
  simp [Launch.Base64.encodeUrl, Fvdep.Base64.EncodeUrl.V1_0_0.encodeUrl, encodeAcc_eq]

theorem decode_eq : Launch.Base64.decode = Fvdep.Base64.Decode.V1_0_0.decode := by
  funext s
  simp [Launch.Base64.decode, Fvdep.Base64.Decode.V1_0_0.decode, decodeAcc_eq]

theorem decodeUrl_eq : Launch.Base64.decodeUrl = Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl := by
  funext s
  simp [Launch.Base64.decodeUrl, Fvdep.Base64.DecodeUrl.V1_0_0.decodeUrl, decodeAcc_eq]

end Launch.Proof.Base64
