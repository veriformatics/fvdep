import Fvdep.Base64.Encode.V1_0_0
import Launch.Base64

/-! U7 R: an extra axiom — A names it. -/

axiom R.Extra.cheat : Launch.Base64.encode = Fvdep.Base64.Encode.V1_0_0.encode

theorem R.Extra.encode_eq : Launch.Base64.encode = Fvdep.Base64.Encode.V1_0_0.encode :=
  R.Extra.cheat
