import Launch.Proof.Base64

/-! U7 R: `native_decide` — A names the compiler's axiom. -/

theorem R.Native.encode_eq : Launch.Base64.encode = Fvdep.Base64.Encode.V1_0_0.encode := by
  have _h : (2 : Nat) + 2 = 4 := by native_decide
  exact Launch.Proof.Base64.encode_eq
