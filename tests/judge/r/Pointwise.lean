import Launch.Proof.Base64

/-! U7 R: a pointwise theorem — S refuses its statement. -/

theorem R.Pointwise.encode_eq :
    ∀ bs, Launch.Base64.encode bs = Fvdep.Base64.Encode.V1_0_0.encode bs :=
  fun bs => congrFun Launch.Proof.Base64.encode_eq bs
