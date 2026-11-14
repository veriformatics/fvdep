import Conformance.Encode
import Fvdep.Base64.Encode.V1_0_0

/-! `Conformance.Encode.encode` = `base64.encode@1.0.0` (contract U4 A8, shape `fn`). -/

namespace Conformance.Proof.Encode

open Fvdep.Base64.Rfc4648.V1_0_0 Conformance.Encode

set_option maxRecDepth 8000 in
theorem sym_eq : ∀ i, i < 64 → sym i = symbol standard i := by decide

theorem encode_list : ∀ b : List UInt8, encode b = encodeWith standard b
  | x :: y :: z :: rest => by
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    have hz := z.toNat_lt
    have e0 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) / 262144 = x.toNat / 4 := by omega
    have e1 :
        (x.toNat * 65536 + y.toNat * 256 + z.toNat) / 4096 % 64 =
          x.toNat % 4 * 16 + y.toNat / 16 := by omega
    have e2 :
        (x.toNat * 65536 + y.toNat * 256 + z.toNat) / 64 % 64 = y.toNat % 16 * 4 + z.toNat / 64 :=
      by omega
    have e3 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) % 64 = z.toNat % 64 := by omega
    simp only [encode, encodeWith, e0, e1, e2, e3, encode_list rest,
      sym_eq _ (by omega : x.toNat / 4 < 64),
      sym_eq _ (by omega : x.toNat % 4 * 16 + y.toNat / 16 < 64),
      sym_eq _ (by omega : y.toNat % 16 * 4 + z.toNat / 64 < 64),
      sym_eq _ (by omega : z.toNat % 64 < 64)]
  | [x, y] => by
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    have e0 : (x.toNat * 65536 + y.toNat * 256) / 262144 = x.toNat / 4 := by omega
    have e1 : (x.toNat * 65536 + y.toNat * 256) / 4096 % 64 = x.toNat % 4 * 16 + y.toNat / 16 := by
      omega
    have e2 : (x.toNat * 65536 + y.toNat * 256) / 64 % 64 = y.toNat % 16 * 4 := by omega
    simp only [encode, encodeWith, e0, e1, e2, sym_eq _ (by omega : x.toNat / 4 < 64),
      sym_eq _ (by omega : x.toNat % 4 * 16 + y.toNat / 16 < 64),
      sym_eq _ (by omega : y.toNat % 16 * 4 < 64)]
  | [x] => by
    have hx := x.toNat_lt
    have e0 : x.toNat * 65536 / 262144 = x.toNat / 4 := by omega
    have e1 : x.toNat * 65536 / 4096 % 64 = x.toNat % 4 * 16 := by omega
    simp only [encode, encodeWith, e0, e1, sym_eq _ (by omega : x.toNat / 4 < 64),
      sym_eq _ (by omega : x.toNat % 4 * 16 < 64)]
  | [] => rfl

/-- The `fn` statement: `@impl = @spec`. -/
theorem encode_eq : Conformance.Encode.encode = Fvdep.Base64.Encode.V1_0_0.encode :=
  funext encode_list

end Conformance.Proof.Encode
