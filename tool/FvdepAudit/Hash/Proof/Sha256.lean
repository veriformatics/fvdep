import FvdepIO.Sha256

/-! S3: the streaming byte count's saturation law (the C limit check then aborts every over-limit
stream; HACL* + the shim = tested residue `hacl-sha256`). -/

namespace FvdepAudit.Hash.Proof

open FvdepIO.Hash

/-- S3: `saturate n = min n (2^64 − 1)`, never wrapped. -/
theorem saturate_toNat (n : Nat) : (Sha256.saturate n).toNat = min n (UInt64.size - 1) := by
  unfold Sha256.saturate
  split
  · simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt ‹n < UInt64.size›]
    omega
  · simp only [UInt64.toNat_ofNat']
    simp [UInt64.size] at *
    omega

end FvdepAudit.Hash.Proof
