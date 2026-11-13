import FvdepAudit.Json.Proof.Print.Builder
import FvdepAudit.Json.Proof.Print.Depth
import FvdepAudit.Json.Proof.Print.Grammar
import FvdepAudit.Json.Proof.Print.Normalize

namespace FvdepAudit.Json.Proof

open FvdepCore.Json

theorem print_exact : ∀ v : Value, (print v).data.toList = FvdepAudit.Json.Spec.canonical v := by
  intro v
  simpa [FvdepCore.Json.print] using printTo_exact ByteArray.empty v

theorem round_trip :
    ∀ v : Value,
      FvdepAudit.Json.Spec.Valid v →
        FvdepAudit.Json.Spec.Outcome (FvdepAudit.Json.Spec.canonical v) (.ok v) := by
  intro v hv
  obtain ⟨hi, hs, hd, hk⟩ := hv
  have hn := canonical_invariants v hk
  have ho :=
    FvdepAudit.Json.Spec.Outcome.ok
      (by
        rw [lexicalDepth_canonical]; exact hd)
      (canonical_text v hi) hs hn.2
  simpa only [hn.1] using ho

end FvdepAudit.Json.Proof
