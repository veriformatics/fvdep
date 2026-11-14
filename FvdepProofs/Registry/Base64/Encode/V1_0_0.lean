import Fvdep.Registry.Base64.Encode.V1_0_0
import FvdepProofs.Base64.Encode.V1_0_0

/-! Proof registry (phase 2; `docs/library.md` Registry) of
`Fvdep.Registry.Base64.Encode.V1_0_0`. -/

namespace FvdepProofs.Registry.Base64.Encode.V1_0_0

def proofs : Fvdep.Registry.Types.V1.Proofs where
  obligations :=
    [(``Fvdep.Base64.Encode.V1_0_0.bits, ``FvdepProofs.Base64.Encode.V1_0_0.bits),
      (``Fvdep.Base64.Encode.V1_0_0.length, ``FvdepProofs.Base64.Encode.V1_0_0.length)]
  compat := none

end FvdepProofs.Registry.Base64.Encode.V1_0_0
