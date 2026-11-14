import Fvdep.Registry.Base64.DecodeUrl.V1_0_0
import FvdepProofs.Base64.DecodeUrl.V1_0_0

/-! Proof registry (phase 2; `docs/library.md` Registry) of
`Fvdep.Registry.Base64.DecodeUrl.V1_0_0`. -/

namespace FvdepProofs.Registry.Base64.DecodeUrl.V1_0_0

def proofs : Fvdep.Registry.Types.V1.Proofs where
  obligations :=
    [(``Fvdep.Base64.DecodeUrl.V1_0_0.inverse, ``FvdepProofs.Base64.DecodeUrl.V1_0_0.inverse),
      (``Fvdep.Base64.DecodeUrl.V1_0_0.canonical, ``FvdepProofs.Base64.DecodeUrl.V1_0_0.canonical)]
  compat := none

end FvdepProofs.Registry.Base64.DecodeUrl.V1_0_0
