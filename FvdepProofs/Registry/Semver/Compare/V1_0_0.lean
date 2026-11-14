import Fvdep.Registry.Semver.Compare.V1_0_0
import FvdepProofs.Semver.Compare.V1_0_0

/-! Proof registry (phase 2; `docs/library.md` Registry) of
`Fvdep.Registry.Semver.Compare.V1_0_0`. -/

namespace FvdepProofs.Registry.Semver.Compare.V1_0_0

def proofs : Fvdep.Registry.Types.V1.Proofs where
  obligations :=
    [(``Fvdep.Semver.Compare.V1_0_0.swap, ``FvdepProofs.Semver.Compare.V1_0_0.swap),
      (``Fvdep.Semver.Compare.V1_0_0.trans, ``FvdepProofs.Semver.Compare.V1_0_0.trans),
      (``Fvdep.Semver.Compare.V1_0_0.eqIff, ``FvdepProofs.Semver.Compare.V1_0_0.eqIff),
      (``Fvdep.Semver.Compare.V1_0_0.precedence, ``FvdepProofs.Semver.Compare.V1_0_0.precedence)]
  compat := none

end FvdepProofs.Registry.Semver.Compare.V1_0_0
