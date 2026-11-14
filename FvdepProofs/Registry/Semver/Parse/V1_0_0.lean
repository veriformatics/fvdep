import Fvdep.Registry.Semver.Parse.V1_0_0
import FvdepProofs.Semver.Parse.V1_0_0

/-! Proof registry (phase 2; `docs/library.md` Registry) of
`Fvdep.Registry.Semver.Parse.V1_0_0`. -/

namespace FvdepProofs.Registry.Semver.Parse.V1_0_0

def proofs : Fvdep.Registry.Types.V1.Proofs where
  obligations :=
    [(``Fvdep.Semver.Parse.V1_0_0.onlyValid, ``FvdepProofs.Semver.Parse.V1_0_0.onlyValid),
      (``Fvdep.Semver.Parse.V1_0_0.canonical, ``FvdepProofs.Semver.Parse.V1_0_0.canonical),
      (``Fvdep.Semver.Parse.V1_0_0.complete, ``FvdepProofs.Semver.Parse.V1_0_0.complete)]
  compat := none

end FvdepProofs.Registry.Semver.Parse.V1_0_0
