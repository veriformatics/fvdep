import Fvdep.Registry.Types.V1
import Fvdep.Semver.Compare.V1_0_0

/-! Registry entry `semver.compare@1.0.0` (`docs/library.md` Registry). -/

namespace Fvdep.Registry.Semver.Compare.V1_0_0

def entry : Fvdep.Registry.Types.V1.Module where
  id := "semver.compare"
  version := "1.0.0"
  spec := ``Fvdep.Semver.Compare.V1_0_0.compare
  obligations :=
    [``Fvdep.Semver.Compare.V1_0_0.swap, ``Fvdep.Semver.Compare.V1_0_0.trans,
      ``Fvdep.Semver.Compare.V1_0_0.eqIff, ``Fvdep.Semver.Compare.V1_0_0.precedence]
  abi := none
  compat := none

end Fvdep.Registry.Semver.Compare.V1_0_0
