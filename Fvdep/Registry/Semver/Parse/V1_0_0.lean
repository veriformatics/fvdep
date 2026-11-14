import Fvdep.Registry.Types.V1
import Fvdep.Semver.Parse.V1_0_0

/-! Registry entry `semver.parse@1.0.0` (`docs/library.md` Registry). -/

namespace Fvdep.Registry.Semver.Parse.V1_0_0

def entry : Fvdep.Registry.Types.V1.Module where
  id := "semver.parse"
  version := "1.0.0"
  spec := ``Fvdep.Semver.Parse.V1_0_0.parse
  obligations :=
    [``Fvdep.Semver.Parse.V1_0_0.onlyValid, ``Fvdep.Semver.Parse.V1_0_0.canonical,
      ``Fvdep.Semver.Parse.V1_0_0.complete]
  abi := none
  compat := none

end Fvdep.Registry.Semver.Parse.V1_0_0
