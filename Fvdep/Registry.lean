import Fvdep.Registry.Base64.Decode.V1_0_0
import Fvdep.Registry.Base64.DecodeUrl.V1_0_0
import Fvdep.Registry.Base64.Encode.V1_0_0
import Fvdep.Registry.Base64.EncodeUrl.V1_0_0
import Fvdep.Registry.ProfileTypes.V1
import Fvdep.Registry.Semver.Compare.V1_0_0
import Fvdep.Registry.Semver.Parse.V1_0_0

/-! The library's root registry (`docs/library.md` Registry): every operation entry once, then
every profile entry once. `fvdep index` reads both lists. -/

namespace Fvdep.Registry

def modules : List Fvdep.Registry.Types.V1.Module :=
  [Fvdep.Registry.Base64.Encode.V1_0_0.entry, Fvdep.Registry.Base64.Decode.V1_0_0.entry,
    Fvdep.Registry.Base64.EncodeUrl.V1_0_0.entry, Fvdep.Registry.Base64.DecodeUrl.V1_0_0.entry,
    Fvdep.Registry.Semver.Parse.V1_0_0.entry, Fvdep.Registry.Semver.Compare.V1_0_0.entry]

def profiles : List Fvdep.Registry.ProfileTypes.V1.Profile := []

end Fvdep.Registry
