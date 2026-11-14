/-! Profile registry type (placeholder; contract U4 A2): the root registry's `profiles` list has
this type. No entry identity covers this module (only the root registry imports it), so U10 defines
its fields before the first profile entry is indexed. -/

namespace Fvdep.Registry.ProfileTypes.V1

structure Profile where
  id : String
  version : String

end Fvdep.Registry.ProfileTypes.V1
