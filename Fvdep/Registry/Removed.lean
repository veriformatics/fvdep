import Fvdep.Registry.Types.V1

/-! Removed-entry records (`docs/library.md` Registry; Decisions Lifecycle): an entry leaves the
tree only through a toolchain bump it fails, with a notice; records are appended, never edited
(gate stage `index-history`). -/

namespace Fvdep.Registry

def removed : List Fvdep.Registry.Types.V1.Removed := []

end Fvdep.Registry
