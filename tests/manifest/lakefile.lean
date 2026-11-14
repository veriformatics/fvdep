import Lake

open Lake DSL

package «fvdep-manifest-tests» where leanOptions := #[⟨`autoImplicit, false⟩]

require fvdeptool from "../../tool"

@[default_target] lean_exe «manifest-driver» where root := `Driver
