import Lake

open Lake DSL

package «fvdep-sys-tests» where leanOptions := #[⟨`autoImplicit, false⟩]

require fvdeptool from "../../tool"

@[default_target] lean_exe «sys-extra» where root := `Extra
