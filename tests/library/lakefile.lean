import Lake

open Lake DSL

package «fvdep-library-tests» where leanOptions := #[⟨`autoImplicit, false⟩]

require fvdeptool from "../../tool"

lean_lib LibraryHarness

@[default_target] lean_exe «library-driver» where root := `Driver
