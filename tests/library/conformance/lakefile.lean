import Lake

open Lake DSL

/-- Contract U4 A8, the conformance trial: a consumer package built against the library alone, one
independent implementation per statement shape — `base64.encode` (`fn`: `@impl = @spec`) and
`base64.decode` (`abi`: `@impl = Fvdep.Abi.V1_0_0.decoder @spec`); implementation modules import
Init alone, proof modules any Lean (`Conformance.Audit` fails the build unless both theorems rest on
the standard axioms alone). -/
package «fvdep-conformance-trial» where
  leanOptions :=
  #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩]

require fvdep from "../../.."

@[default_target] lean_lib Conformance
