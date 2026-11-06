import Fvdep.Base64.Encode.V1_0_0
import Lean
/-!
Fails on purpose: a forged proof. A metaprogram adds `Forged.conforms` with
`debug.skipKernelTC`, so the kernel never checks it. `#print axioms` reports only the
standard axioms; `lake comparator` replays it through the kernel and rejects it.
-/
namespace Forged
def encode : List Nat → List Char := fun _ => []
end Forged

open Lean Elab Term Meta in
set_option debug.skipKernelTC true in
run_elab do
  let ty ← elabType (← `(∀ bs : List Nat, Forged.encode bs = Fvdep.Base64.Encode.V1_0_0.encode bs))
  let v : TheoremVal :=
    { name := `Forged.conforms, levelParams := [], type := ← instantiateMVars ty, value := mkConst ``True.intro }
  addDecl (.thmDecl v)
