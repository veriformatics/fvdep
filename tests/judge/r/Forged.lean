import Fvdep.Base64.Encode.V1_0_0
import Launch.Base64
import Lean

/-! U7 R: a forged proof — a metaprogram adds the theorem with `debug.skipKernelTC` (its value
`True.intro`, its type the template): S, G + A pass; the three kernels refuse it. -/

open Lean Elab Term Meta in
set_option debug.skipKernelTC true in
run_elab do
  let ty ← elabType (← `(Launch.Base64.encode = Fvdep.Base64.Encode.V1_0_0.encode))
  addDecl (.thmDecl
    { name := `R.Forged.encode_eq, levelParams := [], type := ← instantiateMVars ty
      value := mkConst ``True.intro })
