import Conformance.Proof.Decode
import Conformance.Proof.Encode
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! The trial's verdict inside its build: both statements closed on the standard axioms alone
(`sorryAx` or any other axiom fails the build). -/

open Lean Elab Command in
run_cmd do
  for n in [``Conformance.Proof.Encode.encode_eq, ``Conformance.Proof.Decode.decode_eq] do
    let axioms ← liftCoreM (collectAxioms n)
    unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n} rests on {axioms}"
    logInfo m!"{n}: axioms {axioms}"
