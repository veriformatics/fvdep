import FvdepAudit.Oracle.Wire.Proof

/-! Proofs: the step's typed application (contract `docs/contracts/U5b-oracle.md` W5) with its
dictionaries supplied — `answer`, the `Serve` instances `resultServe` + `argServe`, the `Answer`
instances `plainAnswer` + `optionAnswer`. Which dictionaries + which spec function the generated
driver supplies = residue `oracle-driver`. -/

namespace FvdepAudit.Oracle.Wire.Proof

open FvdepCore.Protocol FvdepCore.Oracle FvdepAudit.Oracle.Wire.Spec

/-- W5: on a line that is the W1 layout of values of `f`'s argument types, `answer f` = `f`'s
served call on those values (`malformed` where it gives none); on any other line, `malformed`. -/
theorem answer_exact {F : Type} [Wire.Serve F] (f : F) (line : String) :
    (∀ xs : List Val,
        xs.map Val.ty = Wire.Serve.args F →
          line = argsLayout xs → Wire.answer f line = (Wire.Serve.call f xs).getD "malformed") ∧
      ((∀ xs : List Val, ¬(xs.map Val.ty = Wire.Serve.args F ∧ line = argsLayout xs)) →
        Wire.answer f line = "malformed") := by
  constructor
  · intro xs hty hl
    have h := (decodeArgs_exact (Wire.Serve.args F) line xs).2 ⟨hty, hl⟩
    simp [Wire.answer, h]
  · intro hnone
    cases h : Wire.decodeArgs (Wire.Serve.args F) line with
    | none => simp [Wire.answer, h]
    | some xs => exact absurd ((decodeArgs_exact _ _ _).1 h) (hnone xs)

/-- W5: a result served (`resultServe`): no argument types, its answer's result type; applied to
no value = its line, to any value = none. -/
theorem serve_result {β : Type} [Wire.Answer β] (b : β) (vs : List Val) (s : String) :
    Wire.Serve.args β = [] ∧
      Wire.Serve.rty β = Wire.Answer.rty β ∧
      (Wire.Serve.call b vs = some s ↔ vs = [] ∧ s = Wire.Answer.line b) := by
  refine ⟨rfl, rfl, ?_⟩
  cases vs <;> simp [Wire.Serve.call, eq_comm]

/-- W5: a function served (`argServe`), its argument's conversions exact: its argument's type
before the rest's; applied to `v :: vs` = `f x` applied to `vs` exactly when `v` is `x`'s value; to
no value = none. -/
theorem serve_arg {α β : Type} [Wire.Native α] [Wire.Serve β]
    (conv : ∀ (v : Val) (x : α), Wire.Native.ofVal v = some x ↔ v = Wire.Native.toVal x) (f : α → β)
    (v : Val) (vs : List Val) (s : String) :
    Wire.Serve.args (α → β) = Wire.Native.ty α :: Wire.Serve.args β ∧
      Wire.Serve.rty (α → β) = Wire.Serve.rty β ∧
      Wire.Serve.call f [] = none ∧
      (Wire.Serve.call f (v :: vs) = some s ↔
        ∃ x, v = Wire.Native.toVal x ∧ Wire.Serve.call (f x) vs = some s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show (Wire.Native.ofVal v).bind (fun a => Wire.Serve.call (f a) vs) = some s ↔ _
  constructor
  · intro h
    cases hx : (Wire.Native.ofVal v : Option α) with
    | none => simp [hx] at h
    | some x =>
      simp only [hx, Option.bind_some] at h
      exact ⟨x, (conv v x).1 hx, h⟩
  · rintro ⟨x, rfl, h⟩
    simp [(conv _ x).2 rfl, h]

/-- W2 + W5: a plain result (`plainAnswer`): its type = `.plain` of its representation's; its line
= W2's layout of `ok` its value. -/
theorem answer_plain {β : Type} [Wire.Native β] (b : β) :
    Wire.Answer.rty β = .plain (Wire.Native.ty β) ∧
      Wire.Answer.line b = resultLayout (.ok (Wire.Native.toVal b)) := ⟨rfl, printResult_eq _⟩

/-- W2 + W5: an optional result (`optionAnswer`): its type = `.option` of its representation's;
`some b`'s line = W2's layout of `ok` its value, `none`'s = W2's `err`. -/
theorem answer_option {β : Type} [Wire.Native β] (b : β) :
    Wire.Answer.rty (Option β) = .option (Wire.Native.ty β) ∧
      Wire.Answer.line (some b) = resultLayout (.ok (Wire.Native.toVal b)) ∧
      Wire.Answer.line (none : Option β) = resultLayout .err :=
  ⟨rfl, printResult_eq _, printNone_eq⟩

end FvdepAudit.Oracle.Wire.Proof
