---
paths:
  - "**/*.lean"
---

# Lean 4.35 (this toolchain, this repo)

- Layout = lean-fmt's (gate stage `lean-style`; `declaration-body = "same-line"`, width 100): reformat with `tools/vflab-run bash -c '(cd tools/lean-fmt && lake build «lean-fmt») && B=$PWD/tools/lean-fmt/.lake/packages/lean-fmt/.lake/build/bin/lean-fmt && $B format && (cd tool && $B format)'`, then copy the files back; it breaks `else if` chains into nested `else` blocks ⇒ long chains read better as `match` or early returns.
- leanOptions (both lakefiles) carry autoImplicit off, relaxedAutoImplicit off, warningAsError + the extra core linters (`linter.extra.*`, `linter.redundantVisibility`): a lint is a build error. No Mathlib/Batteries: `swap` is unknown ⇒ `case neg =>` after `by_cases`; a contradiction = `Classical.byContradiction fun bad => …`.
- A Lake `require x` declares the name `x` ⇒ a target of that name collides; the tool's exe target is `«fvdep-cli»` with `exeName := "fvdep"`.
- Structure literals: every field at or right of the first field's column, else `unexpected identifier; expected '}'` ⇒ one field per line after `{ x with` / `{`.
- `section`, `scoped`, `local`, `at` = keywords: never variable/field/hypothesis names.
- `if` on a mixed Bool/Prop condition can fail Decidable synthesis ⇒ Bool operators (`&&`, `||`, `!`, `!=`); membership in a Bool context ⇒ `xs.contains x`.
- `if` guards do not reduce reliably under `rw [if_pos]`/`split` ⇒ `rcases` the head + `cases` the stream, then `simp_all [def, Bind.bind, Except.bind]`; `if_pos`/`if_neg` are deprecated (errors here) ⇒ state the reduced form by defeq or use `ite_eq_left`/`ite_eq_right`.
- Recursion inside a tactic proof: `match` on the decreasing argument (tactic `match`), not `rcases`/`cases`, or `termination_by` loses the equation.
- `return` inside `let x ← match …` arms exits the enclosing `do`; `let some x := e | alt` is do-notation only.
- `rcases h : f _ … with …` leaves `_` an unresolved metavariable ⇒ spell the argument or `split at` the unfolded bind chain.
- `decide` needs a closed goal with a `Decidable` instance ⇒ `show` the closed literal form first. `native_decide` adds an axiom outside {propext, Classical.choice, Quot.sound} ⇒ never.
- A do-block `let x := e` becomes `have x := e`: hidden from `cases e`/`rw` until `simp only [f]` (zeta) exposes it; do join points block `split` the same way ⇒ `simp only [f] at h`, then `split at h`.
- `cases h` on `some a = some b` (both locals) may eliminate the variable you need ⇒ `have e := Option.some.inj h; subst e`; on an equation between non-variable constructor arguments ⇒ `simp only [….injEq] at h`.
- `cases` takes comma-separated targets: inside `⟨fun x => by cases x, …⟩` the comma reads as a second target ⇒ parenthesize every `fun … => by …` field.
- Name constructor implicits with `| @ctor a b h =>`; `rename_i` renames the most recent inaccessibles, often anonymous proofs.
- Formal premises that stay visible by ruling are theorem arguments, never axioms or `sorry`.
- Compiled allocation hides in runtime primitives: a `Nat` literal ≥ 2^32 (also a folded def such as `2 ^ 53 - 1`, inlined at each use) compiles to a GMP parse at every evaluation — `@[noinline]` on such a constant keeps its uses on the global, initialized once (an attribute: proofs + statements untouched; `FvdepCore.Json.maxInt`); `String.toList` builds a C++ vector ⇒ a cost model reads the compiled C (`.lake/build/ir/**.c`), never the Lean source alone.
