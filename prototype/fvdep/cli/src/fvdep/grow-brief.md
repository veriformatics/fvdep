# fvdep growth brief: package profile for `{package}` version `{version}`

You are the drafting agent of fvdep's growth loop ("agent drafts, kernel admits"). cwd = a staging copy
of the fvdep prototype (`library/` = Lean 4.35.0 lake package, core only, no Mathlib; `packages/` =
real-package adapters; `./fvdep` = the CLI). Work only inside cwd. Finish line: `./fvdep admit .`
prints `ADMITTED` and the new profile shows `published` in `./fvdep list`.

## Contract modules in the library (id: title; open obligations)

{modules}

## Deliverables

1. Real-package adapter `packages/<eco>-<name>/` (own manifest + lockfile, pinned to `{version}`)
   speaking `PROTOCOL.md`: one request line in → one reply line out, ops named after the contract
   modules' `op` (see each `library/catalog/<module>/<version>.toml`). Map the package's own API to
   each op; a thrown error / null / invalid result = `err`.
2. Lean model `library/Fvdep/Profiles/<Pkg>/V<x_y_z>.lean` (namespace
   `Fvdep.Profiles.<Pkg>.V<x_y_z>`): one function per op, same type as the contract's `fn`, written to
   behave exactly like the real package (port its algorithm; read its source in the adapter's
   installed package). Theorems relating each op to the contract:
   - an exact characterization (`complete = true` relation), e.g. `model s = contract (normalize s)` or
     `model = contract` — it states the full set of deviations;
   - `agrees` where it holds (contract accepts ⇒ package returns the same), else a deviation saying so;
   - one named deviation per difference, each with a witness theorem
     `model w = … ∧ contract w = …` proven by `decide`/`rfl`.
3. Profile TOML `library/profiles/<eco>/<name>/{version}.toml`, same schema as
   `library/profiles/cpython/base64/3.14.toml` (`package`, `version`, `title`, `measured`, `lean`,
   `source`, `adapter`, optional `setup`, `[[ops]]` with `op`, `api`, `contract`, `relations`
   (`complete = true` on the exact one), `[[ops.deviations]]` with `name`, `says`, `witness`, `theorem`).
4. Oracle: add a `handler` line for `{package}@{version}` in `library/Oracle.lean` and the import in
   `library/Fvdep.lean`.
5. Open obligations of the contract modules you use: prove them. A version is immutable, so publish a
   new version `<module>@<x.y+1.0>` (new Lean file + catalog TOML) with `[compat]` (theorem
   `unchanged : new = old := rfl`), every obligation proven, and point your profile at it. An open
   obligation may be false as stated: then state the corrected property (e.g. restricted to valid
   inputs), prove it, and say why in its docstring. Add the new modules to `library/Fvdep.lean` + an
   oracle handler.

## Rules

- Never edit an existing versioned file (`V*_*_*.lean`, `catalog/*/*.toml`, `profiles/*/*/*.toml`);
  `./fvdep admit .` rejects it. `Oracle.lean` and `Fvdep.lean` may gain lines.
- Proofs: standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, `native_decide`,
  `axiom`, `debug.skipKernelTC`, `implemented_by`, `extern`. The gate replays everything through the kernel.
- Lean docstrings + TOML `says` lines = plain English for a reader who does not know Lean.
- Self-check loop: `cd library && lake build`; `./fvdep profile {package}@{version} --check` (model vs real
  package, must print `MODEL MATCHES`; raise `--cases 2000` and try `--seed 2..4`); `./fvdep admit .`.
- End with a short report: files added, deviations found, proofs closed, any statement you corrected.
