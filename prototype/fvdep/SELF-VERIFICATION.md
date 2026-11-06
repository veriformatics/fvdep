# Plan: verify fvdep itself

The Intent says that the whole fvdep system must be formally verified. This plan
lists what a user relies on when fvdep says "delivered" or "published", and how each
part becomes proven or stays trusted with a stated reason.

## What a user relies on

A "delivered" label is correct only when all of these parts are correct:

1. The Lean kernel accepts only valid proofs.
2. The statement that fvdep writes says "this implementation equals this spec
   module", and it names the spec module that the user pinned.
3. `lake comparator` compares that statement with the proof and permits only the
   standard axioms.
4. The fvdep decision logic turns these results into labels: `PROVEN`, `delivered`,
   `published`, `ADMITTED`, the lock, and the upgrade classification.
5. For other languages: the Lean compiler, the Lean runtime, the C shim and the
   binding.
6. The spec says what the standard means. No proof can show this. Evidence comes
   from profiles of real packages and from differential checks.

Today only parts 1 and 3 come from mature tools. Part 2 is a text template, and
part 4 is Python.

## Steps

1. **Decision core in Lean.** Move part 4 into a Lean module `Fvdep.Core`. It contains
   the verdict, the labels, the publish rule, the admission rule, the lock
   transitions and the version classification, as pure functions over the results of
   the kernel and comparator. Prove these properties:
   - `delivered` is true only when comparator accepted the proof with the standard
     axioms.
   - `upgrade` changes the lock only after a passing check.
   - A profile is `published` exactly when each of its operations has a proven
     completeness theorem and all of its theorems are proven.
   - Admission never changes a published version.

   The Python command-line tool then only reads files, runs tools and prints text.
   It calls the compiled core in the same way that it calls the oracle today.
2. **Statements as terms.** `Fvdep.Core` builds the challenge statement as a Lean term
   from the catalog, and a theorem states its form (`impl = spec fn`, or the
   C ABI shape). This replaces the text template of part 2.
3. **Several kernels.** Admission runs `lake comparator --paranoid`. It checks every
   proof with Lean's kernel and with independent checkers that Lean ships:
   `lean4lean`, `nanoda` and others. One kernel defect then cannot admit a false entry
   alone.
4. **fvdep uses its own specs.** The tool compares versions with `semver.compare`
   and reads hashes and encodings through proven library modules. A defect in a
   proven module then shows up in fvdep itself.
5. **Stated trust.** Parts 5 and 6, the operating system, and the process runner stay
   trusted. Every label that depends on them names them, as the C library check does
   today.

## Not in scope

- A proof about Python, Node or Rust code that does not come from Lean.
- A proof that a spec matches the intent of a standard. Profiles, differential
  checks and review give evidence for this.
