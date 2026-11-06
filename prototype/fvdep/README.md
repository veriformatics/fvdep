# fvdep prototype

This prototype shows the fvdep idea from end to end. It has a library of formal
specs for popular dependencies, example implementations, and a command-line tool.
The tool checks an implementation against a spec and follows spec updates.

## Run it

You need `lean` 4.35.0 with `lake`, `bwrap`, `rsync`, `uv`, `python3`, `cargo`, `node`
and `pnpm`.

To see every command on a throwaway copy of the demo project, run:

    ./tour.sh

To run one command, use the `fvdep` wrapper in this folder:

    ./fvdep list
    ./fvdep show base64.decode
    ./fvdep profile npm:base64-js --check
    ./fvdep check base64.encode@1.0.0 --lean impls/lean:Base64Acc --impl Base64Acc.encode --proof Base64Acc.conforms
    ./fvdep check base64.decode@1.0.0 -- python3 -I impls/python/base64_strict.py

The first run builds the Lean library and the oracle. This takes about two minutes.

## Ideas

- **Spec modules.** Each operation is its own spec module with its own version, for
  example `base64.encode@1.0.0` and `base64.decode@1.1.0`. A project pins only the
  modules that it uses, in `fvdep.toml`.
- **Delivery needs a proof.** An implementation is delivered only when a Lean proof
  shows that it equals the spec. fvdep writes the statement `impl = spec` itself, so a
  proof of a different statement fails. `lake comparator` then judges the proof in a
  sandbox, against a statement that fvdep built from its own copy of the library. The
  kernel checks the proof again, and only the standard axioms are permitted.
- **Kernel replay.** Before fvdep reports the status of an obligation, `leanchecker`
  replays the whole library through the Lean kernel. A metaprogram can add a theorem
  that the kernel never checked, and `#print axioms` alone does not show this.
- **Development evidence.** A differential check sends the same requests to the
  implementation and to an oracle compiled from the spec. A match is useful while you
  build, but it does not deliver the implementation. `fvdep lock --require-proof`
  fails while a module has development evidence only.
- **Package profiles.** A profile describes how a real package differs from the
  contract. It contains a Lean model of the package, a named deviation with a
  kernel-checked example for each difference, and theorems that relate the model to
  the contract. `fvdep profile <package> --check` compares the model with the real
  package.
- **Updates.** A new module version can prove that its behaviour is unchanged. Then a
  proof against the old version carries over, and `fvdep upgrade` shows this.

## What is here

- `library/` holds the specs in Lean 4. `library/catalog/` lists each module version.
  `library/profiles/` lists each package profile. `library/Oracle.lean` compiles the
  specs and the profile models into a reference program.
- `impls/` holds example implementations. `impls/lean/Base64Acc.lean` is proven
  against `base64.encode` and `base64.decode`. The Python and Rust implementations
  have development evidence only. `impls/lean-forged/` fails on purpose: its proof
  passes `#print axioms` but not the kernel replay.
- `packages/` holds adapters for the real packages that the profiles describe:
  CPython `base64`, npm `base64-js` and the Rust `base64` crate.
- `demo/` is an example consumer project with `fvdep.toml`.
- `PROTOCOL.md` describes how an adapter talks to the checker.

## What is not real yet

- `fvdep request` only saves the request in `.state/requests.jsonl`. No order
  service exists.
- The Lean check copies the implementation project and puts a copy of the library in
  it, because the sandbox of `lake comparator` hides your home directory. A real
  project gets the library from a pinned Git revision. The project must use
  `lakefile.toml`, and `bwrap` must be installed.
- A proof covers equality of Lean functions on `List Nat` and `List Char`. Python,
  Rust and other languages have no proof route yet.
- The `base64-js` profile does not yet prove that it agrees with the contract on
  valid input, and no theorem states that its list of deviations is complete.
- Two semver obligations are open (not proven). `fvdep list` shows them.
- The model of a package is checked against the package by tests only. A profile is
  measured on one package version.
- The `fvdep` tool itself is Python and is not formally verified.
