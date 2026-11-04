# fvdep prototype

This prototype shows the fvdep idea from end to end. It has a library of formal
specs for popular dependencies, example implementations, and a command-line tool.
The tool checks an implementation against a spec and follows spec updates.

## Run it

You need `lean` 4.35.0 with `lake`, `uv`, `python3` and `cargo`.

To see every command on a throwaway copy of the demo project, run:

    ./tour.sh

To run one command, use the `fvdep` wrapper in this folder:

    ./fvdep list
    ./fvdep show base64@1.1.0
    ./fvdep check base64@1.0.0 -- python3 -I impls/python/base64_strict.py
    ./fvdep check base64@1.0.0 --lean impls/lean:Base64Acc.conforms

The first run builds the Lean library and the oracle. This takes about two minutes.

## What is here

- `library/` holds the specs in Lean 4. Each spec is an executable model plus
  theorems (the obligations). `library/catalog/` lists each spec version.
- `library/Oracle.lean` compiles the specs into a reference program. The check
  sends the same requests to this program and to an implementation.
- `impls/` holds example implementations in Python, Rust and Lean.
  `impls/python/base64_stdlib.py` fails on purpose: Python's standard library
  accepts non-canonical base64 text, and the spec does not.
- `demo/` is an example consumer project with `fvdep.toml`.
- `PROTOCOL.md` describes how an implementation talks to the checker.

## What is not real yet

- `fvdep request` only saves the request in `.state/requests.jsonl`. No order
  service exists.
- A Lean implementation check audits the axioms of the theorem that you name.
  It does not yet confirm that the theorem states conformance to the spec.
- Two semver obligations are open (not proven). `fvdep show semver` marks them.
- The `fvdep` tool itself is Python and is not formally verified.
