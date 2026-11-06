# Adapter protocol (prototype)

A differential check runs an implementation through a small adapter. The adapter is a program
that reads requests on stdin and writes one reply line for each request on stdout.

- Request: `op<TAB>arg[<TAB>arg]`, one per line. `op` is the operation of the spec module
  (`base64.decode` → `decode`).
- Reply: `ok<TAB>result`, `err` when the input is rejected, or `unsupported` when the
  operation is not implemented.
- Bytes travel as lowercase hex.

The reference oracle (`library/Oracle.lean`, compiled from the Lean library) speaks the same
protocol. Its argument selects a spec module (`base64.decode@1.0.0`) or the model of a package
profile (`npm:base64-js@1.5.1`). `fvdep check` sends the same requests to the oracle and to
the implementation and compares the replies line by line. `fvdep profile --check` does the same
for a real package (`packages/`) and the model of its profile.

A differential check is development evidence. Delivery needs a Lean proof (`fvdep check --lean`).
The operation of each module is listed in `library/catalog/<module>/<version>.toml`.
