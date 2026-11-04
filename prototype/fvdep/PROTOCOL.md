# Adapter protocol (prototype)

An implementation is checked through a small adapter: a program that reads
requests on stdin and writes one reply line per request on stdout.

- Request: `op<TAB>arg[<TAB>arg]`, one per line.
- Reply: `ok<TAB>result`, `err` when the spec rejects the input, or
  `unsupported` when the operation is not implemented.
- Bytes travel as lowercase hex.

The reference oracle (`library/Oracle.lean`, compiled from the Lean specs)
speaks the same protocol. `fvdep check` sends the same requests to both and
compares the replies line by line.

Operations per spec version are listed in `library/catalog/<dep>/<version>.toml`.
