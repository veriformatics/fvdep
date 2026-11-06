#!/bin/sh
# Guided run of every fvdep command on a throwaway copy of demo/ + its own state dir.
# Tracked files stay unchanged; the Lean, Cargo and pnpm build caches in the repo are reused.
set -e
HERE=$(dirname "$(readlink -f "$0")")
F="$HERE/fvdep"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
export FVDEP_STATE="$T/state"
cp -r "$HERE/demo" "$HERE/impls" "$T/"
ln -s "$HERE/library" "$T/library"  # impls/lean requires ../../library
rm -rf "$T/impls/rust/base64/target" "$T/impls/rust/base64-ffi/target" "$T/impls/lean/.lake" "$T/impls/lean-forged/.lake"
cd "$T/demo"
note() { printf '\n# %s\n' "$*"; }
step() { printf '\n\033[1m$ fvdep %s\033[0m\n' "$*"; "$F" "$@" || true; }
note "The library: one spec module per operation, plus profiles of real packages."
step list
step show base64.decode
note "How real packages differ from the contract. The model of each package is checked against the package."
step profile npm:base64-js --check
step profile cpython:base64
note "Delivery = a proof. fvdep writes the statement (impl = spec) and audits the axioms of the proof."
step check base64.encode@1.0.0 --lean ../impls/lean:Base64Acc --impl Base64Acc.encode --proof Base64Acc.conforms
note "Other languages call the proven Lean code as a C library. The export is proven; the binding is tested."
step check base64.encode@1.0.0 --ffi ../impls/lean:Base64Ffi --impl Base64Ffi.encode --proof Base64Ffi.encode_abi -- node ../impls/node/base64-ffi/adapter.mjs
note "A forged proof: #print axioms looks clean, but the kernel replay in lake comparator rejects it."
step check base64.encode@1.0.0 --lean ../impls/lean-forged:Forged --impl Forged.encode --proof Forged.conforms
note "A differential run against the spec oracle is development evidence. It finds the Python stdlib deviation."
step check base64.decode@1.0.0 -- python3 -I "$HERE/packages/cpython-base64.py"
step lock
step lock --require-proof
step outdated
step diff base64.decode 1.0.0 1.1.0
step upgrade base64.decode
note "base64.decode_url is a new module. The Python implementation lacks it; the Rust one has it."
step check base64.decode_url@1.0.0 -- python3 -I ../impls/python/base64_strict.py
step check base64.decode_url@1.0.0 -- cargo run --release -q --manifest-path ../impls/rust/base64/Cargo.toml
step scan "$HERE/demo"
step request npm:ajv --lang rust
