#!/bin/sh
# Guided run of every fvdep command on a throwaway copy of demo/ (the repo stays untouched).
set -e
HERE=$(dirname "$(readlink -f "$0")")
F="$HERE/fvdep"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
cp -r "$HERE/demo" "$HERE/impls" "$T/"
rm -rf "$T/impls/rust/base64/target" "$T/impls/lean/.lake"
RUST="cargo run --release -q --manifest-path ../impls/rust/base64/Cargo.toml"
cd "$T/demo"
step() { printf '\n\033[1m$ fvdep %s\033[0m\n' "$*"; "$F" "$@" || true; }
step list
step show base64
step check base64@1.0.0 -- python3 -I "$HERE/impls/python/base64_stdlib.py"
step check base64@1.0.0 --lean "$HERE/impls/lean:Base64Acc.conforms"
step lock
step outdated
step diff base64 1.0.0 1.1.0
step upgrade base64
printf '\n# Point base64 at the Rust implementation (it supports base64@1.1.0), then upgrade again.\n'
sed -i "s#python3 -I ../impls/python/base64_strict.py#$RUST#" fvdep.toml
step upgrade base64
step outdated
step scan "$HERE/demo"
step request npm:ajv --lang rust
