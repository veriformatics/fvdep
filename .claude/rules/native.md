---
paths:
  - "vendor/**"
  - "c/**"
  - "tools/vendor-hacl.sh"
  - "tools/check-vendor.sh"
---

# Vendored C + fvdep's native code (contract `docs/contracts/U3-codecs.md` S1–S5)

- `vendor/<upstream>/` = upstream bytes, never edited: `lock.json` pins upstream, commit + each file's sha256; stage `vendor` (`tools/check-vendor.sh`) = every locked file present with its digest + nothing else (local); stage `vendor-upstream` (`bash tools/vendor-hacl.sh --check`) = a fresh fetch of the locked commit yields exactly the lock + the tree (network, writes nothing). `bash tools/vendor-hacl.sh` (no argument) re-vendors the locked commit, rc 1 unless it reproduces the lock; `bash tools/vendor-hacl.sh <commit>` relocks = a bump (Renovate's `git-refs` manager moves `commit` alone ⇒ red on `vendor-upstream` until relocked in the same PR), decided by the gate's SHA-256 tests. The script's loop variables (`fmode`, `ftype`) stay distinct from its run mode (`action`): a shared name turns `--check` into a relock. `.gitignore` re-includes `vendor/**/dist/` past its `dist/` rule.
- Each vendored upstream: a `docs/dependencies.md` row (stage `deps`), a Renovate manager (stage `renovate`), an OSV query by its locked commit (stage `vulns`).
- `c/` = fvdep's own C, built by `tool/lakefile.lean` with the toolchain clang (`-std=gnu11 -O3 -fPIC -Wall -Wextra -Werror`; HACL keeps its own warning policy), every header in the Lake trace (`cTrace`), linked through `FvdepIO`'s `moreLinkObjs`. `c/fvdep_sha256_core.{h,c}` stays Lean-free (the sanitizer + fuzz harnesses' surface); its limits are `-D` macros (S3), so test builds lower all three.
- Every `@[extern]` declaration lies in a residue's ledger `boundary` (`tool/FvdepLedger/Rows.lean`; `hacl-sha256` = the four SHA-256 externs): a new extern joins its residue's list or the `compiled` check fails.
