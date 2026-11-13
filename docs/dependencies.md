# Dependencies — pin, update path, scanner (agent-read; gate stage `deps` holds every pin to a row)

| Dependency | Pinned in | Update path | Scanner / check |
|---|---|---|---|
| `leanprover/lean4` | `lean-toolchain`, `tool/lean-toolchain`, `tools/lean-fmt/lean-toolchain` (4.35.0) | Renovate custom regex manager, grouped with `jcreinhold/lean-fmt`; a bump requalifies the verification profile + the whole library before merge (`Decisions` → Lifecycle) | the gate's kernel-checked build + tests; CodeQL has no Lean extractor |
| `jcreinhold/lean-fmt` | `tools/lean-fmt/lake-manifest.json` (commit 57c2390, tag `v4.35.0`; Apache-2.0) | Renovate Lake manager (one tag per Lean toolchain, grouped with it); no tag for a new toolchain → style rules alone + a `.agent/deferred.md` row | runs in the gate alone (never shipped, never imported); third-party code executing in the vflab slice + CI runners, bounded by the commit pin + review of each bump |
| `elan-init` | `tools/tools.lock` (version + sha256) | Renovate custom manager (version column) + `tools/pin-tool.sh` (digest) | sha256 verified by `tools/fetch-tools.sh` before use |
| `actionlint` | `tools/tools.lock` | as `elan-init` | sha256 pin; it is itself the workflow linter |
| `betterleaks` | `tools/tools.lock` | as `elan-init` | sha256 pin; it is itself the secret scanner |
| `osv-scanner` | `tools/tools.lock` (raw binary) | as `elan-init` | sha256 pin; it is itself the vulnerability scanner (queries osv.dev) |
| `pyrefly` | `tools/tools.lock` (static-musl archive) | as `elan-init`; re-pin keeps the asset scheme | sha256 pin; type checking with explicit `pyrefly.toml` |
| `ruff` | `tools/tools.lock` (static-musl archive) | as `elan-init`; re-pin keeps the asset scheme | sha256 pin; Python correctness lint |
| `shellcheck` | `tools/tools.lock` | as `elan-init` | sha256 pin; it is itself the shell linter |
| `zizmor` | `tools/tools.lock` | as `elan-init` | sha256 pin; it is itself the workflow security auditor (offline audits) |
| `actions/checkout` | `.github/workflows/*.yml` (commit digest) | Renovate github-actions manager (`helpers:pinGitHubActionDigests`) | zizmor + actionlint; CodeQL `actions` |
| `github/codeql-action/init` | `.github/workflows/codeql.yml` (commit digest) | as `actions/checkout` | zizmor + actionlint; CodeQL `actions` |
| `github/codeql-action/analyze` | `.github/workflows/codeql.yml` (commit digest) | as `actions/checkout` | zizmor + actionlint; CodeQL `actions` |
| `git`, `bash`, coreutils, `curl`, `tar`, `rsync`, `ssh`, `python3` (stdlib), `jq`, `gh` | distribution packages (vflab Ubuntu 26.04, CI runners, the desktop) | the distribution's security updates | not pinned: the gate reads their output, never ships them |

Prototype lockfiles (`prototype/fvdep/**`, retired at U14) are scanned by stage `vulns` (`tools/lockfiles.txt`) and left out of Renovate (`renovate.json` `ignorePaths`).
