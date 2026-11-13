---
paths:
  - "tools/**"
  - "tests/**"
  - ".github/**"
  - "renovate.json"
  - "lakefile.lean"
  - "tool/lakefile.lean"
  - "ruff.toml"
  - "pyrefly.toml"
  - ".lean-fmt.toml"
  - "tool/.lean-fmt.toml"
---

# Purpose-built checks + their probes

- An edit to a check (gate registry + aggregation + step ledger, `tree-clean`, `imports`, `preview`, `lean-style`, `fanout`, `vendor`, `vendor-upstream`, `deps`, `renovate`, `meta`, `spec`, `cli`, `coverage`, `ledger-suite`, `python`, `secrets`, `vulns`, `workflows`, `tools/fetch-tools.sh`, `tools/ci-gate.sh` `ci_missing`, the compiler options + linters in either lakefile) reruns `tools/vflab-run bash tools/gate-probe.sh` (also the gate's `probes` stage): each check passes on a clean copy, fails on its planted input naming its cause, passes once restored. A new check lands with its probe.
- Probe copies share the gate tree's lean-fmt build through `FVDEP_LEAN_FMT` (a 339 MB package cache per copy otherwise); the gate's own `lean-style` builds + runs the pinned one.
- Stage `python` = pinned Ruff (correctness families E4, E9, E711–E722, F, B; `ruff.toml`) + Pyrefly (`pyrefly.toml`: preset `default` — without the file Pyrefly silently falls back to `basic`; unannotated bodies checked, warnings fail) over `tools/*.py` + `tests/**/*.py`; a suppression carries its reason on the line.
- Stage `vulns`: `tools/lockfiles.txt` lists every lockfile of the tree (`fixture <path>` = a test input never installed: listed, not scanned); osv-scanner needs network (osv.dev); vendored C has no lockfile ⇒ each `vendor/*/lock.json` commit is queried at OSV by commit (a failed query = red, never clean).
- An edit to `tools/vflab-run` or `tools/vflab-reclaim.sh` reruns `bash tools/vflab-run-probe.sh` from the desktop.
- An edit to `tools/vflab-provision.sh` or `tools/vflab-agent-smoke.sh` reruns both from the desktop (a host change ⇒ announce it to the fvapi session first): smoke rc 0, or 3 while the token is absent.
- An edit to `renovate.json` records `tools/vflab-run bash -c 'npx --yes --package renovate@<release ≥ 7 days old> renovate-config-validator --strict renovate.json'` → rc 0 in the commit body.
- `tools/pin-tool.sh NAME VERSION` re-pins a tool (asset name = the current one with the version replaced); a Renovate bump of the version column alone stays red on `renovate` + `tools` until re-pinned.
