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

- An edit to a check (gate registry + aggregation + step ledger, `tree-clean`, `imports`, `preview`, `lean-style`, `fanout`, `vendor`, `vendor-upstream`, `deps`, `renovate`, `meta`, `spec`, `cli`, `coverage`, `ledger-suite`, `codec-suite`, `manifest-suite`, `python`, `secrets`, `vulns`, `workflows`, `tools/fetch-tools.sh`, `tools/ci-gate.sh` `ci_missing`, the compiler options + linters in either lakefile) reruns `tools/vflab-run bash tools/gate-probe.sh` (also the gate's `probes` stage): each check passes on a clean copy, fails on its planted input naming its cause, passes once restored. A new check lands with its probe.
- Probe copies share the gate tree's lean-fmt build through `FVDEP_LEAN_FMT` (a 339 MB package cache per copy otherwise); the gate's own `lean-style` builds + runs the pinned one.
- Stage `python` = pinned Ruff (correctness families E4, E9, E711–E722, F, B; `ruff.toml`) + Pyrefly (`pyrefly.toml`: preset `default` — without the file Pyrefly silently falls back to `basic`; unannotated bodies checked, warnings fail) over `tools/*.py` + `tests/**/*.py`; a suppression carries its reason on the line.
- Stages `codec-suite` (`tests/codec/run.sh`: tester-3's J, H, D + S5 cases) + `manifest-suite` (`tests/manifest/run.sh`: tester-4's T6) = blind suites over shipped code (`suite` in `tools/gate.sh`): the fast gate reuses a green verdict while the input closure stays byte-identical (the suite's files + the shipped code its driver builds + Lake configs + toolchain pins; jq's lock line for codec), the full gate always runs them; a run narrowed to one case (`FVDEP_CODEC_CASE`, `FVDEP_MANIFEST_CASE`, `FVDEP_LEDGER_ONLY`) never writes the green mark. Expected values change only in their own unit, on evidence a case errs against the contract: codec's are pinned by `FROZEN-JH.tsv` + `FROZEN-JHD.tsv` (freeze guards inside `run.sh`; probes `codec-freeze-jh`, `codec-freeze-jhd`). jq = the pinned one, first on `PATH` for `codec-suite` alone (its output bytes are a printer oracle). Their Lean packages (`tests/codec`, `tests/manifest`) take `lean-style`'s layout rules, not lean-fmt (it runs on `.` + `tool`, the root `.lean-fmt.toml` excluding `tests/**`: lean-fmt elaborates each file, and the packages build inside their own stages). A suite probe sets `with_suites=1` (copies the test packages' builds).
- Stage `vulns`: `tools/lockfiles.txt` lists every lockfile of the tree (`fixture <path>` = a test input never installed: listed, not scanned); osv-scanner needs network (osv.dev); vendored C has no lockfile ⇒ each `vendor/*/lock.json` commit is queried at OSV by commit (a failed query = red, never clean).
- An edit to `tools/vflab-run` or `tools/vflab-reclaim.sh` reruns `bash tools/vflab-run-probe.sh` from the desktop.
- An edit to `tools/vflab-provision.sh` or `tools/vflab-agent-smoke.sh` reruns both from the desktop (a host change ⇒ announce it to the fvapi session first): smoke rc 0, or 3 while the token is absent.
- An edit to `renovate.json` records `tools/vflab-run bash -c 'npx --yes --package renovate@<release ≥ 7 days old> renovate-config-validator --strict renovate.json'` → rc 0 in the commit body.
- `tools/pin-tool.sh NAME VERSION` re-pins a tool (asset name = the current one with the version replaced; release tags tried: `v<v>`, `<v>`, `<name>-<v>`); a Renovate bump of the version column alone stays red on `renovate` + `tools` until re-pinned.
