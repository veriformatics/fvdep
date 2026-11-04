## Intent

Provably secure dependencies. This repo is a library and automated system for building a library, that contains an ever-growing list of formal verification spec for popular dependencies. We create implementations for some of them in various languages as an example, but the idea is that with a provably secure spec, anyone can use coding agents to implement them in any way they want. We provide a workflow to help ensure that what they implement matches the spec, and a system for them to follow updates to the spec (perhaps this can be commercialized). We can also commercialize dependencies by request and creating the implementations for users. This whole system itself should be formally verified as well.

## Artifacts

- `prototype/fvdep/` = whole-product prototype (`README.md` = human tour). Needs lean 4.35.0 + lake, uv, python3, cargo.
  - Run: `prototype/fvdep/tour.sh` (every command on a temp copy of `demo/`); single command: `prototype/fvdep/fvdep <cmd>`.
  - Smoke: `tour.sh` rc 0 with 4 `PASS` lines, 2 `FAIL` (stdlib base64 non-canonical decode; upgrade missing url ops), `Upgraded base64 to 1.1.0`; `fvdep list` shows base64 8 proven/0 open, semver 3/2.
  - `library/` = Lean lake pkg: specs `Fvdep/<Dep>/V<x_y_z>.lean`, catalog `catalog/<dep>/<ver>.toml` (ops + obligations), oracle exe `Oracle.lean` (`lake build` → `.lake/build/bin/fvdep-oracle`).
  - `impls/` = example impls: python (`base64_stdlib.py` fails on purpose, `base64_strict.py`, `semver_impl.py`), rust (`base64`, spec 1.1.0), lean (`Base64Acc`, refinement theorem `conforms`).
  - `cli/` = uv pkg `fvdep` (stdlib only), wrapper `prototype/fvdep/fvdep`; state `prototype/fvdep/.state/` (gitignored).
  - `demo/` = consumer project (`fvdep.toml`, `package.json`). Protocol = `PROTOCOL.md`.

## Decisions

- Prototype stack (speed pick, reopened at IMPLEMENT): specs + proven impls = Lean 4.35.0 core (no Mathlib); CLI = Python/uv stdlib; example impls = Python + Rust + Lean.
- Spec = executable Lean model + named obligations (theorems) per version; obligation status derived from `#print axioms` (std axioms only = proven, `sorryAx` = open, other = trusts X), never hand-written. (MAIN, unruled by user)
- Conformance tiers: `proven` = Lean impl + refinement theorem (axioms audited; statement-shape match = stub); `tested` = differential run vs the oracle compiled from the spec (seeded random + standard vectors, adapter protocol over stdin). (MAIN, unruled by user)
- Spec versions = semver: minor = additive + proven `std_unchanged` compatibility obligations; major = breaking. Consumer pins in `fvdep.toml`, evidence in `fvdep.lock` (spec sha256, trust, cases, seed); `upgrade` re-checks before moving the pin. (MAIN, unruled by user)
- Related projects: fvapi = verification API on host `vflab`, whose ruling has vflab serve fvapi alone; user suggests vflab for fvdep work → open question at showing. fva + fvtrace deps → `.agent/deferred.md`. Prototype runs locally only.
- Commercial surface = `fvdep request` stub (local log); self-verification of the fvdep system = open.

## Tasks

- [x] b38c444 Standup: repo, `.gitignore`, spec skeleton
- [ ] Lean spec library: base64 v1.0.0 + v1.1.0, semver v1.0.0; oracle exe; Lean refinement impl
- [ ] Example impls: Python + Rust, adapter protocol
- [ ] `fvdep` CLI: list, show, check, lock, outdated, diff, upgrade, scan, request; `tour.sh`
- [ ] Navigator pass + user showing
- [ ] Review (fixed lenses) + close → `Phase: ITERATE`
- Deferred → `.agent/deferred.md`

## Phase

PROTOTYPE — whole product
