## Intent

Provably secure dependencies. This repo is a library and automated system for building a library, that contains an ever-growing list of formal verification spec for popular dependencies. We create implementations for some of them in various languages as an example, but the idea is that with a provably secure spec, anyone can use coding agents to implement them in any way they want. We provide a workflow to help ensure that what they implement matches the spec, and a system for them to follow updates to the spec (perhaps this can be commercialized). We can also commercialize dependencies by request and creating the implementations for users. This whole system itself should be formally verified as well.

## Artifacts

- `prototype/fvdep/` = spec library (Lean 4) + example impls + `fvdep` CLI. Building.

## Decisions

- Prototype stack (speed pick, reopened at IMPLEMENT): specs + proven reference impls = Lean 4 core (no Mathlib); CLI = Python/uv; example impls = Python + Rust.

## Tasks

- [ ] Standup: repo, `.gitignore`, spec skeleton
- [ ] Lean spec library: base64 v1.0.0 + v1.1.0, semver v1.0.0; proven reference impls; oracle exe
- [ ] Example impls: Python + Rust, JSON-lines adapter
- [ ] `fvdep` CLI: list, show, check, lock, outdated, diff, request
- [ ] Smoke run + review + navigator pass
- Deferred → `.agent/deferred.md`

## Phase

PROTOTYPE — whole product
