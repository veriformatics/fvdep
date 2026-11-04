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

- Guarantee (user ruling): proof only — an implementation counts as delivered only with a machine-checked proof against its spec. Differential checks vs the spec oracle = development evidence, never a delivery label. Foreign languages need a proof route (e.g. Verus/Aeneas for Rust) or a Lean implementation compiled/linked into them.
- Library entry (user ruling): both, mapped — a spec = the secure behaviour contract (e.g. strict RFC 4648 base64) + per-package profiles stating where each real package (npm `base64-js`, Python stdlib, …) deviates. A package without deviations matches the contract; deviations are named, never hidden.
- Spec modularity (user ruling): modular specs — each operation (e.g. `base64.encode`, `base64.decodeUrl`) = its own versioned spec module; consumers pin the modules they use; no shared per-dependency version line.
- Automation (user ruling): agent drafts, kernel admits — agents pick popular packages, draft spec + proofs from the standard + upstream tests; admission = Lean kernel build + axiom audit, fully proven entries alone; human spec review optional. Runs on vflab.
- Host (user ruling, fvapi commit 42c5b62): fvdep shares vflab with fvapi at equal priority — same `eturkes` account + `fvapi_gate.slice` for builds, checks + library growth; live services run outside the slice + outrank dev work; host maintenance announced to the fvapi session first. Conventions + paths = `CLAUDE.local.md`.
- Openness (user ruling): open core — popular specs public (repo licence Apache-2.0); paid = update feed/alerts, requested specs, built implementations.
- fva + fvtrace dependencies → fvdep (user: "eventually") → `.agent/deferred.md`.
- Prototype stack (speed pick, reopened at IMPLEMENT): specs + Lean impls = Lean 4.35.0 core (no Mathlib); CLI = Python/uv stdlib; example impls = Python + Rust + Lean.
- Obligation status derived from `#print axioms` (std axioms only = proven, `sorryAx` = open, other = trusts X), never hand-written; spec completeness (open obligations) + implementation evidence stay separate labels.
- Self-verification of the fvdep system (Intent): open; prototype CLI = unverified Python.

## Tasks

- [x] b38c444 Standup: repo, `.gitignore`, spec skeleton
- [x] 9fdd332 Prototype build: Lean spec library + oracle, Python/Rust/Lean impls, CLI, tour
- [x] 9ebb36b Review + navigator-1 fixes: Lean check bound to spec module, `axioms-audited` label, scan/obligation wording
- [ ] ITERATE r1: `tested` → development-evidence label; delivery = proof (Guarantee)
- [ ] ITERATE r1: modular specs — split base64/semver into per-operation versioned modules; pins per module; `upgrade`/`diff` per module
- [ ] ITERATE r1: per-package profiles — base64 contract + profiles (Python stdlib deviation: accepts non-zero unused bits; npm `base64-js`)
- [ ] ITERATE r1: Lean conformance check = statement shape (impl = spec per operation), so a Lean impl earns `proven`
- [ ] ITERATE: foreign-language proof route (research: Verus, Aeneas, Lean-compiled libs) for one Rust impl
- [ ] ITERATE: automation sketch — agent draft → kernel admit loop for one new package; runs on vflab per `Host`
- [ ] ITERATE: self-verification plan for the fvdep system
- Deferred → `.agent/deferred.md`

## Phase

ITERATE — whole product
