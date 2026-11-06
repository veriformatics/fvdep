## Intent

Provably secure dependencies. This repo is a library and automated system for building a library, that contains an ever-growing list of formal verification spec for popular dependencies. We create implementations for some of them in various languages as an example, but the idea is that with a provably secure spec, anyone can use coding agents to implement them in any way they want. We provide a workflow to help ensure that what they implement matches the spec, and a system for them to follow updates to the spec (perhaps this can be commercialized). We can also commercialize dependencies by request and creating the implementations for users. This whole system itself should be formally verified as well.

## Artifacts

- `prototype/fvdep/` = whole-product prototype (`README.md` = human tour). Needs lean 4.35.0 + lake, uv, python3, cargo, node + pnpm.
  - Run: `prototype/fvdep/tour.sh` (every command on a temp copy of `demo/`, own state dir); single command: `prototype/fvdep/fvdep <cmd>`.
  - Smoke: `tour.sh` rc 0; 9 lines `^(PROVEN|MATCHED)`; exactly 2 `^MISMATCH` (CPython stdlib decode vs `base64.decode`; Python impl lacks `decode_url`); `MODEL MATCHES  npm:base64-js`; `Upgraded base64.decode to 1.1.0`; `--require-proof` names `semver.compare`. `fvdep list`: 6 modules, `semver.compare` 3/1, `semver.parse` 0/1, 3 profiles (cpython 1, crates 0, npm 5 deviations). `fvdep profile <pkg> --check` → `MODEL MATCHES` for all 3.
  - `library/` = Lean lake pkg: contract modules `Fvdep/<Dep>/<Op>/V<x_y_z>.lean` + catalog `catalog/<dep>.<op>/<ver>.toml` (fn, op, uses, obligations, compat); profiles `Fvdep/Profiles/<Pkg>/V<ver>.lean` + `profiles/<eco>/<pkg>/<ver>.toml` (ops → contract, relations, deviations + witness); oracle exe `Oracle.lean` (`lake build` → `.lake/build/bin/fvdep-oracle <module@ver | eco:pkg@ver>`).
  - `impls/` = example impls: lean `Base64Acc` (encode + decode, proven), python (`base64_strict.py`, `semver_impl.py`), rust (`base64`, 4 base64 modules) = development evidence.
  - `packages/` = real-package adapters for profiles: `cpython-base64.py`, `npm-base64-js/` (pnpm), `crates-base64/` (cargo, base64 0.22.1).
  - `cli/` = uv pkg `fvdep` (stdlib only), wrapper `prototype/fvdep/fvdep`; state `prototype/fvdep/.state/` (gitignored, `FVDEP_STATE` overrides).
  - `demo/` = consumer project (`fvdep.toml` per-module pins, `package.json`). Protocol = `PROTOCOL.md`.

## Decisions

- Guarantee (user ruling): proof only — an implementation counts as delivered only with a machine-checked proof against its spec. Differential checks vs the spec oracle = development evidence, never a delivery label. Foreign languages need a proof route (e.g. Verus/Aeneas for Rust) or a Lean implementation compiled/linked into them.
- Library entry (user ruling): both, mapped — a spec = the secure behaviour contract (e.g. strict RFC 4648 base64) + per-package profiles stating where each real package (npm `base64-js`, Python stdlib, …) deviates. A package without deviations matches the contract; deviations are named, never hidden.
- Spec modularity (user ruling): modular specs — each operation (e.g. `base64.encode`, `base64.decodeUrl`) = its own versioned spec module; consumers pin the modules they use; no shared per-dependency version line.
- Automation (user ruling): agent drafts, kernel admits — agents pick popular packages, draft spec + proofs from the standard + upstream tests; admission = Lean kernel build + axiom audit, fully proven entries alone; human spec review optional. Runs on vflab.
- Host (user ruling, fvapi commit 42c5b62): fvdep shares vflab with fvapi at equal priority — same `eturkes` account + `fvapi_gate.slice` for builds, checks + library growth; live services run outside the slice + outrank dev work; host maintenance announced to the fvapi session first. Conventions + paths = `CLAUDE.local.md`.
- Openness (user ruling): open core — popular specs public (repo licence Apache-2.0); paid = update feed/alerts, requested specs, built implementations.
- fva + fvtrace dependencies → fvdep (user: "eventually") → `.agent/deferred.md`.
- Prototype stack (speed pick, reopened at IMPLEMENT): specs + Lean impls = Lean 4.35.0 core (no Mathlib); CLI = Python/uv stdlib; example impls = Python + Rust + Lean.
- Conformance check (MAIN, at r1 showing): fvdep writes the statement `@impl = @spec_fn` (catalog `fn`) and the user names the proof; status from `#print axioms` of that generated theorem. Equality over the spec's own types (`List Nat`/`List Char`).
- Profile shape (MAIN, at r1 showing): profile = Lean model of one package version + per-op relation theorems to the contract (`agrees`; `complete` = exact characterization) + each deviation named with a kernel-checked witness; model ↔ real package = differential evidence (`profile --check`), never a proof. Missing completeness theorem = shown as "deviations beyond the list may exist".
- Module updates (MAIN, at r1 showing): a version's `compat` theorem (`new = old`) proven ⇒ "same behaviour; proofs carry over" — the Lean check retries the user's proof through it; no compat ⇒ minor = "not stated"; major ⇒ re-prove. Module dependencies (`uses`) = spec references, not implementation requirements.
- Lock (MAIN, at r1 showing): `lock` records each module's evidence (`proof` | `differential`) + `delivered`; `--require-proof` fails unless every module is delivered.
- Obligation status derived from `#print axioms` (std axioms only = proven, `sorryAx` = open, other = trusts X), never hand-written; spec completeness (open obligations) + implementation evidence stay separate labels.
- Self-verification of the fvdep system (Intent): open; prototype CLI = unverified Python.

## Tasks

- [x] b38c444 Standup: repo, `.gitignore`, spec skeleton
- [x] 9fdd332 Prototype build: Lean spec library + oracle, Python/Rust/Lean impls, CLI, tour
- [x] 9ebb36b Review + navigator-1 fixes: Lean check bound to spec module, `axioms-audited` label, scan/obligation wording
- [x] 31f2ab5 ITERATE r1: `tested` → development-evidence label; delivery = proof (Guarantee)
- [x] 31f2ab5 ITERATE r1: modular specs — split base64/semver into per-operation versioned modules; pins per module; `upgrade`/`diff` per module
- [x] 31f2ab5 ITERATE r1: per-package profiles — base64 contract + profiles (Python stdlib deviation: accepts non-zero unused bits; npm `base64-js`)
- [x] 31f2ab5 ITERATE r1: Lean conformance check = statement shape (impl = spec per operation), so a Lean impl earns `proven`
- [ ] ITERATE: foreign-language proof route (research: Verus, Aeneas, Lean-compiled libs) for one Rust impl
- [ ] ITERATE: automation sketch — agent draft → kernel admit loop for one new package; runs on vflab per `Host`
- [ ] ITERATE: self-verification plan for the fvdep system
- Deferred → `.agent/deferred.md`

## Phase

ITERATE — whole product
