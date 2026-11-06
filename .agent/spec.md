## Intent

Provably secure dependencies. This repo is a library and automated system for building a library, that contains an ever-growing list of formal verification spec for popular dependencies. We create implementations for some of them in various languages as an example, but the idea is that with a provably secure spec, anyone can use coding agents to implement them in any way they want. We provide a workflow to help ensure that what they implement matches the spec, and a system for them to follow updates to the spec (perhaps this can be commercialized). We can also commercialize dependencies by request and creating the implementations for users. This whole system itself should be formally verified as well.

## Artifacts

- `prototype/fvdep/` = whole-product prototype (`README.md` = human tour). Needs lean 4.35.0 + lake, uv, python3, cargo, node + pnpm.
  - Run: `prototype/fvdep/tour.sh` (every command on a temp copy of `demo/`, own state dir); single command: `prototype/fvdep/fvdep <cmd>`.
  - Smoke: `tour.sh` rc 0; 10 lines `^(PROVEN|MATCHED)` (incl. `Base64Ffi … shipped as a C library` for the Rust-bound decode + Node-bound encode); exactly 1 `^NOT PROVEN` (`impls/lean-forged`, comparator: kernel rejected); exactly 2 `^MISMATCH` (CPython stdlib decode vs `base64.decode`; Python impl lacks `decode_url`); `MODEL MATCHES  npm:base64-js`; `Upgraded base64.decode to 1.1.0`; `--require-proof` names `semver.compare`. `fvdep list`: 6 modules, `semver.compare` 3/1, `semver.parse` 0/1, 8 modules (`semver.parse` 1.1.0 + `semver.compare` 1.1.0 0 open), 4 profiles (cpython published 1, crates published 0, npm:base64-js preview 5, npm:semver published 6). `fvdep profile <pkg> --check` → `MODEL MATCHES` for all 3.
  - `library/` = Lean lake pkg: contract modules `Fvdep/<Dep>/<Op>/V<x_y_z>.lean` + catalog `catalog/<dep>.<op>/<ver>.toml` (fn, op, uses, obligations, compat); profiles `Fvdep/Profiles/<Pkg>/V<ver>.lean` + `profiles/<eco>/<pkg>/<ver>.toml` (ops → contract, relations, deviations + witness); oracle exe `Oracle.lean` (`lake build` → `.lake/build/bin/fvdep-oracle <module@ver | eco:pkg@ver>`).
  - `impls/` = example impls: lean `Base64Acc` (encode + decode, proven) + `Base64Ffi` (C exports, proven in `Fvdep.Abi` shape; `ffi/build.sh` → `.lake/build/ffi/libfvdep_base64.so`); bindings `rust/base64-ffi`, `python/base64_ffi.py`, `node/base64-ffi` (koffi); `lean-forged` (skipKernelTC forgery, rejected on purpose); python (`base64_strict.py`, `semver_impl.py`), rust (`base64`, 4 base64 modules) = development evidence.
  - `packages/` = real-package adapters for profiles: `cpython-base64.py`, `npm-base64-js/` (pnpm), `crates-base64/` (cargo, base64 0.22.1).
  - `cli/` = uv pkg `fvdep` (stdlib only), wrapper `prototype/fvdep/fvdep`; state `prototype/fvdep/.state/` (gitignored, `FVDEP_STATE` overrides).
  - `demo/` = consumer project (`fvdep.toml` per-module pins, `package.json`). Protocol = `PROTOCOL.md`.
  - Growth: `fvdep grow <eco:pkg> --version V` (staging copy + `cli/src/fvdep/grow-brief.md` → `FVDEP_AGENT`, default `claude -p --dangerously-skip-permissions`) → `fvdep admit <staging> [--apply]`; `fvdep admit . --base-rev HEAD` = working tree vs a revision; vflab: `tools/vflab-run sh -c '… cd prototype/fvdep && PYTHONPATH=cli/src python3 -m fvdep.cli admit . --base-rev HEAD'`. Records `growth/<eco>-<pkg>-<ver>/` (brief, agent report, admission).
  - `SELF-VERIFICATION.md` = plan for verifying fvdep itself (user review pending).
  - `tools/vflab-run` (repo root) = fvapi runner adapted: bare repo `~/gate/fvdep-repo.git`, workspace `~/gate/ws/fvdep-…`, `fvapi_gate.slice`.

## Decisions

- Guarantee (user ruling): proof only — an implementation counts as delivered only with a machine-checked proof against its spec. Differential checks vs the spec oracle = development evidence, never a delivery label.
- Foreign-language route (user ruling, r1): Lean via C library only — the proven Lean implementation, compiled to a C-ABI library, linked into Rust, Python, Node, …; no per-language proof tools (Aeneas, Verus). Trusted base beyond the kernel = Lean compiler + runtime + the binding glue, stated wherever delivery is claimed.
- Security bar (user ruling, r1): a spec for a popular dependency that passes formal verification = the bar; no per-family threat model or extra security property set is in scope.
- Library entry (user ruling): both, mapped — a spec = the secure behaviour contract (e.g. strict RFC 4648 base64) + per-package profiles stating where each real package (npm `base64-js`, Python stdlib, …) deviates. A package without deviations matches the contract; deviations are named, never hidden.
- Profile publishing (user ruling, r1): complete to publish — a profile is published only with every op's agreement + deviation-list completeness proven; otherwise it shows as `preview`.
- Spec modularity (user ruling): modular specs — each operation (e.g. `base64.encode`, `base64.decodeUrl`) = its own versioned spec module; consumers pin the modules they use; no shared per-dependency version line.
- Automation (user ruling): agent drafts, kernel admits — agents pick popular packages, draft spec + proofs from the standard + upstream tests; admission = Lean kernel build + axiom audit, fully proven entries alone; human spec review optional. Runs on vflab. First growth target (user ruling, r1): npm `semver` profile + closing the open semver obligations.
- Host (user ruling, fvapi commit 42c5b62): fvdep shares vflab with fvapi at equal priority — same `eturkes` account + `fvapi_gate.slice` for builds, checks + library growth; live services run outside the slice + outrank dev work; host maintenance announced to the fvapi session first. Conventions + paths = `CLAUDE.local.md`.
- Openness (user ruling): open core — popular specs public (repo licence Apache-2.0); paid = update feed/alerts, requested specs, built implementations.
- fva + fvtrace dependencies → fvdep (user: "eventually") → `.agent/deferred.md`.
- Prototype stack (speed pick, reopened at IMPLEMENT): specs + Lean impls = Lean 4.35.0 core (no Mathlib); CLI = Python/uv stdlib; example impls = Python + Rust + Lean.
- Conformance check (MAIN, at r1 showing): fvdep writes the statement `@impl = @spec_fn` (catalog `fn`) and the user names the proof; a local probe gives readable errors, `lake comparator` (Lean 4.35 core, bwrap sandbox) decides against a challenge exported from fvdep's own library (`--challenge-from-export`), std axioms only. Equality over the spec's own types (`List Nat`/`List Char`). Measured: a project-built challenge accepts a tampered vendored spec; the trusted export rejects it.
- Library audit (MAIN): `leanchecker` kernel replay of `Fvdep` before any `#print axioms` status — `debug.skipKernelTC` forgeries pass `#print axioms` with std axioms only (`impls/lean-forged`).
- Profile shape (MAIN, at r1 showing): profile = Lean model of one package version + per-op relation theorems to the contract (`agrees`; `complete` = exact characterization) + each deviation named with a kernel-checked witness; model ↔ real package = differential evidence (`profile --check`), never a proof. Missing completeness theorem = shown as "deviations beyond the list may exist".
- Module updates (MAIN, at r1 showing): a version's `compat` theorem (`new = old`) proven ⇒ "same behaviour; proofs carry over" — the Lean check retries the user's proof through it; no compat ⇒ minor = "not stated"; major ⇒ re-prove. Module dependencies (`uses`) = spec references, not implementation requirements.
- C-library delivery (MAIN, r2): fvdep states `@export = Fvdep.Abi.<encoder|decoder> @spec_fn` (catalog `abi`), comparator judges the proof; then `ffi/build.sh` + the binding's differential run vs the oracle (glue evidence; mismatch = MISMATCH, not delivered). Trusted beyond the kernel: Lean compiler + runtime, C shim, binding — printed with every such PROVEN.
- Admission reading (MAIN, r2): contract modules enter only fully proven; profiles enter kernel-checked + model ↔ package matched, status `published` iff all their theorems (completeness included) are proven, else `preview`.
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
- [x] de60fa0 ITERATE r2: profile publish status — `published` iff agreement + completeness proven per op, else `preview` (list, scan, profile)
- [x] de60fa0 ITERATE r2: Lean via C library — export proven Base64Acc through a C ABI + proven wrapper theorem; Rust, Python, Node bindings; `fvdep check` reports the Lean proof + trusted base for a binding; binding vs oracle = integration evidence
- [x] b72d2cb ITERATE r2: automation loop — `fvdep grow` (agent drafts) + `fvdep admit` (kernel gate: build, leanchecker, axioms, no sorry, profile fidelity) on npm `semver`; fix `semver.parse.parse_render` (false as stated: pre id alnum "1" renders `0.0.0-1`, parses as num 1) + close `compare_trans`; runs on vflab per `Host`
- [x] b72d2cb ITERATE: self-verification plan for the fvdep system (`SELF-VERIFICATION.md`; user review pending)
- Deferred → `.agent/deferred.md`

## Phase

ITERATE — whole product
