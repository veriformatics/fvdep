# ITERATE — whole product (closed)

Opened 1f7d89d. Rounds: r1 (modular specs, profiles, proof-only delivery), r2 (Lean via C library, publish status, grow/admit on npm semver, self-verification proposal), r3 (trim past-illustration parts; business rules → IMPLEMENT orientation). Close review (5 lenses fixed before reading: artifacts run, rulings held, Decisions readable alone, stubs labeled, spec = shipped): 4 pass, 1 fixed 418ff71; navigator-4 + janitor-6 passes on b49e059.

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
- [x] b72d2cb ITERATE: self-verification plan for the fvdep system (`SELF-VERIFICATION.md`)
- [x] ea9d56e ITERATE r2: navigator-3 + janitor-5 fixes (tour installs Node binding, step exit codes, `--skip-package` REJECTS)
- [x] 418ff71 ITERATE r3: trim past-illustration parts (user ruling r3)
