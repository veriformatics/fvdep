# fvdep acceptance tests

This suite checks the public fvdep contract through its binaries. It uses Python's standard library only. It does not import product implementation code.

## Run

From the repository root:

```sh
python3 -I tests/acceptance/run.py --list
FVDEP_BIN=tool/.lake/build/bin/fvdep python3 -I tests/acceptance/run.py --merged
FVDEP_BIN=tool/.lake/build/bin/fvdep python3 -I tests/acceptance/run.py --unit U1
FVDEP_BIN=tool/.lake/build/bin/fvdep python3 -I tests/acceptance/run.py -k oracle.base64
python3 -I tests/acceptance/run.py
```

`MANIFEST.tsv` gives each case a status. A `merged` case runs in the gate. An `unmerged` case waits for the unit that turns it green. `--merged` selects the merged cases alone; the gate stage `acceptance` runs `run.py --merged` against the built `fvdep`. A unit that merges a case changes its status to `merged` and records the case's red run in its commit. `--list` validates `MANIFEST.tsv` against the discovered cases. It does not run fvdep. `--unit U<n>` selects a planned implementation unit. `-k TEXT` selects case ids containing `TEXT`. An empty selection is a usage error. A run prints one PASS or FAIL line per case, the seed, and the five slowest cases. Its exit code is the failure count, capped at 255 because process exit codes use one byte. A failed run therefore cannot wrap to exit 0.

The complete suite needs the implemented library and tool. Unit labels identify the earliest unit that supplies the required public command. Schema, profile, sandbox, and judge assertions reached through `check` therefore belong to U8, even though their components land earlier. U2, U3, U5, and U6 have no separate public test entry point in the supplied contract. U14 and U15 add no new CLI behavior.

## Environment

| Variable | Default / use |
|---|---|
| `FVDEP_BIN` | `tool/.lake/build/bin/fvdep` in this repository |
| `FVDEP_GROW_BIN` | `tool/.lake/build/bin/fvdep-grow` in this repository |
| `FVDEP_LIBRARY_URL` | Optional git source. Each case clones it to a temporary local repository. Without it, each case copies this repository's tracked and untracked, unignored library files and commits the copy. |
| `FVDEP_CACHE` | The suite replaces it with a fresh temporary cache for every case. One case separately checks the XDG default in another temporary directory. |
| `FVDEP_GROWTH_STATE` | The suite replaces it with a fresh temporary state directory. |

Git, Lean 4.35.0, Lake, and bwrap must be available for the implemented product's checks. Real-package profile and C binding tests need their future unit contracts before this suite can pin their invocation details. Tests do not use the real growth account, subscription login, or vflab state.

A case removes its temporary files when it ends. Output-write checks use Linux `/dev/full`. The listener in the network-confinement case binds only to `127.0.0.1` and closes when the case ends.

## Contract and fixtures

Expected values come from `.agent/spec.md` Intent and Decisions, `docs/interface.md`, `docs/library.md`, and the K2 cases in `docs/contracts/U1-foundation.md`. The initial contract is commit `c9cab81`. The output-write cases also use the D1/D2 additions supplied in `LEAD-DIRECTIVES.txt`: output-write failure is an I/O failure, exit 2. A broken output pipe exits 2 without a stderr message. D4 refines the reserved first-component rule, infrastructure precedence within a module, and the ordered status reasons; its observable name and status boundaries are included.

`reference.py` implements independent RFC 4648 §§3.2–3.5, 4, and 5 encoders/strict decoders and SemVer 2.0.0 §§2, 9–11 parsing/precedence. It imports no base64 or semver implementation. The semver comparator also covers the invalid-but-typed identifiers allowed by the library's whole-type comparison contract.

Generators use fixed seed `0xf4de2026`. Functional oracle failures shrink byte strings, text, or version pairs. Shrinking is bounded to 64 rounds and 128 candidates per round. The failure prints the shrunk request, actual reply, reference value, seed, and round count. This is a smaller counterexample, not a claim of a globally minimal input. Finite generated samples are development evidence, not a proof over the domain.

`fixtures/consumers/` contains project templates. The harness substitutes the temporary library commit and policy. It turns `.lean.in` templates into `.lean` modules before invoking fvdep. The extension keeps intentionally invalid or malicious inputs out of the production Lean source set. Expected verdicts and reason codes live in `test_conformance.py`, beside their contract citations.

The consumer templates include honest function and ABI implementations, a renamed multi-module implementation, forged kernel terms, axiom/sorry/native-decide proofs, wrong statements, compiler attribute swaps, macro hijacks, implementation build hooks, proof write/network/link attempts, reserved module shadowing, and a tampered vendored spec. `fixtures/generate.py` regenerates them. It does not run their Lean code.

`library_fixtures.py` adds versioned specs, entry declarations, proof registries, compatibility proofs, and notices to a temporary library. It uses the public Registry declarations. It preserves the original operation identities and starts each fixture from a full local git repository. Its root-registration helper expects the documented `def modules` before `def profiles`.

`fixtures/scan/` holds synthetic lockfiles for pnpm, npm, Cargo, uv, and Lake. They are input data, not dependencies to install. Their deliberate dependency edges exercise direct/indirect classification. `fixtures/scan/generate.py` regenerates them. The supported reader subsets still need U12's contract.

`fixtures/adapter.py` supplies matching, mismatching, unsupported, malformed, crashing, missing-reply, and extra-reply adapters. `fixtures/agent_stub.py` supplies draft, refusal, hang, crash, login-failure, and escape-attempt modes for U13's future qualification harness. The stub never supplies an admission verdict.

## Check fixture syntax

```sh
python3 -I tests/acceptance/check_fixtures.py
```

This separate light check compiles seven proof fixtures against a committed signature-only stub. It does not run fvdep or use the real spec body. It also checks that the forged term fails the normal Lean kernel while its axiom list remains empty under `skipKernelTC`. A reported PASS for the normal-kernel control includes the expected nonzero Lean exit. All temporary compiler files are removed. `TMPDIR` can select their parent directory.

## Qualification limits

The initial red run sets `FVDEP_BIN=/nonexistent`. Every case must then fail before fixture work with `fvdep binary not found`. This proves the runner cannot silently pass without the product. It does not prove that a product-semantic test has failed on an implemented revision.

The source explicitly defers the typed profile registry, exact package operations, domains, deviations, adapters, and witnesses to U10. The C ABI contract does not yet name binary symbols, error representation, or memory ownership. The growth contract does not yet define config keys, ranking/pre-staged-input/record schemas, or clock controls. Those cases need the corresponding unit contracts; this suite does not invent them.

Kernel fault injection, persistence interruption at every boundary, theorem/call-path inventory checks, full history gates, live bindings, and real unattended growth remain the owning units' qualification work. A signature-stub check can validate a fixture's Lean syntax without validating the production spec or the product.

After a suite change, regenerate its inventory explicitly:

```sh
python3 -I tests/acceptance/generate_manifest.py
```

The normal runner never regenerates the inventory or changes expected values.
