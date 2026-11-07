# Growth record: npm semver 7.7.3

Drafting agent: `claude -p` with the brief in `brief.md`. Its final report follows, then the admission results.

## Agent report

The profile for `npm:semver@7.7.3` is finished: `./fvdep admit .` prints **ADMITTED** and `./fvdep list` shows it as **published** with 6 deviations. The base's newer CLI also admits it.

**One thing you should know first.** The base library at `~/Projects/fvdep/prototype/fvdep` changed while I was working. Another session (I think) added an ABI layer: `Fvdep/Abi.lean`, an `abi = …` line in the five base64 catalog TOMLs, and edits to `cli.py` that aren't committed yet. Because my staging copy was older, the first admit failed with "published versions unchanged". I fixed this by copying those five TOMLs and `Abi.lean` from the base into staging and adding `import Fvdep.Abi` to `Fvdep.lean`. No published file in staging now differs from the base. If the base changes again before you run `--apply`, the same check will fail again.

**Files added**
- `packages/npm-semver/` (`package.json`, `pnpm-lock.yaml` pinned to 7.7.3, `adapter.mjs`): `parse` calls `semver.valid(text)`, `compare` calls `semver.compare(a, b)`. A `null` result or a thrown error is `err`.
- `library/Fvdep/Semver/Parse/V1_1_0.lean` and `catalog/semver.parse/1.1.0.toml`
- `library/Fvdep/Semver/Compare/V1_1_0.lean` and `catalog/semver.compare/1.1.0.toml`
- `library/Fvdep/Profiles/NpmSemver/V7_7_3.lean`: a port of the `SemVer` constructor and `compare`.
- `library/profiles/npm/semver/7.7.3.toml`
- Lines added to `Oracle.lean` (two helpers and handlers for the two new modules and the profile) and three imports added to `Fvdep.lean`.

**Deviations found** (each has a witness proven by `decide`)

| Op | Deviation | Witness |
|---|---|---|
| parse | build metadata is dropped | `1.0.0+build` gives `1.0.0` |
| parse | one leading `v` is accepted | `v1.2.3` |
| parse | whitespace at either end is trimmed (JavaScript's full whitespace set) | `" 1.2.3 "` |
| parse | text longer than 256 UTF-16 units is rejected, even a valid version | `1.0.0-` + 251 `a` |
| parse | a major, minor or patch number above 2^53−1 is rejected | `9007199254740992.0.0` |
| compare | numeric pre-release identifiers of 2^53 and above are compared after rounding to JavaScript numbers; the first such tie makes the whole result "equal" | `1.0.0-9007199254740993` vs `…992` gives `eq` (contract: `gt`) |

The rounding one was a surprise. The package even says `1.0.0-9007199254740993.b` equals `…992.a`, because it stops at the first tie instead of comparing the remaining identifiers.

**Relations proven:**
- **parse:** `parse_exact` (the complete relation) states the model as an equation in terms of the contract. It has no separate `agrees` theorem because dropping build metadata breaks agreement; the build-metadata deviation says so.
- **compare:**
  - `compare_exact` (complete) says the model equals the contract except in that rounding-tie case. Its proof needed a proof that JavaScript's rounding to a double never reverses order.
  - `agrees` says the model equals the contract when every numeric pre-release identifier is below 2^53.

**Open obligations closed**
- `semver.compare@1.1.0`: unchanged from 1.0.0 (proved by `rfl`). `compare_trans` is now proven, plus one new obligation, `compare_eq`: two versions of equal precedence differ only in build metadata.
- `semver.parse@1.1.0`: unchanged from 1.0.0 (by `rfl`), but the obligation is corrected (below).

**Statement corrected.** `parse_render` in 1.0.0 is false. A version value can hold identifiers that no version text can produce, for example a word identifier `"1"`: it renders as `0.0.0-1`, which parses back as the number 1. `parse_render_counterexample` proves this. The corrected `parse_render_valid` only covers versions whose identifiers a real text could contain, and is proven.

**Checks run**
- `lake build` passes.
- No `sorry`, `native_decide`, `axiom`, `debug.skipKernelTC`, `implemented_by` or `extern` in my files. The gate's kernel replay and axiom audit pass.
- `--check` printed MODEL MATCHES on seed 1 with the default cases, then with `--cases 2000` on seeds 1 to 4 (4,021 cases each).
- I also ran 332 hand-made edge cases with 0 differences: Unicode whitespace, the 256-length limit, huge numbers, rounding ties, and characters outside the Basic Multilingual Plane.

**Limits**
- `\r`, U+2028 and U+2029 can't be sent through the line protocol, because Node splits lines on them. I checked them in Node directly: the package trims them, as the model does.
- I wrote the edge-case files to `/tmp/fvdep-semver-probe`, outside cwd, against the brief, and have deleted them.

## Admission (local, `fvdep grow`)

```
  PASS  published versions unchanged                     10 checked
  PASS  new entries                                      semver.compare@1.1.0, semver.parse@1.1.0, npm:semver@7.7.3
  PASS  lake build                                       ok
  PASS  kernel replay (leanchecker)                      ok
  PASS  semver.compare@1.1.0: every obligation proven    6 theorems
  PASS  semver.compare@1.1.0: oracle serves it           ok
  PASS  semver.parse@1.1.0: every obligation proven      3 theorems
  PASS  semver.parse@1.1.0: oracle serves it             ok
  PASS  npm:semver@7.7.3: kernel-checked profile         published (complete)
  PASS  npm:semver@7.7.3: oracle serves it               ok
  PASS  npm:semver@7.7.3: model matches the real package 1021 cases
ADMITTED  <staging>
```

## Admission (vflab, `fvapi_gate.slice`, retired prototype runner; Node 24, working tree vs HEAD)

```
  PASS  published versions unchanged                     10 checked
  PASS  new entries                                      semver.compare@1.1.0, semver.parse@1.1.0, npm:semver@7.7.3
  PASS  lake build                                       ok
  PASS  kernel replay (leanchecker)                      ok
  PASS  semver.compare@1.1.0: every obligation proven    6 theorems
  PASS  semver.compare@1.1.0: oracle serves it           ok
  PASS  semver.parse@1.1.0: every obligation proven      3 theorems
  PASS  semver.parse@1.1.0: oracle serves it             ok
  PASS  npm:semver@7.7.3: kernel-checked profile         published (complete)
  PASS  npm:semver@7.7.3: oracle serves it               ok
  PASS  npm:semver@7.7.3: model matches the real package 1021 cases
ADMITTED  <repo>/prototype/fvdep
```
