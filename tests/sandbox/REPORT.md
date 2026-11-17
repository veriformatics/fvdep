# U5 blind suite — tester-6

| part | cases | pre-unit red | verdict |
|---|---:|---:|---|
| D2 — outcomes, bounded streams, frames, line rule, usage | 45 | 45 | credited red |
| D1/S/P — phases, roots, source oracle, artifacts, snapshots, reproducibility | 45 | 45 | credited red |
| D3/K — graph/cache work counts, corruption, single-flight, eviction | 25 | 25 | credited red |
| B/D4 — complete/incomplete bundles, rerun, retention | 4 | 4 | credited red |
| total | 119 | 119 | 0 pre-unit passes |

Source = U5 contract at `b2d79a3850d856244f5ac0236af071ec958e148a` (condensed brief copy; G excluded), interface §§1/2/4/6/7, U3 H1–H4, Decisions U5 rulings + Accepted risks, MAIN's confirmations cited under Rulings. U5 implementation unread. Every case owns a fresh temporary `FVDEP_CACHE`; repeated commands inside that case share it. No default cache use. All fvdep/Lean execution = vflab.

## Rulings

Sources = MAIN's messages `Rulings Q1-Q4 and the artifacts layout; update the suite` (Q1–Q4 + layout) + `Confirm the export manifest entry reading` (Q5). Assertions already matched the confirmations; no expected value changed for this close.

| id | binding reading | pinned by |
|---|---|---|
| Q1 | T1 resolves the first `bwrap` on PATH; environment trusted. `--version` ≥ `bubblewrap 0.8.0`; older ⇒ `infra tool_missing`. Version-qualified wrapper with no status ⇒ `outcome setup_failed: <first stderr line>`. | `R.setup-failed` (minimum version, two stderr lines, exit 1), `R.preflight.old-version`; fixture-backed junk/closed fd 4 ⇒ D2 `frame invalid` / D1 `infra io`. |
| Q2 | D2 `stdout <bytes>` / `stderr <bytes>` = total stream bytes; dropped = total − retained. | `R.pump.*`, `R.pump.concurrent`; exact counts against independently generated input bytes. |
| Q3 | Phase 1 reason = `implementation build failed (…)`; phase 2 = `proof build failed (…)`. | `phase_failed` across compile errors, graph/root refusals + bundles. |
| Q4 | Kept first + last fragments concatenate without a marker, then relay line by line under the line rule; the dropped count signals the cut. | `R.pump.*`, `R.pump.concurrent`; first/last bytes + exact escaped lines. |
| Q5 | Text export path = `exports/e1.ndjson` / `exports/e2.ndjson`; manifest entry phase = `exports`, path = `e1.ndjson` / `e2.ndjson`, relative to that directory. Artifact manifest paths likewise relative to `phase1` / `phase2`. | `P.honest`, `P.module-proof`, artifacts-checker controls. |

D1 retained layout = `<dir>/phase1/<path>`, `<dir>/phase2/<path>`, `<dir>/exports/e1.ndjson`, `<dir>/exports/e2.ndjson`, `<dir>/manifest.json`; nothing else. Manifest = canonical JSON `{"files":[{"path":<str>,"phase":"phase1"|"phase2"|"exports","sha256":<hex>,"size":<n>}…],"schema":1}`; keys sorted, files in printed order. Every printed tuple must match its exact retained file + manifest entry. Legacy + modern-module trials check regular files, bytes, exact directory contents + canonical metadata.

Proxy templates = `fixtures/bwrap/`; each case owns its copied/substituted wrapper + PATH. The real executable comes from the original PATH. Helper-death coverage remains separate.

## Files + replay

- `run.sh`: builds `tool/` targets `fvdep-dev` + `«fvdep-cli»`, then `python3 -I run.py`.
- `run.py`: D1–D4 black-box cases; independent H2 big-endian/UTF-8 frame + SHA-256 oracle. Seed `5006001` (`FVDEP_TEST_SEED` overrides; printed).
- `fixtures/honest/`: correct alias + equality proof; `fixtures/module-proof/`: modern-module public `True` witness, artifact-family trial alone; `fixtures/bwrap/`: setup-failure, old-version, junk-frame + closed-frame proxies.
- `COVERAGE.tsv`: exact registration table, 119 rows. Each row names the contract clause + observable.
- `RED.jsonl`: 239 records = 120 driver invocations (argv, relevant environment, exit, full stdout/stderr) + 119 case verdicts/replay commands. The extra invocation = the two-builder single-flight case. `<repo>`/`<tmp>`/`<home>` redact machine-local prefixes.
- `qualify.sh`: authoring-only external Lean qualification; disposable package builds, including B.incomplete's actual artifact footprint.

Whole suite: `tools/vflab-run bash tests/sandbox/run.sh`.
One case: `tools/vflab-run bash tests/sandbox/run.sh --exact <id>`.
Subset: `tools/vflab-run bash tests/sandbox/run.sh --case <substring>`; `FVDEP_SANDBOX_CASE` = the same filter.
Validator controls: `tools/vflab-run python3 -I tests/sandbox/run.py --audit`.

## Red run

Production bytes = `b2d79a3850d856244f5ac0236af071ec958e148a`; harness = checkpoint `9160917` + ruling-confirmation comments/docs. Diff outside `tests/sandbox/**` = empty; positive control = 17 tracked sandbox diff paths. Every pending write also lies inside that allowlist. Actual suite step inside `tools/vflab-run`:

```sh
bash tests/sandbox/run.sh --evidence tests/sandbox/.runs/red.jsonl
```

Direct replay from the worktree:

```sh
tools/vflab-run bash tests/sandbox/run.sh --evidence tests/sandbox/.runs/red.jsonl
```

Fresh full run after all confirmations: 119 FAIL, 0 PASS, suite/runner exit 119. Output:

```text
All checks passed!
 INFO 0 errors
AUDIT 119 cases, 119 coverage rows
ARTIFACT_AUDIT positive PASS; 8 planted deviations refused
SEED 5006001
SUMMARY 119 cases; 0 passed; 119 failed
RED_RUN_EXIT 119
```

Every driver invocation: exit 2, empty stdout, existing `fvdep-dev` usage on stderr. Its advertised commands = `sys run`, `json measure`, `oracle`, `index decode|history`; D1–D4 unavailable. All 119 cases reached the built driver; no fixture-construction exception supplies a credited red. Usage-only negatives + proxy-failure cases start with a supported positive call, so generic pre-unit usage cannot pass them. Per-case command + complete output = `RED.jsonl`; every covered id occurs in its command + verdict records. The original 114 cases also have full red evidence in checkpoint `6b6ff2d`.

Confirmed-rulings vflab unit: 13.715 s, `Memory peak: 181.2M` (`status=119/n/a`, expected pre-unit red). This is the enclosing-unit time, not isolated suite latency.

## Validator + fixture checks

| check | result |
|---|---|
| Pinned Ruff 0.17.4 over `tests/sandbox` | PASS; `All checks passed!` |
| Pinned Pyrefly 1.4.1 over `run.py` | PASS; `0 errors` |
| Pinned ShellCheck 0.11.0 over both shell drivers + all bwrap fixtures | PASS; exit 0 |
| Coverage table = registered cases | PASS, 119/119; planted extra row refused; restored table PASS |
| Exact artifacts checker | Positive input PASS; 8 planted deviations refused |
| Report seed validator | Initial 10 placeholder cells (6 matching lines); final cells = 0 |
| Red evidence structure | 119 covered ids = 119 FAIL ids = ids with a recorded driver call; 120/120 invocations exit 2 + usage; 119 distinct per-case caches |
| Ordinary Lean fixture | `QUALIFY honest PASS` |
| Modern-module witness fixture | `QUALIFY module-proof PASS` |
| Oversized bundle input view | `QUALIFY bundle-view 36136000 bytes > 33554432 PASS` |

Artifacts-checker controls are synthetic validator inputs, not product stubs or green contract cases. Plants = extra file, wrong phase directory, wrong digest, reversed manifest order, schema 2, missing metadata, trailing LF + a symlink to byte-identical content. Their positive manifest follows Q5's confirmed ruling.

Independent fixture command = `tools/vflab-run bash tests/sandbox/qualify.sh`; retained qualification from the byte-identical fixture/script inputs in `6b6ff2d`: exit 0, enclosing unit 13.852 s, `Memory peak: 581M`. The 20 × 900,000-character library constants produce 36,136,000 bytes of required `.olean`/`.ilean`/`.c` artifacts; B.incomplete therefore starts with an actually over-cap view, not an assumed source-size proxy.

Modern modules cannot import the launch library's legacy modules: external Lean diagnostic `cannot import non-\`module\` SandboxTrial.Impl from \`module\``. D1 roots are unqualified, so that trial uses a standalone public witness; it never claims to prove base64. Separate launch fn/ABI cases use the independent implementations + real equality proofs from `tests/library/conformance/`.

## Questions

None. Q1–Q5 + the artifacts layout are settled under Rulings.

## Coverage limits

- G isolation + runner internals = MAIN's suite, excluded by brief. No claimed coverage of host escapes, descriptor internals, toolchain tampering or native memory safety.
- Implemented U5 behavior = unconfirmed; inspected only the source contract/addendum + pre-unit driver behavior. P7 e1/artifact pairs + e2 qualification pairs cannot be measured until D1 exists; their cases record those pairs when run. Proxy cases likewise stop at their positive control on this revision; no claim that the missing implementation exercised the proxy.
- Cache entry storage-container prefixes stay open; artifact family, immutable manifest validation + byte counts remain pinned. D1's retained output layout is exact under Rulings.
- B2's bundle JSON is checked for schema 1 + size; operational rerun tests retained inputs. D4's incomplete refusal must name a generated view-artifact path; JSON member spellings for omissions stay open.
- Full gate + CI = not run on this intentionally red tester branch. No U5 implementation, production stub, contract, docs, rules or gate edited. No push.

tester-6-DONE-2
