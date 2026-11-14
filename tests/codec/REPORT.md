# tester-3 — U3 J + H

| id | surface | verdict | evidence |
| --- | --- | --- | --- |
| R1 | clause coverage | PASS | COVERAGE.tsv: 27/27 rows filled; `unknown` = 0 |
| R2 | stub A | expected RED | 3,934 cases = 2,707 FAIL + 1,227 PASS; rc 1; API driver rc 0 |
| R3 | oracle independence | PASS | own J2/J3 parser + J4 printer + H2 encoder/decoder; production/fvapi source unread |
| R4 | oracle controls | PASS | strict Python: 586 valid texts + 8 malformed texts; jq 1.8.1: 214 valid values; fixed byte goldens |
| R5 | transport controls | PASS | 9 constructor/payload echoes; independent length-prefixed transport + own output hex |
| R6 | Python + shell checks | PASS | pinned Ruff 0.17.4, Pyrefly 1.4.1 (0 diagnostics), shellcheck; Driver lines ≤100 |
| R7 | Lean formatter | PASS | 2 files all formatted + no findings; same-line/100-column policy mirrors tool/.lean-fmt.toml |
| R8 | J5 domain question | resolved | MAIN Ruling 1: constructor/accessor laws total; printer/round-trip laws restricted to Valid |
| R9 | credit remaining | explicit | 2,707 cases red on A; GREEN.stubA.txt names all 1,227 cases awaiting B or a shipped-code mutant |
| R10 | real-code runtime | unconfirmed | only the fixed-answer stub ran; ≤5-minute warm limit must be checked on MAIN's code |

## R2 + R9: run + per-case evidence

Source under test = stub A, `5729bf89ff0a55cd4cc75863960fd3bc1dd71493` (implementation files unchanged in this worktree). Driver checkpoint = `390c4d0`. Branch = `wt/tester-3`.

```sh
tools/vflab-run bash tests/codec/run.sh > /tmp/fvdep-tester-3-final-replay.log 2>&1
rc=$? # 1: expected planted red
python3 -I tests/codec/record.py /tmp/fvdep-tester-3-final-replay.log
```

Exact summary:

```text
SEED 4158533633 (FVDEP_TEST_SEED overrides)
CONTROL strict-python corpus=586 negatives=8 PASS
CONTROL jq-1.8.1 canonical-values=214 PASS
CONTROL independent-goldens PASS
CONTROL independent-transport values=9 PASS
SUMMARY seed=4158533633 cases=3934 api=3470 relations=464 pass=1227 fail=2707 driver_rc=0 driver_seconds=0.063
vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=1/FAILURE; Service runtime: 10.907s; CPU time consumed: 7.109s; Memory peak: 210.5M (swap: 0B)
```

`RESULTS.stubA.tsv` = 3,934 rows, each with the actual batch command + that test's exact PASS/FAIL output line. Long mismatch output carries prefix + length + SHA-256; the seed regenerates the complete input/expected bytes. `GREEN.stubA.txt` = every green id, 1,227 lines. No case is credited merely because a fixed stub passes it. MAIN owns stub B + any required mutants; `record.py LOG --column stubB` adds B's table column + per-case files.

`COVERAGE.tsv` case notation: `[000..127]` = inclusive numeric range, padding preserved; `[0..2,31..34]` = a union; multiple brackets = Cartesian product; `;` = union. Clause counts overlap because one API case can test several clauses. The 464 relational cases require their operands to meet the independent oracle as well as the relation; constant error/empty outputs cannot pass an equality property accidentally.

Replay one case or a group: `tools/vflab-run env FVDEP_CODEC_CASE=J.int.valid.6 bash tests/codec/run.sh`; the filter accepts shell-style globs and includes a selected relation's operands. Default = every case. `FVDEP_TEST_SEED` accepts decimal or Python-style base prefixes. Positive control: `tools/vflab-run env FVDEP_TEST_SEED=42 FVDEP_CODEC_CASE=J.limits bash tests/codec/run.sh` → rc 0; `SEED 42`; `PASS J.limits`; summary 1 API case, 1 pass, 0 fail; oracle + transport controls pass; service 2.964 s. Filtering keeps the full oracle cross-check corpus but runs only selected API cases/relations.

After formatting, the full replay's 3,934 PASS/FAIL lines equal the pre-format run byte-for-byte (`cmp -s` → rc 0). This is a second fixed-seed replay, not a new red class.

## R3–R5: oracle design

- J decoder: independent byte recursive descent. Stage 1 scans lexical depth with only quote/escape state; exceeding 32 wins even on malformed text. Stage 2 parses J2 completely, retaining object text order + duplicate keys. Stage 3 checks decoded UTF-8 string/key byte lengths. Stage 4 selects the first duplicate-bearing raw object in pre-order, then its least repeated UTF-8 key. Stage 5 canonicalizes every object's member order. Every successful reference outcome satisfies an independently stated J1 `valid` predicate.
- J printer: own recursive J4 layout + exact escape table; raw UTF-8 for all other scalars. Python's `json` module supplies corpus agreement only, never expected values. jq supplies a second byte oracle for each of 214 valid printer values. Its final LF is removed; stream parsing is not confused with the single-text grammar.
- H: own u64be encoder + cursor decoder. Decoder uses unbounded Python offsets, checks each length against remaining input, checks UTF-8 + strict path order, and requires exact consumption. `argv_bytes` + `adapter_entries` follow H3 independently; fixed encoder/argv byte goldens prevent a mutually consistent reference round-trip bug.
- Driver: imports only the public JSON/framing modules. A private netstring-like value format constructs/observes values independently of JSON. Raw decoder/unframe inputs come from files. The driver's own hex formatter formats observations; the tested `Hash.hex` never formats its own expected/observed output. Loading the Python reference under `-I` uses its exact source path, not an ambient import path.

RFC 8259 source (full text read): https://www.rfc-editor.org/rfc/rfc8259.txt. Binding excerpts: `JSON-text = ws value ws`; `ws = *( %x20 / %x09 / %x0A / %x0D )`; `The literal names MUST be lowercase.`; `The names within an object SHOULD be unique.`; `JSON text ... MUST be encoded using UTF-8`; `An implementation may set limits on the maximum depth of nesting.` J2 explicitly narrows RFC numbers, surrogate escapes + BOM handling; the RFC's broader permissiveness never overrides the contract.

## R1: generator domains

Fixed seed = `0xF7DE3001` = 4,158,533,633. PRNG = Python `random.Random`; vflab Python 3.14. All generated sets are sorted before order-sensitive shuffles; regeneration does not depend on hash randomization.

- Values: every constructor; integers sampled over the full allowed range + boundary values; strings mix the whole Unicode scalar domain (surrogates excluded) with weighted control/escape/Unicode edges. Generated nesting + containers, unique byte-sorted object keys. Printer/round-trip inputs always J1-valid. J5 total laws additionally get over-range integers, 65,537-byte strings, depth 33 + unsorted/repeated objects.
- Text: 128 generated values and alternative legal spellings; 256 insertion/deletion/substitution/truncation/suffix mutations; 128 arbitrary byte strings; generated integer/UTF-8/depth/site/bound-priority families. Grammar examples pin every named J3 consequence + both site examples. UTF-8 width/scalar edges, every raw control + canonical control escape, every short escape, surrogate pair endpoints + lone halves, BOM/trailing bytes, exact integer caps, string/key sizes 65,535/65,536/65,537 with 1/2/4-byte scalars, escaped decoded-length bounds, generated interior lengths, depth 32/33, million-open/million-closed nesting, quoted million opens + a million digits.
- H: all 256 byte values + generated blobs; empty/multibyte/NUL tags + paths; path spellings retained; 96 distinct-path file sets with order permutations and distinct tag/content/count variants. Decoder input mutations include arbitrary bytes, every byte truncation of a multibyte fixture, trailing bytes, order/repeat failures, invalid UTF-8 + u64 maximum lengths/counts. Accepted mutations get an independent exact re-encoding case. Pure argv/adapter laws include empty/NUL/repeated arguments, repeated named paths with different contents + the reserved empty entry.

## R8: contract questions + rulings

Q1: brief point 4's value-domain restriction conflicted with J5's unqualified laws. MAIN Ruling 1: `Value.object`, `get?` + `as*?` are total laws over all inputs, including unsorted/repeated outer members/children + raw duplicate objects; point 4 restricts J4/J6 printer/round-trip laws + later D decoding. Cases retained unchanged; total accessor boundary cases added.

No unresolved question. Length/count ≥2^64 is not realizable in the generated in-memory buffers; malformed encoded u64 maxima are tested. Claims of asymptotic sorting/fuel/tail recursion + measured real-code resource curves remain MAIN's proof/resource work, not an inference from this stub run.

## R6–R7: validator evidence + harness corrections

- Seed: `command grep -c unknown tests/codec/COVERAGE.tsv` → 27, rc 0 (expected 27). Final → 0, rc 1 (expected 0). TSV row count = 27; per-case rows = 3,934; green ids = 1,227.
- `cmp -s tool/lean-toolchain tests/codec/lean-toolchain` → rc 0.
- Initial driver build: `tools/vflab-run bash -c 'cd tests/codec && lake build codec-driver'` → rc 0, 15 jobs, 3.235 s, peak 269.9M. Final suite also builds + drives the package boundary; launch alone is not counted.
- Pinned checks on vflab: `.tools/bin/ruff check --config ruff.toml --output-format concise tests/codec`; `.tools/bin/pyrefly check --config pyrefly.toml --output-format=min-text --min-severity=warn tests/codec`; `shellcheck tests/codec/run.sh`; Driver line-length `awk` check. Final combined checks additionally run the pinned formatter from the test-package directory (`format --check` + `check`): rc 0; Ruff `All checks passed!`; Pyrefly `0 diagnostics`; formatter `2 files, all formatted.` + `2 files, no findings.`; remote service 9.896 s, peak 354.4M. One preliminary shellcheck ran on the desktop (no fvdep execution); the final check reran on vflab.
- Harness red: jq accepts `true false` as a two-value stream. The negative corpus control first mistook rc 0 for one-text acceptance; corrected to count emitted LF-terminated values. The run stopped before API checks. Expectations stayed unchanged.
- Harness reds: Ruff found 2 implicit `zip` strictnesses + an unused loop name; explicit strictness + `_` fixed them. Pyrefly found CSV header `Sequence.append` + an unresolved dynamic script-directory import; list conversion + exact-path reference loading fixed them. These are harness findings, not product defects.
- Formatter reds: initial Driver/lakefile drift + FMT005 import order; formatter applied, imports sorted. `tests/codec/.lean-fmt.toml` mirrors the tool's same-line/100-column policy; the formatter's default layout alone does not inherit the parent package policy. Two exported files matched the remote SHA-256 values after import; final format/lint checks pass.
- LSP `documentSymbol` on Driver → no `.lean` server; vflab compiler diagnostics used.
- Positive-control search: one written `driver-error:positive-control` line matched once (rc 0). Completed API run had no `driver-error`/`Traceback` matches (rc 1).

## R9–R10: limits + handoff

- Stub B + real implementation + surviving-case mutants: not run here; MAIN owns them. No implementation-correctness, proof-faithfulness or real-code performance claim follows from red on a fixed-answer stub.
- D/S/T/F, SHA-256, persistence, coverage-guided fuzz campaigns, full gate + J5 resource measurements: outside this batch; full gate deliberately not run per brief.
- Writes confined to `tests/codec/**` + temporary `/tmp/fvdep-tester-3-*`; no primary implementation, other project refs, fvapi files or host/service/account configuration changed. Package configs are explicit test files. Useful RFC browser tab retained.
- Cleanup control: one test-owned dangling link found once, then removed; final link count 0, rc 0. Run temp directories self-remove; authoring logs removed after the durable per-case evidence was recorded.
- Finish: blind J + H suite, reference oracles, complete clause table + stub-A red evidence delivered; final checkpoint on `wt/tester-3`. No work running.

tester-DONE-3

## Batch 2

| id | verdict | evidence |
| --- | --- | --- |
| B2-1 source + merge | PASS | one prescribed merge: 9df6dc5 → merge 1ce31c4; Doc bodies unread; signatures + permitted U2 input types only |
| B2-2 J/H freeze | PASS | FROZEN-JH.tsv = 3,934 case/relation records; id, op, input + expected SHA-256; default run checks equality |
| B2-3 D oracle | PASS at first run | independent D1–D8 layouts, typed domains, schema walk + renderer; 4 literal layout controls + 4 typed transport controls |
| B2-4 stub C | expected RED | final D 3,371 = 2,918F/453P; total 7,305 = 4,024F/3,281P; driver rc 0; suite rc 1 |
| B2-5 D coverage | filled; corrected validator | 26 rows filled; target cells equal to `unknown` = 0; ruling 7 replaces the false-positive grep |
| B2-6 checks | PASS | driver builds; pinned Ruff/Pyrefly (0 diagnostics), shellcheck, lean-fmt format/lint, frozen-inventory planted probe + seed-42 D control pass |
| B2-7 contract questions | resolved | rulings 2–7 adopted; no unresolved source ambiguity |

### B2-1 + B2-2: source + freeze

B2-1 command: `git merge --no-edit 9df6dc51279413037628882aa6ffcf029d220ded` → rc 0, merge `1ce31c4f3a999f03cd9cbfbda8556c2dc86adcd1`. This is the only merge. Inputs read: merged U3 D1–D8, interface §6/§7, U2 contract, U2 Ids/Evidence/Status input types, repo rules. `tool/FvdepCore/Doc.lean`: declarations/fields only; bodies omitted. Real J + H implementation/proof sources remain unread.

`python3 -I tests/codec/freeze_jh.py --emit` on vflab captured 3,934 records before D generation was added. `freeze_jh.py` regenerates the original builder sequence with its fixed seed and compares every id/op/payload hash/expected hash, plus relation targets/predicate bytecode. Every run begins `CONTROL frozen-JH cases=3934 PASS`. D uses its own PRNG (`seed ^ 0xD0C50002`) after every J/H builder finishes. Batch-1 oracle + coverage + stub-A outputs remain unchanged.

### B2-3 + B2-4: oracle + first red

`doc_oracle.py`: independent D layouts + schema tree; discriminator → extras → absent members → member walk → array order. General kinds precede field predicates; a rejected nullable field never descends. Value-level Receipt.ofJson/Lock.ofJson inputs are J1-valid; 65,537-byte id/version/argv cases use typed wellFormed checks or byte-level decodeLock (J3 tooLarge), never an invalid ofJson input. Typed observations serialize every field directly, not through tested toJson; typed inputs do not call tested ofJson. Diagnostic clipping differs from identifier refusal.

`doc_cases.py`: seeded valid/invalid documents, field × JSON-kind matrix, every member deletion + extra keys, boundary/date/identifier/argv rules, error precedence + RFC6901 paths/render bytes, normalization, envelope result/diagnostic rules, U2 argv regressions. Literal proof/differential/empty-lock/envelope layout goldens are separate from the reference encoder. Controls are not credited product cases.

Command: `tools/vflab-run bash tests/codec/run.sh` → rc 1 (planted stub red), seed 4158533633. The first complete run had 3,130 D cases (2,683F/447P); its API driver completed with rc 0. Domain/coverage-strengthening added the final cases below; all were rerun on stub C.

Final run: **7,305 cases = 3,934 frozen J/H + 3,371 D**. D = **2,918 FAIL + 453 PASS**; whole suite = 4,024 FAIL + 3,281 PASS; driver rc 0. All 2,637 J cases passed on the merged real J; H = 191P/1,106F on its unchanged stub. Final summary:

```text
SUMMARY seed=4158533633 cases=7305 api=6841 relations=464 pass=3281 fail=4024 driver_rc=0 driver_seconds=3.547
vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=1/FAILURE; Service runtime: 36.004s; CPU time consumed: 20.431s; Memory peak: 227.5M (swap: 0B)
```

`RESULTS.stubC.tsv` records all 7,305 cases' actual batch command/output, including every D case. Long mismatches retain a prefix, length + SHA-256; the seed regenerates the complete payload. `GREEN.stubC.txt` records 3,281 green ids; `GREEN.D.stubC.txt` isolates the 453 D ids requiring complementary-stub or mutant credit. Clause counts overlap. `record_d.py LOG --column stubD` adds MAIN's complementary run without changing batch-1 evidence. Real D/stub D/mutants were not run here.

### B2-5 + B2-7: questions + rulings

- Ruling 2: receipt constructor kind must equal Decl.kind for WellFormed; layout evidence = constructor kind. Both mismatched typed cases added.
- Ruling 3: root/receipt library pins need not agree for Lock WellFormed. Named + generated mixed-pin positive locks added.
- Ruling 4: proof request.adapter=[1] fails bad_value at the field before element judging. Named precedence case added.
- Ruling 5: raw detail/fetch_error/trusted strings may exceed the cap; toJson clips each. Oversized raw diagnostics remain WellFormed.
- Ruling 6: EnvelopeEncodeExact is total; `.obj e.result` is preserved unchanged, even when unsorted/repeated/over-cap. No sorting, clipping, dedup or normalization; wellFormed rejects invalid result. Invalid-result layout cases retained.
- Ruling 7 corrects B2-5's validator defect: seed `grep -c unknown COVERAGE-D.tsv` → 26, rc 0. Filled table → 4, rc 0, because `D5-unknown-missing`, `unknown_field` + case ids are legitimate vocabulary. Replacement: `awk -F '\t' 'NR>1 && ($3=="unknown" || $4=="unknown" || $5=="unknown" || $6=="unknown") {n++} END {print n+0}' tests/codec/COVERAGE-D.tsv`. On vflab: seed a8863a5 → 26; filled table → 0. No tested id or expected value renamed to satisfy grep.

### B2-6: harness corrections + open work

- Build-only harness reds: Option.toExcept is absent; explicit match substituted. One multiline structure field was left of its first field; fields aligned. Corrected driver builds.
- Generation-only harness red: a supposedly valid generated differential argv contained NUL; positive argv generator now removes NUL (later empty arguments remain valid). Negative NUL cases remain explicit.
- Ruff B020: loop name overrode an iterable binding; renamed. Pyrefly rejected a dynamic replacement-key dict; explicit impl/proof branches substituted. Final pinned Ruff 0.17.4 + Pyrefly 1.4.1 → `All checks passed!`, `0 diagnostics`; shellcheck covers run.sh + probe-freeze.sh; all run on vflab.
- Formatter: Driver reformatted under the existing same-line/100-column policy; the imported bytes matched remote SHA-256. Final `format --check` + `check` → `2 files, all formatted.` + `2 files, no findings.` Combined checks rc 0; service 16.476 s, peak 532.9M. No grading expectation changed for a format/type correction.
- Freeze probe: `tools/vflab-run bash tests/codec/probe-freeze.sh` plants one changed expectation hash in a temporary inventory copy; the guard exits 1 naming `B2-2 breach`; the committed inventory exits 0. Output: `PASS freeze-jh rejects-planted-hash`, `CONTROL frozen-JH cases=3934 PASS`, `PASS freeze-jh committed-inventory`. Actual J/H cases remain unchanged.
- Seed/filter control: `tools/vflab-run env FVDEP_TEST_SEED=42 FVDEP_CODEC_CASE=D.decl.changes.000.same bash tests/codec/run.sh` → rc 0, one API case PASS, driver rc 0; J/H freeze + both batches' oracle/transport controls pass. D control service 20.168 s; sampling = one API case on seed 42, the full suite on the fixed gate seed.
- Scope limits: no real D, complementary stub D, surviving-case mutants, full gate or fuzz campaign ran here. API data/lint/probe/format runs all use vflab; local Python only records emitted evidence into the tables. No production implementation, config or instruction file was authored; only the prescribed merge imported MAIN's files.
- Finish: 26 D rows filled, corrected placeholder validator 0; every D case has a stub-C result; checks pass; committed on wt/tester-3. Authoring temporary artifacts removed; no work running.

tester-DONE-3.2

## Batch 3

| id | verdict | evidence |
| --- | --- | --- |
| B3-1 merge | PASS | single prescribed stub-F merge cc4b226 → 26ba6c8 |
| B3-2 frozen prior cases | PASS at capture | FROZEN-JHD.tsv = all 7,305 J/H/D case/relation fingerprints; old oracle/cases retained |
| B3-3 NIST provenance | PASS | 3 authorized rsp blobs match official NIST archive byte-for-byte; SHA256SUMS narrowed to those 3 per ruling 2 |
| B3-4 SHA suite | expected RED | final 1,212 cases = 1,150 FAIL + 62 PASS on F; independent controls pass; every case recorded |
| B3-5 limits | approved + exercised | ruling 1: min + public squeeze composition + small ceilings + raw refusal; all 61 limit cases pass F; no actual ≥2^64-byte stream claim |
| B3-6 checks + red credit | PASS / explicit remainder | pinned Ruff/Pyrefly/shellcheck + format pass; freeze probe rejects/restores; 62 F-green cases need E or mutant credit |
| B3-7 blindness | disclosed exception | an unsolicited primary-file reminder showed update/saturate/finish; ruling 2 permits continuation; no expectation derives from it |

### B3-1–B3-3: sources + data

Only merge: `git merge --no-edit cc4b226500fea8657aa9c3908a83f6cb63380f0b` → rc 0, 26ba6c8444844aeec1ee98edb8de2e58393fe66b. Read S1–S5/H3, public SHA declarations/doc comments + c/fvdep_sha256_core.h, build composition. C core/glue/HACL bodies remain unread; no real D/J bodies read. Prior 7,305 cases regenerate from their unchanged builders; S uses a separate PRNG.

NIST source: https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing labels the archive `SHA Test Vectors for Hashing Byte-Oriented Messages` and links https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip. BrowserOS + verbatim page text checked; ZIP read as data in its own empty download directory. All 3 rsp files from fvapi 02d99d1 match the official ZIP bytes:

- SHA256ShortMsg.rsp: 10,299 bytes, SHA-256 75e1cb83994638481808e225b9eb0c1ebd0c232d952ac42b61abce6363be283c.
- SHA256LongMsg.rsp: 426,209 bytes, SHA-256 6fac36f37360bcf74ffcf4465c18e30d6d5a04cc90885b901fc3130c16060974.
- SHA256Monte.rsp: 8,751 bytes, SHA-256 29ea30c6bb4b84e425fb8c1d731c6bb852dac935825f2bd1143e5d3c4f10bfb9.

Full copied SHA256SUMS first failed because it also listed SHA256Monte.txt, outside the 4 authorized blobs. No other fvapi file was read. Ruling 2: remove that unused entry, preserve all 3 rsp pins; plain sha256sum -c then checks exactly the vendored corpus.

### B3-4–B3-7: design + checkpoint

- Hash oracle = hashlib, cross-checked against every published NIST response and sha256sum over every generated/boundary blob. Monte Carlo = each published seed/checkpoint pair independently driven for 1,000 calls (100,000 total); previous published MD seeds the next case, never a tested result. Framed digest oracle = the independent H2 encoder + literal tags + hashlib.
- Test-owned C harness uses only c/fvdep_sha256_core.h; gcc ASan+UBSan builds default + small ceilings 127/64/513. Small Lean driver routes the 4 raw C symbols through ld --wrap to the same core compiled with those ceilings; no tool/c/vendor edit. Separate executable roots share CodecHarness so all prior dispatcher behavior remains intact.
- Limits: isolated processes print SHA_LIMIT_READY before the tested call; a surviving call prints DIGEST. Expected abort = nonzero + ready marker + no digest. ≥2^64 limits are tested compositionally (independent saturate oracle -> public squeeze), not by allocating an infeasible stream. Raw C refusal must keep the output sentinel untouched.
- Involuntary source disclosure: a system reminder injected primary SHA update/saturate/finish bodies after the test design + driver were written. I did not fetch that primary file or derive any expected value from the excerpt. MAIN ruling 2: no successor; those bodies are unchanged in stub F, the expected values remain independent. Total SHA-body unreadness is not claimed.
- Harness reds: Lake rejects 2 executable targets with one root module; split Driver/SmallDriver wrappers over CodecHarness. Shared helper import needs an explicit lean_lib target; added. Relative archive link paths were resolved outside the package; use an absolute __dir__-derived path and build ignored native outputs in the same remote command. Native C harness builds; full S execution pending. C build cache keys source/header/compiler closure + verifies the 3 output byte digests; sanitized HACL compiles once for both ceilings.
- More harness reds: nested IO action in an if argument needed a separate monadic binding; fixed. First S execution completed both Lean batches + independent NIST/hashlib/sha256sum controls, then failed before native cases because the executable category c-normal was used as a filename (built name core-normal); corrected the mapping. No S case credit claimed for that interrupted run. Ruff/Pyrefly pass; shellcheck's sanitizer-flag comma warning fixed by quoting that one argument.
- Raw CAVP rsp files keep their upstream CRLF/whitespace bytes. Git's text whitespace check first flagged that pinned data (bulk output truncated); nist/.gitattributes marks only rsp files binary/-text. Corpus hashes remain unchanged; owned source whitespace is still checked.
### B3-4 + B3-6: final evidence

`tools/vflab-run bash tests/codec/run.sh` → rc 1 (expected planted red). Fixed seed 4158533633; S's PRNG = seed XOR 0x5A256003. **1,212 S/H3 cases = 1,150 FAIL + 62 PASS**. Both normal/small Lean batch drivers exited 0; every native/abort case completed. The earlier 7,305 cases also ran, all fingerprints unchanged: 6,015P/1,290F (J+D real; H stub B). Exact final summaries:

```text
SUMMARY seed=4158533633 cases=7305 api=6841 relations=464 pass=6015 fail=1290 driver_rc=0 driver_seconds=2.229
SUMMARY_S seed=4158533633 cases=1212 pass=62 fail=1150
vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=1/FAILURE; Service runtime: 1min 4.412s; CPU time consumed: 1min 3.118s; Memory peak: 451M (swap: 0B)
```

- Independent controls: all 65 short + 64 long vectors match hashlib; all 100 Monte checkpoints (100,000 rounds) match hashlib; sha256sum agrees on 78 boundary/generated blobs. The million-a digest is pinned literally. Cases include every named padding/block/page/1MiB edge; explicit one-byte chunks of all 256 byte values; empty chunks; 40 persistent-state forks/reuses; 40 groups of 6 Tasks (physically shared first 2 inputs + distinct others); first-empty and erroring readers; 1MiB file boundaries; 40 min checks; small ceilings + isolated limits; 85 framed digests (all 5 tags, including reserved empty-path adapter argv frames).
- C harness: 411 individual default/small ASan+UBSan invocations, including vectors + 100 Monte steps, block streams, generated/boundary messages + refusals; zero sanitizer/leak diagnostics. Positive-control search matched one written AddressSanitizer marker; run search found 0 (rc 1). Raw-refusal output sentinels stay untouched; malformed digest results remain FAIL even with no memory diagnostic. This is finite corpus evidence, not a memory-safety proof.
- `RESULTS.S.stubF.tsv`: actual batch command + output for all 1,212 cases; long mismatches include prefix, length + SHA-256. `GREEN.S.stubF.txt`: all 62 F-green ids (40 saturate, 21 other limits/refusals, 1 missing-file case). MAIN owns complementary E + real S + any required mutants. `tests/sha256/record.py LOG --column stubE` records a complementary run without rewriting previous batches.
- Coverage validator (B3-6 cell-exact awk): seed 16, filled 0; 16 rows. `FROZEN-JHD.tsv` = 7,305 entries. `probe.sh` rejects one planted expectation hash (guard rc 1 + B3-2 breach), accepts committed inventory (rc 0), and finds all 4 raw __wrap symbols in the small executable. Actual cases/expected values stay unchanged.
- Final pinned Ruff 0.17.4 + Pyrefly 1.4.1 → `All checks passed!`, `0 diagnostics`; shellcheck covers all codec/S shell scripts. lean-fmt: `4 files, all formatted.` + `4 files, no findings.`; imported formatting bytes matched remote SHA-256. Final checks rc 0; service 5.258 s, peak 607.9M. LSP .c server unavailable; gcc/Lean compiler diagnostics used.
- Sampling/limits: all pinned CAVP vectors; generated data = one fixed seed, 64 arbitrary blobs, 40 branch groups/readers/Tasks, 80 random + 5 named frames. Actual 4GiB and ≥2^64-byte messages were not allocated; macro ceilings + approved public squeeze composition cover the intended limits. No proof/collision-resistance claim; no real S/E run, full gate or fuzz campaign here. C setup cache is source/header/compiler/output-digest scoped; reported vflab runs rebuilt it, so no cache-reuse timing claim.
- Finish: 16 filled rows, every S case run/recorded, prior cases frozen, checks pass; committed on wt/tester-3. Authoring downloads/logs/temporary work removed after recording; useful NIST browser tab retained. No work running. Authored changes stay under tests/; tool/c/vendor/tools/docs untouched beyond the one prescribed merge.

tester-DONE-3.3
