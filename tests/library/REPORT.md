# U4 batch 1 — tester-5

## Verdict

| surface | cases | A PASS / FAIL | B PASS / FAIL | red on ≥1 stub |
|---|---:|---:|---:|---:|
| A.b64 | 110 | 110 / 0 | 110 / 0 | 0 |
| A.semver | 113 | 113 / 0 | 113 / 0 | 0 |
| B.value | 220 | 138 / 82 | 9 / 211 | 220 |
| B.request | 76 | 61 / 15 | 1 / 75 | 76 |
| B.reply | 16 | 0 / 16 | 1 / 15 | 16 |
| B.lines | 15 | 1 / 14 | 2 / 13 | 15 |
| B.sig | 40 | 16 / 24 | 2 / 38 | 40 |
| B.cli | 22 | 1 / 21 | 1 / 21 | 22 |

612 cases; 389 red on ≥1 stub; 223 green on both (uncredited pending product mutants). Expected real-implementation reds = none. Real B remains unread + unrun; this is a prediction, not a green claim.

MAIN (merge at the U4 B commit): per-stub outputs `STUB-A.tsv` + `STUB-B.tsv` stay on `wt/tester-5` @ 0cb568c. Real B at 2eaff28 (`wip/u4-b-review`): 609/612 — `B.value.refuse.{nat,int}.integer-range.*` red = product defect (`decodeVal` took an integer beyond ±(2^53 − 1)), fixed → 612/612. The 223 A cases = mutant-credited: `tests/library/mutants.py` (54 hand mutants of the launch specs, each killing ≥1 A case; union 223/223; no survivor). MAIN cases `B.sig.mdata.{codomain-arrow,list-arg}` (reviewer-5 S7 regressions: metadata transparent) red at 2eaff28, green after the fix ⇒ 614 cases.

## Run + layout

- Canonical suite command (inside this worktree): `tools/vflab-run bash tests/library/run.sh`. A adds a `--list` prelude for the coverage catalog + the static checks below; B runs the canonical command alone.
- Seed = `4108190721` (`0xf4de0401`). Exploration: `tools/vflab-run env FVDEP_TEST_SEED=123 bash tests/library/run.sh`. `FVDEP_LIBRARY_CASE` (inside the remote command) selects a case substring.
- `LibraryHarness.lean` + `Driver.lean`: direct calls to the six launch specs, `render`, protocol APIs + `sigOf`. Independent test transport = length-prefixed values inside hex lines; no product codec transports its own test inputs/results.
- `reference.py`: independent RFC4648 bit-stream encoder + strict decoder, SemVer ASCII grammar + whole-type first-difference comparator, B2 layouts + J4 printer. No product definitions imported; stdlib base64/SemVer packages unused.
- `suite.py`: cases + fixed-seed properties; each PASS/FAIL line names its case, duration + failure detail. Slowest 10 cases printed; nonzero exit counts failures (saturated at 255). CLI tests compare raw stdout + exit codes.
- `COVERAGE.tsv`: every case → source clause + domain. `STUB-A.tsv`, `STUB-B.tsv`: complete per-case outputs + seconds. Per-case result/credit table below.
- `record.py A.log B.log --seed-log seed.log`: idempotent regeneration of these four evidence files.

## Independent domains

- RFC4648 §10 vectors, all 256 one-byte + 65,536 two-byte inputs for both encoders + decoder round trips. This is exhaustive at lengths 1/2, not at longer lengths. Longer lengths = 136 seeded samples (0..129, 255/256/257, 1023/1024/1025). Per alphabet: all 108 nonzero filling-bit tails, all 272 padding-position masks at 4/8 characters, every ASCII character at every position in one quartet (512), named non-ASCII/control/alphabet refusals + seeded mutated canonical texts.
- SemVer §§2/9/10 grammar witnesses/refusals incl. 256-digit numerics; all 64 §11 chain pairs; invalid whole-type alnum/build witnesses. Generated: 256 Valid values + 320 whole-type triples, plus 64 build-only comparisons. Properties: render round trip, swap, trans, eqIff, independent precedence, build ignored.
- B2: all seven value classes; ±(2^53−1), next integers as decimal strings, canonical decimal refusals, UTF16 0/65535/65536 + surrogates as code units, Version exact keys + tags. Text byte caps checked with ASCII/multibyte/non-BMP. 160 seeded typed values grade encode/decode layouts.
- B3: valid/invalid JSON requests, arity/op/kind/key refusals, J1/J2 string/depth/number/UTF8/surrogate bounds, canonical reply bytes + LF, arbitrary-byte LF framing (128 seeded streams). Replies above the request cap remain whole.
- B1 sigOf: six launch function-type shapes, every table type with plain/optional result, multiargument arrows, non-encodable types + dependent/higher-order shapes.
- B5 CLI: six targets, EOF, empty line, CRLF, final fragment, failure recovery, usage/target refusals, stdin preservation, 65536-character decode request → 98304-character hex result (both alphabets; byte-for-byte whole stdout).

## Checks + captured runs

| check | result |
|---|---|
| vflab Lean harness build | PASS; 36 targets |
| Ruff (pinned) on tests/library | PASS |
| Pyrefly (pinned, warning severity) on tests/library | PASS; 0 diagnostics |
| ShellCheck (pinned) on tests/library/run.sh | PASS |
| Seed override `1`, `A.semver.property` | `TOTAL 5 PASS 5 FAIL 0` |
| Lean source layout | lines ≤100 characters |
| LSP hover on Driver.lean | no server for .lean; build diagnostics used |
| Full gate | NOT RUN (brief) |
| Real B implementation | NOT RUN (blindness) |

Static command: `tools/vflab-run bash -c '.tools/bin/ruff check --config ruff.toml --output-format concise tests/library; .tools/bin/pyrefly check --config pyrefly.toml --output-format=min-text --min-severity=warn tests/library; .tools/bin/shellcheck tests/library/run.sh'` (final run uses `set -e`). The first two static attempts found test-code typing errors/warning; fixed before these final runs.

| product revision | summary | suite rc | setup/build failures |
|---|---|---:|---|
| stub A `b7c271a` | `TOTAL 612 PASS 440 FAIL 172` | 172 | none |
| stub B `f84b956` | `TOTAL 612 PASS 239 FAIL 373` | 255 | none |

A accounting: `vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=172/n/a; Service runtime: 37.033s; CPU time consumed: 39.471s; Memory peak: 586.8M (swap: 0B)`

B accounting: `vflab-run: Finished with result: exit-code; Main processes terminated with: code=exited, status=255/EXCEPTION; Service runtime: 36.673s; CPU time consumed: 39.025s; Memory peak: 582.5M (swap: 0B)`

Seed-check command: `tools/vflab-run env FVDEP_TEST_SEED=1 FVDEP_LIBRARY_CASE=A.semver.property bash tests/library/run.sh` → rc 0.

## Questions for MAIN + credit limits

- A's launch definitions are real + byte-identical across the prescribed stubs. Their green tests need product-mutant firing evidence. The write allowlist excluded library-source mutations; MAIN's B6 campaign can supply it.
- Cases green on both stubs stay visible + uncredited (table below). A red counts only when it reaches its target assertion. `B.cli.unknown-stdin-unread` uses a finite pipe: exit 2 + an exact marker left unread. Earlier live-pipe experiments timed out on both stubs (uncredited); the final fixture reaches behavioral assertions without a timeout. No timeout contributes credit.
- No contract/API defect identified. Not covered here: conformance trial A8, registry/index C, proof faithfulness, fuzz campaigns, real B green run. MAIN owns those parts. No target test skipped or xfailed.

## Per-case results

Command per row = the canonical suite command above, with the row's case selected by `FVDEP_LIBRARY_CASE`. Full stdout line = result + case + seconds + detail in the corresponding TSV (`-` = empty detail). `red` below means a stub red, not automatic mutant credit.

| case | A | B | stub detection |
|---|---|---|---|
| `A.b64.vector.0.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.0.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.0.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.0.url.decode` | PASS | PASS | uncredited |
| `A.b64.vector.1.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.1.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.1.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.1.url.decode` | PASS | PASS | uncredited |
| `A.b64.vector.2.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.2.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.2.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.2.url.decode` | PASS | PASS | uncredited |
| `A.b64.vector.3.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.3.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.3.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.3.url.decode` | PASS | PASS | uncredited |
| `A.b64.vector.4.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.4.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.4.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.4.url.decode` | PASS | PASS | uncredited |
| `A.b64.vector.5.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.5.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.5.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.5.url.decode` | PASS | PASS | uncredited |
| `A.b64.vector.6.std.encode` | PASS | PASS | uncredited |
| `A.b64.vector.6.std.decode` | PASS | PASS | uncredited |
| `A.b64.vector.6.url.encode` | PASS | PASS | uncredited |
| `A.b64.vector.6.url.decode` | PASS | PASS | uncredited |
| `A.b64.exhaustive.1.encode` | PASS | PASS | uncredited |
| `A.b64.exhaustive.1.encodeUrl` | PASS | PASS | uncredited |
| `A.b64.exhaustive.1.roundtrip` | PASS | PASS | uncredited |
| `A.b64.exhaustive.1.roundtripUrl` | PASS | PASS | uncredited |
| `A.b64.exhaustive.2.encode` | PASS | PASS | uncredited |
| `A.b64.exhaustive.2.encodeUrl` | PASS | PASS | uncredited |
| `A.b64.exhaustive.2.roundtrip` | PASS | PASS | uncredited |
| `A.b64.exhaustive.2.roundtripUrl` | PASS | PASS | uncredited |
| `A.b64.generated.encode` | PASS | PASS | uncredited |
| `A.b64.generated.encodeUrl` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.length1` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.length2` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.length3` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.length5` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding1` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding2` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding3` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding4` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding3only` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding5` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding-tail-missing` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding-after-full` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding-interior` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding-interior3` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding-double-group` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.padding-then-char` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.space` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.tab` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.lf` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.crlf` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.space-around` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.nul` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.del` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.nonascii-latin` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.nonascii-bmp` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.nonascii-nonbmp` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.nonascii-fullwidth` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.bits-one-byte` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.bits-two-byte` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.foreign0` | PASS | PASS | uncredited |
| `A.b64.refuse.decode.foreign1` | PASS | PASS | uncredited |
| `A.b64.filling-bits.decode` | PASS | PASS | uncredited |
| `A.b64.padding-masks.decode` | PASS | PASS | uncredited |
| `A.b64.ascii-domain.decode` | PASS | PASS | uncredited |
| `A.b64.generated.inverse.decode` | PASS | PASS | uncredited |
| `A.b64.generated.canonical.decode` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.length1` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.length2` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.length3` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.length5` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding1` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding2` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding3` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding4` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding3only` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding5` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding-tail-missing` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding-after-full` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding-interior` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding-interior3` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding-double-group` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.padding-then-char` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.space` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.tab` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.lf` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.crlf` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.space-around` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.nul` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.del` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.nonascii-latin` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.nonascii-bmp` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.nonascii-nonbmp` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.nonascii-fullwidth` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.bits-one-byte` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.bits-two-byte` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.foreign0` | PASS | PASS | uncredited |
| `A.b64.refuse.decodeUrl.foreign1` | PASS | PASS | uncredited |
| `A.b64.filling-bits.decodeUrl` | PASS | PASS | uncredited |
| `A.b64.padding-masks.decodeUrl` | PASS | PASS | uncredited |
| `A.b64.ascii-domain.decodeUrl` | PASS | PASS | uncredited |
| `A.b64.generated.inverse.decodeUrl` | PASS | PASS | uncredited |
| `A.b64.generated.canonical.decodeUrl` | PASS | PASS | uncredited |
| `A.semver.parse.accept.00` | PASS | PASS | uncredited |
| `A.semver.render.00` | PASS | PASS | uncredited |
| `A.semver.parse.accept.01` | PASS | PASS | uncredited |
| `A.semver.render.01` | PASS | PASS | uncredited |
| `A.semver.parse.accept.02` | PASS | PASS | uncredited |
| `A.semver.render.02` | PASS | PASS | uncredited |
| `A.semver.parse.accept.03` | PASS | PASS | uncredited |
| `A.semver.render.03` | PASS | PASS | uncredited |
| `A.semver.parse.accept.04` | PASS | PASS | uncredited |
| `A.semver.render.04` | PASS | PASS | uncredited |
| `A.semver.parse.accept.05` | PASS | PASS | uncredited |
| `A.semver.render.05` | PASS | PASS | uncredited |
| `A.semver.parse.accept.06` | PASS | PASS | uncredited |
| `A.semver.render.06` | PASS | PASS | uncredited |
| `A.semver.parse.accept.07` | PASS | PASS | uncredited |
| `A.semver.render.07` | PASS | PASS | uncredited |
| `A.semver.parse.accept.08` | PASS | PASS | uncredited |
| `A.semver.render.08` | PASS | PASS | uncredited |
| `A.semver.parse.accept.09` | PASS | PASS | uncredited |
| `A.semver.render.09` | PASS | PASS | uncredited |
| `A.semver.parse.accept.10` | PASS | PASS | uncredited |
| `A.semver.render.10` | PASS | PASS | uncredited |
| `A.semver.parse.accept.11` | PASS | PASS | uncredited |
| `A.semver.render.11` | PASS | PASS | uncredited |
| `A.semver.parse.accept.12` | PASS | PASS | uncredited |
| `A.semver.render.12` | PASS | PASS | uncredited |
| `A.semver.parse.accept.13` | PASS | PASS | uncredited |
| `A.semver.render.13` | PASS | PASS | uncredited |
| `A.semver.parse.accept.14` | PASS | PASS | uncredited |
| `A.semver.render.14` | PASS | PASS | uncredited |
| `A.semver.parse.accept.15` | PASS | PASS | uncredited |
| `A.semver.render.15` | PASS | PASS | uncredited |
| `A.semver.parse.accept.16` | PASS | PASS | uncredited |
| `A.semver.render.16` | PASS | PASS | uncredited |
| `A.semver.parse.accept.17` | PASS | PASS | uncredited |
| `A.semver.render.17` | PASS | PASS | uncredited |
| `A.semver.parse.accept.18` | PASS | PASS | uncredited |
| `A.semver.render.18` | PASS | PASS | uncredited |
| `A.semver.parse.accept.19` | PASS | PASS | uncredited |
| `A.semver.render.19` | PASS | PASS | uncredited |
| `A.semver.parse.accept.20` | PASS | PASS | uncredited |
| `A.semver.render.20` | PASS | PASS | uncredited |
| `A.semver.parse.accept.21` | PASS | PASS | uncredited |
| `A.semver.render.21` | PASS | PASS | uncredited |
| `A.semver.parse.accept.22` | PASS | PASS | uncredited |
| `A.semver.render.22` | PASS | PASS | uncredited |
| `A.semver.parse.accept.23` | PASS | PASS | uncredited |
| `A.semver.render.23` | PASS | PASS | uncredited |
| `A.semver.parse.accept.24` | PASS | PASS | uncredited |
| `A.semver.render.24` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.00` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.01` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.02` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.03` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.04` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.05` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.06` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.07` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.08` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.09` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.10` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.11` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.12` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.13` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.14` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.15` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.16` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.17` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.18` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.19` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.20` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.21` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.22` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.23` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.24` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.25` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.26` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.27` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.28` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.29` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.30` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.31` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.32` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.33` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.34` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.35` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.36` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.37` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.38` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.39` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.40` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.41` | PASS | PASS | uncredited |
| `A.semver.parse.refuse.42` | PASS | PASS | uncredited |
| `A.semver.precedence-chain` | PASS | PASS | uncredited |
| `A.semver.whole-type.00` | PASS | PASS | uncredited |
| `A.semver.whole-type.01` | PASS | PASS | uncredited |
| `A.semver.whole-type.02` | PASS | PASS | uncredited |
| `A.semver.whole-type.03` | PASS | PASS | uncredited |
| `A.semver.whole-type.04` | PASS | PASS | uncredited |
| `A.semver.whole-type.05` | PASS | PASS | uncredited |
| `A.semver.whole-type.06` | PASS | PASS | uncredited |
| `A.semver.whole-type.07` | PASS | PASS | uncredited |
| `A.semver.whole-type.08` | PASS | PASS | uncredited |
| `A.semver.whole-type.09` | PASS | PASS | uncredited |
| `A.semver.whole-type.10` | PASS | PASS | uncredited |
| `A.semver.whole-type.11` | PASS | PASS | uncredited |
| `A.semver.generated.render` | PASS | PASS | uncredited |
| `A.semver.generated.render-roundtrip` | PASS | PASS | uncredited |
| `A.semver.property.swap` | PASS | PASS | uncredited |
| `A.semver.property.trans` | PASS | PASS | uncredited |
| `A.semver.property.eqIff` | PASS | PASS | uncredited |
| `A.semver.property.precedence` | PASS | PASS | uncredited |
| `A.semver.property.build-ignored` | PASS | PASS | uncredited |
| `B.value.encode.bytes.0` | FAIL | PASS | red |
| `B.value.decode.bytes.0` | FAIL | PASS | red |
| `B.value.encode.bytes.1` | FAIL | FAIL | red |
| `B.value.decode.bytes.1` | FAIL | FAIL | red |
| `B.value.encode.bytes.2` | FAIL | FAIL | red |
| `B.value.decode.bytes.2` | FAIL | FAIL | red |
| `B.value.encode.bytes.3` | FAIL | FAIL | red |
| `B.value.decode.bytes.3` | FAIL | FAIL | red |
| `B.value.encode.bytes.4` | FAIL | FAIL | red |
| `B.value.decode.bytes.4` | FAIL | FAIL | red |
| `B.value.encode.text.empty` | FAIL | PASS | red |
| `B.value.decode.text.empty` | FAIL | PASS | red |
| `B.value.encode.text.ascii` | FAIL | FAIL | red |
| `B.value.decode.text.ascii` | FAIL | FAIL | red |
| `B.value.encode.text.controls` | FAIL | FAIL | red |
| `B.value.decode.text.controls` | FAIL | FAIL | red |
| `B.value.encode.text.unicode` | FAIL | FAIL | red |
| `B.value.decode.text.unicode` | FAIL | FAIL | red |
| `B.value.encode.text.cap-ascii` | FAIL | FAIL | red |
| `B.value.decode.text.cap-ascii` | FAIL | FAIL | red |
| `B.value.encode.text.cap-utf8` | FAIL | FAIL | red |
| `B.value.decode.text.cap-utf8` | FAIL | FAIL | red |
| `B.value.encode.text.cap-nonbmp` | FAIL | FAIL | red |
| `B.value.decode.text.cap-nonbmp` | FAIL | FAIL | red |
| `B.value.encode.utf16.0` | FAIL | FAIL | red |
| `B.value.decode.utf16.0` | FAIL | PASS | red |
| `B.value.encode.utf16.1` | FAIL | FAIL | red |
| `B.value.decode.utf16.1` | FAIL | FAIL | red |
| `B.value.encode.utf16.2` | FAIL | FAIL | red |
| `B.value.decode.utf16.2` | FAIL | FAIL | red |
| `B.value.encode.utf16.3` | FAIL | FAIL | red |
| `B.value.decode.utf16.3` | FAIL | FAIL | red |
| `B.value.encode.nat.0` | FAIL | FAIL | red |
| `B.value.decode.nat.0` | FAIL | PASS | red |
| `B.value.encode.nat.1` | FAIL | FAIL | red |
| `B.value.decode.nat.1` | FAIL | FAIL | red |
| `B.value.encode.nat.2` | FAIL | FAIL | red |
| `B.value.decode.nat.2` | FAIL | FAIL | red |
| `B.value.encode.nat.3` | FAIL | FAIL | red |
| `B.value.decode.nat.3` | FAIL | FAIL | red |
| `B.value.encode.nat.4` | FAIL | FAIL | red |
| `B.value.decode.nat.4` | FAIL | FAIL | red |
| `B.value.encode.nat.5` | FAIL | FAIL | red |
| `B.value.decode.nat.5` | FAIL | FAIL | red |
| `B.value.encode.nat.6` | FAIL | FAIL | red |
| `B.value.decode.nat.6` | FAIL | FAIL | red |
| `B.value.encode.int.0` | FAIL | FAIL | red |
| `B.value.decode.int.0` | FAIL | PASS | red |
| `B.value.encode.int.1` | FAIL | FAIL | red |
| `B.value.decode.int.1` | FAIL | FAIL | red |
| `B.value.encode.int.2` | FAIL | FAIL | red |
| `B.value.decode.int.2` | FAIL | FAIL | red |
| `B.value.encode.int.3` | FAIL | FAIL | red |
| `B.value.decode.int.3` | FAIL | FAIL | red |
| `B.value.encode.int.4` | FAIL | FAIL | red |
| `B.value.decode.int.4` | FAIL | FAIL | red |
| `B.value.encode.int.5` | FAIL | FAIL | red |
| `B.value.decode.int.5` | FAIL | FAIL | red |
| `B.value.encode.int.6` | FAIL | FAIL | red |
| `B.value.decode.int.6` | FAIL | FAIL | red |
| `B.value.encode.int.7` | FAIL | FAIL | red |
| `B.value.decode.int.7` | FAIL | FAIL | red |
| `B.value.encode.int.8` | FAIL | FAIL | red |
| `B.value.decode.int.8` | FAIL | FAIL | red |
| `B.value.encode.int.9` | FAIL | FAIL | red |
| `B.value.decode.int.9` | FAIL | FAIL | red |
| `B.value.encode.int.10` | FAIL | FAIL | red |
| `B.value.decode.int.10` | FAIL | FAIL | red |
| `B.value.encode.ordering.lt` | FAIL | FAIL | red |
| `B.value.decode.ordering.lt` | FAIL | FAIL | red |
| `B.value.encode.ordering.eq` | FAIL | FAIL | red |
| `B.value.decode.ordering.eq` | FAIL | PASS | red |
| `B.value.encode.ordering.gt` | FAIL | FAIL | red |
| `B.value.decode.ordering.gt` | FAIL | FAIL | red |
| `B.value.encode.version.0` | FAIL | FAIL | red |
| `B.value.decode.version.0` | FAIL | PASS | red |
| `B.value.encode.version.1` | FAIL | FAIL | red |
| `B.value.decode.version.1` | FAIL | FAIL | red |
| `B.value.encode.version.2` | FAIL | FAIL | red |
| `B.value.decode.version.2` | FAIL | FAIL | red |
| `B.value.refuse.bytes.0` | PASS | FAIL | red |
| `B.value.refuse.bytes.1` | PASS | FAIL | red |
| `B.value.refuse.bytes.2` | PASS | FAIL | red |
| `B.value.refuse.bytes.3` | PASS | FAIL | red |
| `B.value.refuse.bytes.4` | PASS | FAIL | red |
| `B.value.refuse.bytes.5` | PASS | FAIL | red |
| `B.value.refuse.bytes.6` | PASS | FAIL | red |
| `B.value.refuse.bytes.7` | PASS | FAIL | red |
| `B.value.refuse.bytes.8` | PASS | FAIL | red |
| `B.value.refuse.bytes.9` | PASS | FAIL | red |
| `B.value.refuse.bytes.10` | PASS | FAIL | red |
| `B.value.refuse.bytes.11` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.0` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.1` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.2` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.3` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.4` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.5` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.6` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.7` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.8` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.9` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.10` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.11` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.12` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.13` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.14` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.15` | PASS | FAIL | red |
| `B.value.refuse.nat.decimal.16` | PASS | FAIL | red |
| `B.value.refuse.nat.integer-range.0` | PASS | FAIL | red |
| `B.value.refuse.nat.integer-range.1` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.0` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.1` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.2` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.3` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.4` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.5` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.6` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.7` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.8` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.9` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.10` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.11` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.12` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.13` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.14` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.15` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.16` | PASS | FAIL | red |
| `B.value.refuse.int.decimal.17` | PASS | FAIL | red |
| `B.value.refuse.int.integer-range.0` | PASS | FAIL | red |
| `B.value.refuse.int.integer-range.1` | PASS | FAIL | red |
| `B.value.refuse.nat.negative` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.0` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.1` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.2` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.3` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.4` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.5` | PASS | FAIL | red |
| `B.value.refuse.utf16.codeunit.6` | PASS | FAIL | red |
| `B.value.refuse.ordering.0` | PASS | FAIL | red |
| `B.value.refuse.ordering.1` | PASS | FAIL | red |
| `B.value.refuse.ordering.2` | PASS | FAIL | red |
| `B.value.refuse.ordering.3` | PASS | FAIL | red |
| `B.value.refuse.ordering.4` | PASS | FAIL | red |
| `B.value.refuse.bytes.kind.0` | PASS | FAIL | red |
| `B.value.refuse.bytes.kind.1` | PASS | FAIL | red |
| `B.value.refuse.bytes.kind.2` | PASS | FAIL | red |
| `B.value.refuse.bytes.kind.3` | PASS | FAIL | red |
| `B.value.refuse.bytes.kind.4` | PASS | FAIL | red |
| `B.value.refuse.text.kind.0` | PASS | FAIL | red |
| `B.value.refuse.text.kind.1` | PASS | FAIL | red |
| `B.value.refuse.text.kind.2` | PASS | FAIL | red |
| `B.value.refuse.text.kind.3` | PASS | FAIL | red |
| `B.value.refuse.text.kind.4` | PASS | FAIL | red |
| `B.value.refuse.utf16.kind.0` | PASS | FAIL | red |
| `B.value.refuse.utf16.kind.1` | PASS | FAIL | red |
| `B.value.refuse.utf16.kind.2` | PASS | FAIL | red |
| `B.value.refuse.utf16.kind.3` | PASS | FAIL | red |
| `B.value.refuse.utf16.kind.4` | PASS | FAIL | red |
| `B.value.refuse.nat.kind.0` | PASS | FAIL | red |
| `B.value.refuse.nat.kind.1` | PASS | FAIL | red |
| `B.value.refuse.nat.kind.2` | PASS | FAIL | red |
| `B.value.refuse.nat.kind.3` | PASS | FAIL | red |
| `B.value.refuse.int.kind.0` | PASS | FAIL | red |
| `B.value.refuse.int.kind.1` | PASS | FAIL | red |
| `B.value.refuse.int.kind.2` | PASS | FAIL | red |
| `B.value.refuse.int.kind.3` | PASS | FAIL | red |
| `B.value.refuse.ordering.kind.0` | PASS | FAIL | red |
| `B.value.refuse.ordering.kind.1` | PASS | FAIL | red |
| `B.value.refuse.ordering.kind.2` | PASS | FAIL | red |
| `B.value.refuse.ordering.kind.3` | PASS | FAIL | red |
| `B.value.refuse.ordering.kind.4` | PASS | FAIL | red |
| `B.value.refuse.version.kind.0` | PASS | FAIL | red |
| `B.value.refuse.version.kind.1` | PASS | FAIL | red |
| `B.value.refuse.version.kind.2` | PASS | FAIL | red |
| `B.value.refuse.version.kind.3` | PASS | FAIL | red |
| `B.value.refuse.version.kind.4` | PASS | FAIL | red |
| `B.value.refuse.version.missing.build` | PASS | FAIL | red |
| `B.value.refuse.version.missing.major` | PASS | FAIL | red |
| `B.value.refuse.version.missing.minor` | PASS | FAIL | red |
| `B.value.refuse.version.missing.patch` | PASS | FAIL | red |
| `B.value.refuse.version.missing.pre` | PASS | FAIL | red |
| `B.value.refuse.version.extra` | PASS | FAIL | red |
| `B.value.refuse.version.major.0` | PASS | FAIL | red |
| `B.value.refuse.version.major.1` | PASS | FAIL | red |
| `B.value.refuse.version.major.2` | PASS | FAIL | red |
| `B.value.refuse.version.major.3` | PASS | FAIL | red |
| `B.value.refuse.version.major.4` | PASS | FAIL | red |
| `B.value.refuse.version.minor.0` | PASS | FAIL | red |
| `B.value.refuse.version.minor.1` | PASS | FAIL | red |
| `B.value.refuse.version.minor.2` | PASS | FAIL | red |
| `B.value.refuse.version.minor.3` | PASS | FAIL | red |
| `B.value.refuse.version.minor.4` | PASS | FAIL | red |
| `B.value.refuse.version.patch.0` | PASS | FAIL | red |
| `B.value.refuse.version.patch.1` | PASS | FAIL | red |
| `B.value.refuse.version.patch.2` | PASS | FAIL | red |
| `B.value.refuse.version.patch.3` | PASS | FAIL | red |
| `B.value.refuse.version.patch.4` | PASS | FAIL | red |
| `B.value.refuse.version.pre.0` | PASS | FAIL | red |
| `B.value.refuse.version.pre.1` | PASS | FAIL | red |
| `B.value.refuse.version.pre.2` | PASS | FAIL | red |
| `B.value.refuse.version.pre.3` | PASS | FAIL | red |
| `B.value.refuse.version.pre.4` | PASS | FAIL | red |
| `B.value.refuse.version.pre.5` | PASS | FAIL | red |
| `B.value.refuse.version.pre.6` | PASS | FAIL | red |
| `B.value.refuse.version.pre.7` | PASS | FAIL | red |
| `B.value.refuse.version.pre.8` | PASS | FAIL | red |
| `B.value.refuse.version.pre.9` | PASS | FAIL | red |
| `B.value.refuse.version.pre.10` | PASS | FAIL | red |
| `B.value.refuse.version.pre.11` | PASS | FAIL | red |
| `B.value.refuse.version.pre.12` | PASS | FAIL | red |
| `B.value.refuse.version.build.0` | PASS | FAIL | red |
| `B.value.refuse.version.build.1` | PASS | FAIL | red |
| `B.value.refuse.version.build.2` | PASS | FAIL | red |
| `B.value.refuse.version.build.3` | PASS | FAIL | red |
| `B.value.refuse.version.build.4` | PASS | FAIL | red |
| `B.value.refuse.version.build.5` | PASS | FAIL | red |
| `B.value.refuse.version.build.6` | PASS | FAIL | red |
| `B.value.property.encode-layout` | FAIL | FAIL | red |
| `B.value.property.decode-encode` | FAIL | FAIL | red |
| `B.request.empty-text` | FAIL | PASS | red |
| `B.request.unicode` | FAIL | FAIL | red |
| `B.request.order-whitespace` | FAIL | FAIL | red |
| `B.request.escape-pair` | FAIL | FAIL | red |
| `B.request.escaped-keys` | FAIL | FAIL | red |
| `B.request.slash` | FAIL | FAIL | red |
| `B.request.cap-ascii` | FAIL | FAIL | red |
| `B.request.cap-multibyte` | FAIL | FAIL | red |
| `B.request.empty-line` | PASS | FAIL | red |
| `B.request.whitespace` | PASS | FAIL | red |
| `B.request.malformed` | PASS | FAIL | red |
| `B.request.null` | PASS | FAIL | red |
| `B.request.array` | PASS | FAIL | red |
| `B.request.string` | PASS | FAIL | red |
| `B.request.missing-op` | PASS | FAIL | red |
| `B.request.missing-args` | PASS | FAIL | red |
| `B.request.extra` | PASS | FAIL | red |
| `B.request.op-kind` | PASS | FAIL | red |
| `B.request.args-kind` | PASS | FAIL | red |
| `B.request.wrong-op` | PASS | FAIL | red |
| `B.request.zero-arity` | PASS | FAIL | red |
| `B.request.two-arity` | PASS | FAIL | red |
| `B.request.wrong-arg` | PASS | FAIL | red |
| `B.request.duplicate-op` | PASS | FAIL | red |
| `B.request.duplicate-escaped` | PASS | FAIL | red |
| `B.request.lone-high` | PASS | FAIL | red |
| `B.request.lone-low` | PASS | FAIL | red |
| `B.request.high-then-text` | PASS | FAIL | red |
| `B.request.encoded-surrogate` | PASS | FAIL | red |
| `B.request.utf8-overlong` | PASS | FAIL | red |
| `B.request.utf8-stray` | PASS | FAIL | red |
| `B.request.utf8-high` | PASS | FAIL | red |
| `B.request.bom` | PASS | FAIL | red |
| `B.request.raw-control` | PASS | FAIL | red |
| `B.request.cap-plus-one` | PASS | FAIL | red |
| `B.request.cap-multibyte-plus` | PASS | FAIL | red |
| `B.request.depth33` | PASS | FAIL | red |
| `B.request.depth-priority` | PASS | FAIL | red |
| `B.request.trailing` | PASS | FAIL | red |
| `B.request.trailing-json` | PASS | FAIL | red |
| `B.request.trailing-comma` | PASS | FAIL | red |
| `B.request.typed.bytes.accept` | FAIL | FAIL | red |
| `B.request.typed.bytes.refuse.0` | PASS | FAIL | red |
| `B.request.typed.bytes.refuse.1` | PASS | FAIL | red |
| `B.request.typed.bytes.refuse.2` | PASS | FAIL | red |
| `B.request.typed.bytes.refuse.3` | PASS | FAIL | red |
| `B.request.typed.utf16.accept` | FAIL | FAIL | red |
| `B.request.typed.utf16.refuse.0` | PASS | FAIL | red |
| `B.request.typed.utf16.refuse.1` | PASS | FAIL | red |
| `B.request.typed.utf16.refuse.2` | PASS | FAIL | red |
| `B.request.typed.utf16.refuse.3` | PASS | FAIL | red |
| `B.request.typed.nat.accept` | FAIL | FAIL | red |
| `B.request.typed.nat.refuse.0` | PASS | FAIL | red |
| `B.request.typed.nat.refuse.1` | PASS | FAIL | red |
| `B.request.typed.nat.refuse.2` | PASS | FAIL | red |
| `B.request.typed.nat.refuse.3` | PASS | FAIL | red |
| `B.request.typed.int.accept` | FAIL | FAIL | red |
| `B.request.typed.int.refuse.0` | PASS | FAIL | red |
| `B.request.typed.int.refuse.1` | PASS | FAIL | red |
| `B.request.typed.int.refuse.2` | PASS | FAIL | red |
| `B.request.typed.int.refuse.3` | PASS | FAIL | red |
| `B.request.typed.ordering.accept` | FAIL | FAIL | red |
| `B.request.typed.ordering.refuse.0` | PASS | FAIL | red |
| `B.request.typed.ordering.refuse.1` | PASS | FAIL | red |
| `B.request.typed.ordering.refuse.2` | PASS | FAIL | red |
| `B.request.typed.version.accept` | FAIL | FAIL | red |
| `B.request.typed.version.refuse.0` | PASS | FAIL | red |
| `B.request.typed.version.refuse.1` | PASS | FAIL | red |
| `B.request.json-number.0` | PASS | FAIL | red |
| `B.request.json-number.1` | PASS | FAIL | red |
| `B.request.json-number.2` | PASS | FAIL | red |
| `B.request.json-number.3` | PASS | FAIL | red |
| `B.request.json-number.4` | PASS | FAIL | red |
| `B.request.json-number.5` | PASS | FAIL | red |
| `B.request.two-args.accept` | FAIL | FAIL | red |
| `B.request.two-args.wrong-order` | PASS | FAIL | red |
| `B.reply.ok.00` | FAIL | FAIL | red |
| `B.reply.ok.01` | FAIL | PASS | red |
| `B.reply.ok.02` | FAIL | FAIL | red |
| `B.reply.ok.03` | FAIL | FAIL | red |
| `B.reply.ok.04` | FAIL | FAIL | red |
| `B.reply.ok.05` | FAIL | FAIL | red |
| `B.reply.ok.06` | FAIL | FAIL | red |
| `B.reply.ok.07` | FAIL | FAIL | red |
| `B.reply.ok.08` | FAIL | FAIL | red |
| `B.reply.ok.09` | FAIL | FAIL | red |
| `B.reply.ok.10` | FAIL | FAIL | red |
| `B.reply.none` | FAIL | FAIL | red |
| `B.reply.invalid.0` | FAIL | FAIL | red |
| `B.reply.invalid.1` | FAIL | FAIL | red |
| `B.reply.invalid.2` | FAIL | FAIL | red |
| `B.reply.invalid.3` | FAIL | FAIL | red |
| `B.lines.00` | PASS | FAIL | red |
| `B.lines.01` | FAIL | FAIL | red |
| `B.lines.02` | FAIL | FAIL | red |
| `B.lines.03` | FAIL | PASS | red |
| `B.lines.04` | FAIL | FAIL | red |
| `B.lines.05` | FAIL | FAIL | red |
| `B.lines.06` | FAIL | FAIL | red |
| `B.lines.07` | FAIL | FAIL | red |
| `B.lines.08` | FAIL | FAIL | red |
| `B.lines.09` | FAIL | PASS | red |
| `B.lines.10` | FAIL | FAIL | red |
| `B.lines.11` | FAIL | FAIL | red |
| `B.lines.12` | FAIL | FAIL | red |
| `B.lines.13` | FAIL | FAIL | red |
| `B.lines.property.framing` | FAIL | FAIL | red |
| `B.sig.launch.0` | FAIL | PASS | red |
| `B.sig.launch.1` | FAIL | FAIL | red |
| `B.sig.launch.2` | FAIL | FAIL | red |
| `B.sig.launch.3` | FAIL | FAIL | red |
| `B.sig.launch.4` | FAIL | PASS | red |
| `B.sig.launch.5` | FAIL | FAIL | red |
| `B.sig.table.bytes-list.plain` | FAIL | FAIL | red |
| `B.sig.table.bytes-list.option` | FAIL | FAIL | red |
| `B.sig.table.bytes-array.plain` | FAIL | FAIL | red |
| `B.sig.table.bytes-array.option` | FAIL | FAIL | red |
| `B.sig.table.text.plain` | FAIL | FAIL | red |
| `B.sig.table.text.option` | FAIL | FAIL | red |
| `B.sig.table.utf16.plain` | FAIL | FAIL | red |
| `B.sig.table.utf16.option` | FAIL | FAIL | red |
| `B.sig.table.nat.plain` | FAIL | FAIL | red |
| `B.sig.table.nat.option` | FAIL | FAIL | red |
| `B.sig.table.int.plain` | FAIL | FAIL | red |
| `B.sig.table.int.option` | FAIL | FAIL | red |
| `B.sig.table.ordering.plain` | FAIL | FAIL | red |
| `B.sig.table.ordering.option` | FAIL | FAIL | red |
| `B.sig.table.version.plain` | FAIL | FAIL | red |
| `B.sig.table.version.option` | FAIL | FAIL | red |
| `B.sig.multiple` | FAIL | FAIL | red |
| `B.sig.option-utf16` | FAIL | FAIL | red |
| `B.sig.refuse.00` | PASS | FAIL | red |
| `B.sig.refuse.01` | PASS | FAIL | red |
| `B.sig.refuse.02` | PASS | FAIL | red |
| `B.sig.refuse.03` | PASS | FAIL | red |
| `B.sig.refuse.04` | PASS | FAIL | red |
| `B.sig.refuse.05` | PASS | FAIL | red |
| `B.sig.refuse.06` | PASS | FAIL | red |
| `B.sig.refuse.07` | PASS | FAIL | red |
| `B.sig.refuse.08` | PASS | FAIL | red |
| `B.sig.refuse.09` | PASS | FAIL | red |
| `B.sig.refuse.10` | PASS | FAIL | red |
| `B.sig.refuse.11` | PASS | FAIL | red |
| `B.sig.refuse.12` | PASS | FAIL | red |
| `B.sig.refuse.13` | PASS | FAIL | red |
| `B.sig.refuse.14` | PASS | FAIL | red |
| `B.sig.refuse.15` | PASS | FAIL | red |
| `B.cli.target.base64.encode` | FAIL | FAIL | red |
| `B.cli.target.base64.encode_url` | FAIL | FAIL | red |
| `B.cli.target.base64.decode` | FAIL | FAIL | red |
| `B.cli.target.base64.decode_url` | FAIL | FAIL | red |
| `B.cli.target.semver.parse` | FAIL | FAIL | red |
| `B.cli.target.semver.compare` | FAIL | FAIL | red |
| `B.cli.empty-eof` | PASS | FAIL | red |
| `B.cli.crlf` | FAIL | FAIL | red |
| `B.cli.final-fragment` | FAIL | FAIL | red |
| `B.cli.final-lf` | FAIL | FAIL | red |
| `B.cli.none-result` | FAIL | FAIL | red |
| `B.cli.empty-result` | FAIL | PASS | red |
| `B.cli.recovery` | FAIL | FAIL | red |
| `B.cli.usage.0` | FAIL | FAIL | red |
| `B.cli.usage.1` | FAIL | FAIL | red |
| `B.cli.usage.2` | FAIL | FAIL | red |
| `B.cli.usage.3` | FAIL | FAIL | red |
| `B.cli.usage.4` | FAIL | FAIL | red |
| `B.cli.usage.5` | FAIL | FAIL | red |
| `B.cli.unknown-stdin-unread` | FAIL | FAIL | red |
| `B.cli.maximal-expansion` | FAIL | FAIL | red |
| `B.cli.maximal-expansion-url` | FAIL | FAIL | red |
