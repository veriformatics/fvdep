# Stack + core-method ruling — IMPLEMENT orientation record (agent-read)

Rulings = `.agent/spec.md` Decisions (Stack, Conformance method, Verification profile, Library layout + identity, Library API v1, Data formats, Public interface, Lifecycle + profile evolution, Domains + deviation algebra, Self-verification scope, Growth, Accepted risks). Raw evidence = local branch `wip/spike-evidence` (`evidence/`: spike protocol, grader, fixtures, controls, results, harvest, consultant + scientist deliverables, research tables); spike code = `wt/builder-1`, `wt/builder-2`.

## Protocol
- Check fixed before the first spike (scientist-2 appraised): `spike-check.md` v2 rows c1–c13 + c11 bundle + L1–L4 + K + R (31), grader v3.1 (G1–G6 repairs: exact stdout line, kernel status class, filesystem absence, c11 execution evidence + live listener, library unchanged incl. mtimes, exact fixture set) with controls 16/16 (contract oracle 31/31; always-PROVEN, liar + always-reject dummies fail as designed); manual rows J1 (decision core: soundness, completeness, refusal keeps prior state incl. absent), J2 (evidence path), J3 (atomic replacement).
- Amendment A1 (after the user's instruction to compute primarily on vflab): M1 = two fresh-nonce v3.1 runs per arm on vflab (`fvapi_gate.slice`); desktop runs supplementary. Repair accounting: c14 link plant (descriptive probe, outside the graded rows) repaired by MAIN in both arms after provider-classifier stops; A's J1 gap = A's one repair round on a required row.

## Arms
| arm | commits | M1 vflab | J1–J3 |
|---|---|---|---|
| A Lean throughout | 46a2f4e builder-1 (stopped by provider classifier) → 4c23c04 MAIN c14 repair → 8af3a11 MAIN J1 repair (lock state `Option String`, `refusal_keeps_absent`) | 4c23c04: 31/31, 31/31 (484 s, 535 s); 8af3a11: 31/31, 31/31 (531 s, 506 s) | pass (J1 after 8af3a11: 5 theorems `[propext]`, `leanchecker` rc 0) |
| B Python shell + Lean core | 4f37ed8 builder-2 → 62c1445 leftovers (red test) → 29e91a8 MAIN c14 repair (exports → supervisor-only dir) | 29e91a8: 31/31, 31/31 (253 s, 252 s) | pass |

## Findings that bind the product
- c14 (proof build code plants links in its writable dir; supervisor later writes through them) hit both arms: A 46a2f4e overwrote 14/17 host sentinels; B 4f37ed8 reported PROVEN while overwriting a host file with the 17,386,239-byte export ⇒ supervisor isolation = design rule, language-independent.
- c15 (implementation module named like the spec module): Lake 4.35 refuses ambiguous modules; product refuses reserved prefixes explicitly.
- c12 (macro rewrites `@Impl.encode` to the spec in a definition hole) proved an `[]`-returning implementation in the prototype ⇒ no definition hole; statement as `Expr`.
- c13 (build-time code inside the implementation closure rewrites generated C; attribute-free) ⇒ implementation modules run no consumer build-time code (positive allowlist).
- c7/c7b (`implemented_by`/`extern` swap passes std axioms + replay) ⇒ forbidden in implementation modules.
- A rebuilt the trusted library in 3 workspaces per check (vflab runs ≈ 2× B's) ⇒ cache by content hash. A normalized a sandbox setup failure as a kernel reject ⇒ separate statuses.

## Measures (descriptive)
- M3: equal proven scope (policy over supplied evidence); neither proves parsing, statement construction, attribution, normalization, serialization or commit. B built the statement as `Expr` in its Lean core (adopted).
- M4 (Linux x86_64, unpacked): A incremental runtime 232,574,440 B (one binary, `supportInterpreter`); B 378,807,929 B (core 231,468,408 + CPython 102,039,812 + uv 45,255,280) ⇒ B +146 MB (+38.6 %, material by the pre-registered rule). Common toolchain 3,094,361,839 B.
- M2 latency not run: by the pre-registered cost clause an eligible B overturns the cost hypothesis only without a footprint regression.
- Kernels (r8, desktop n=3, 17.4 MB honest export): Lean 12.2 s, con-leche `--verified` 9.7 s (2 jobs), NanoDa 5.2 s; forgery: all reject except NanoDa panic (rc 101 = crash, still withholds acceptance).

## Review
- consultant-1/2/3 (independent, 14 rows each): direction agree (Lean throughout + two-phase + `Expr` statement + phase-1 delivery); amendments adopted: versioned implementation profile qualified on launch implementations, one versioned verification profile incl. con-leche verified + decline/setup statuses, published-closure immutability + preview isolation + non-circular index commit, versioned schemas + receipt binding + writer/commit semantics, interface contract before the tester, two-phase library admission + proven scheduler, component coverage ledger, lifecycle authority + profile evolution, exact domains + deviation algebra, J1 absence proof.
- scientist-2 (harvest appraisal H1–H9): H7 supported (no latency claim); H1–H5 + H8 partly (grader = 16 calibrated controls, not complete soundness: `lake-manifest.json` write exemption beyond the S12 wording, K-hang ≥ 20 s total-command check does not by itself show kernel waiting; A1 defensible; J1 rebound to 8af3a11 accepted; both arms MAIN-repaired; equal proven scope — B also models the library-hash identity + carries unproven Lean parsing/`Expr` code; footprint = as-built packages, not an intrinsic language size); H6 + H9 not supported (the spikes show implementation feasibility, not proof feasibility; no categorical exclusion of the hybrid; inference bounded to these repaired artifacts) ⇒ Stack basis = MAIN's step-5 judgment (residue argument) with the revisit condition.
- advisor: adopt; steps 3 + 5 basis, cost clause, Decisions sweep, interface holes (library source override, `status`, exits, never-fetched, development + retraction, `--json` error), ABI shapes compiled on vflab before freezing, fixture library for update tests, long-lead growth prerequisites.
- fvapi session (shared host): `data/fvdep` quota; agent under a dedicated system user (same-UID processes read unit credentials + `/proc/<pid>/environ`); unit `MemoryMax` below the slice + stated schedule.
