# fvdep public interface v1 (contract; agent-read)

Binding source = `.agent/spec.md` `Decisions` (Public interface, Data formats, Lifecycle, Conformance method). Quoted output strings = exact UI copy; `<…>` = a value; `[…]` = optional. Tests pin behaviour through this file + `Decisions`; wording outside quoted strings is free.

## 1 Invocation

- `fvdep <command> [args]`. `fvdep --version` → stdout `fvdep <version>`, exit 0. `fvdep help [<command>]`, `fvdep --help`, `fvdep <command> --help` → usage on stdout, exit 0. No command, unknown command, unknown option, missing or extra argument → usage on stderr, exit 2, no effect.
- Project = nearest ancestor of the working directory holding `fvdep.toml`, or `--project <dir>`. Commands needing a project: `check`, `status`, `lock`, `upgrade`, `outdated`, `build-lib`. Outside one → stderr `No fvdep.toml found. Run "fvdep init" in your project directory.`, exit 2.
- Library snapshot = the full commit in `fvdep.toml` `[library] commit`. fvdep fetches + builds that commit in its own cache, never the project's `.lake/packages` copy, so a consumer Lean package requiring `fvdep` at another commit cannot change a verdict: stderr `Your Lake package requires fvdep at <x>; fvdep checks <y>. Update the requirement to <y>.`, exit unchanged.
- Library source = environment variable `FVDEP_LIBRARY_URL` (any git remote or local repository path; default `https://github.com/veriformatics/fvdep`). It serves the pinned snapshot + the lifecycle feed (the source's `main` head). Tests + offline use point it at a local repository.
- fvdep's own state = `FVDEP_CACHE` (default `$XDG_CACHE_HOME/fvdep`, else `~/.cache/fvdep`): library snapshots + builds, per-source lifecycle status snapshots (observed retractions never disappear from it). Tests point it at a temporary directory.
- Library-reading commands without a project (`list`, `show`, `diff`, `brief`, `oracle`, `scan`, `profile`) read the project's snapshot inside a project, else the source's `main` head (fetched into fvdep's cache; unreachable source → the last fetched head; none → `Fetch failed …` (§3 `fetch`), exit 2). `trust` reads no library; `admit` + `index` act on a library working copy.
- One fvdep version checks library snapshots of one Lean toolchain (its verification profile). A snapshot pinning another toolchain → stderr `Library commit <sha> uses Lean <x>; this fvdep checks Lean <y>. Install the matching fvdep or change the library pin.`, exit 2.
- stdout = results; stderr = progress + diagnostics. `--json` (where listed) replaces stdout with one JSON document (§6); stderr unchanged.

## 2 Exit codes (every command)

- 0 = the command did what was asked + every requested module meets the saved policy (§5; report commands: the report completed).
- 1 = a negative result: NOT PROVEN, MISMATCH, MODEL DIFFERS, a policy failure (MATCHED or retracted under proof policy; for `status`, a module not delivered), an admission refusal.
- 2 = the command could not run as asked: usage, missing project/library/module, unknown schema/field, setup or sandbox failure, tool or kernel binary missing or mismatched, adapter failure, fetch failure, I/O failure.
- Several modules: highest code wins (2 > 1 > 0).
- Commit step = the writes after every check + policy decision: `init` creates `fvdep.toml`; `lock` replaces `fvdep.lock`; `upgrade` replaces `fvdep.lock`, then `fvdep.toml` (each file: temp + fsync + rename + directory fsync). Exit 1, and exit 2 raised before the commit step ⇒ `fvdep.toml` + `fvdep.lock` stay byte-identical (only fvdep's own cache may change). A failure inside the commit step → exit 2, stderr `Could not finish writing <file>: <reason>. Run "fvdep status" to see the state.`; each file then holds its old or its new content (durability unknown); where the two files disagree, `status` + `check` report it and no module is delivered until a later `lock` or `upgrade` succeeds.

## 3 Commands

| command | effect | output (stdout) | exit |
|---|---|---|---|
| `init [--development]` | creates `fvdep.toml` (`schema = 1`, `[library] commit` = the library source's `main` head, fetched now; `[policy] proof = "required"`, or `"development"` with the flag), no modules | `Created fvdep.toml (proof required)` / `(development: test evidence accepted, never delivered)` | 0; file exists → 2, unchanged; head on another toolchain → 2 (§1 message), nothing written |
| `list [--previews] [--json]` | none | one line per library operation at its latest version: `<id>@<ver>  <proven>/<total> obligations proven`; then per published profile `<profile>  published  <n> operations`; `--previews` adds preview profiles labelled `preview` with their operation count | 0 |
| `show <id>[@<ver>] \| <profile>[@<ver>]` | none | module: versions, statement, obligations + status, compat edges, notices; profile: package identity (artifact, runtime, options), domain, operations each with its status (published / preview), deviations, package API it does not cover | 0; unknown → 2 |
| `check [<id>…] [--json]` | read-only (caches excepted); rechecks the modules + compares each result with its `fvdep.lock` entry | one verdict block per requested module (§4), default = every manifest module | §2, from the fresh results alone: the lock comparison never changes the exit |
| `status [--json]` | read-only, no rebuild: compares `fvdep.toml`, `fvdep.lock`, the current input digests + the status snapshot | per manifest module `DELIVERED <id>@<ver> <impl>` or `NOT DELIVERED <id>@<ver>: <reason>`, reason ∈ `no lock entry`, `lock entry is stale (<what changed>)`, `fvdep.lock and fvdep.toml disagree (<what>)`, `retracted (<reason>); replacement <ver>\|no replacement`, `test evidence only`, `the proof was checked under an older verification profile` | 0 all delivered (development policy: all meet it); else 1/2 |
| `lock [--json]` | checks every manifest module; all meet the policy → writes `fvdep.lock` | verdict blocks, then `Wrote fvdep.lock (<n> modules)` | 0; else 1/2 + lock untouched (§2 commit step) |
| `upgrade <id> [--to <ver>] [--json]` | target = `--to`, else the latest non-retracted version at the library source's `main` head; a target outside the pinned snapshot moves `[library] commit` to that head (another toolchain → 2, §1 message) + rechecks every manifest module there; the proof of `<id>` transported through a proven compat theorem where one exists; all meet the policy → writes lock, then manifest | one verdict block per manifest module, then `Upgraded <id> from <old> to <new>`, + ` (library commit <old 12 hex> → <new 12 hex>)` when the pin moved | 0; else 1/2 + both files untouched (§2 commit step) |
| `fetch` | refreshes the lifecycle status snapshot from the feed | `Fetched library status at <commit> (<UTC time>)` | 0; failure → stderr `Fetch failed: <reason>. Last successful fetch: <UTC time>\|never.`, 2 |
| `outdated [--json]` | fetches as `fetch`, then reports per manifest module | `<id>  <pinned> → <latest>  <compat>` with `<compat>` ∈ `same behaviour (proven)`, `compatibility not stated`, `major version: prove again`, or `<id>  <pinned>  up to date`; retraction lines (§4); last line `Status as of <UTC time> (<commit>)` | 0; failed fetch → report from the last snapshot (or the pinned snapshot: `Status as of library commit <sha> (never fetched)`), `Fetch failed …` on stderr, 2 |
| `diff <id> <from> <to>` | none | statement change + compat classification | 0; unknown → 2 |
| `scan [<dir>] [--json]` | none; reads lock files (`pnpm-lock.yaml`, `package-lock.json`, `Cargo.lock`, `uv.lock`, `lake-manifest.json`) | per dependency: `<eco>:<pkg>@<resolved>  direct\|indirect  covered <k>/<n> operations\|conditional <k>/<n> operations  assumes: <configuration>\|preview\|not covered[  suggestion: <profile>]`; unresolved ranges `<eco>:<pkg> <range>  unresolved`. `covered` = a published profile for the exact resolved version whose every configuration fact the lock file records + matches; `conditional` = the same, but some facts are not recorded (printed after `assumes:`; never counted as covered); a recorded fact that differs ⇒ not covered; `<k>` = the profile's proven operations, `<n>` = `<k>` + the package API items it lists as not covered | 0; no lock file → 2; lock file outside the supported format subset → 2 naming it |
| `profile <profile>[@<ver>] --check` | runs model vs real package differentially over adapter protocol v1 (development evidence) | `MODEL MATCHES <profile> (<n> inputs)` / `MODEL DIFFERS <profile> <op>: input <x>: package <got>, model <want>` | 0 / 1 / 2 |
| `build-lib <id> [--out <dir>]` | needs `status` DELIVERED for `<id>` (shape `abi`); builds the C library + header from the receipt's phase-1 outputs (fvdep's cache, else rebuilt in a fresh sandbox; export digest ≠ the receipt's → 1, `the implementation changed`); writes them + the build record `fvdep-build.json` to `--out` (default `fvdep-build/`); `fvdep.toml` + `fvdep.lock` untouched | `Built <path> for <id>@<ver> (<abi shape>)`, then `C-ABI delivery also trusts: <C shim>, your binding glue` | 0; else 1/2 |
| `brief <id>[@<ver>]` | none | implementer brief: statement, implementation profile rules, proof freedom, manifest entry, check command | 0; unknown → 2 |
| `trust` | none | verification profile (toolchain, kernels + modes + digests, axioms, implementation profile version) + trusted residue with reasons | 0 |
| `admit <dir> [--base <rev>]` | library admission of a library working copy (maintainers, growth); writes nothing | per entry `ADMITTED <entry>` / `PREVIEW <entry>: <missing proofs>` / `REFUSED <entry>: <reason>` | 0 (admitted or preview) / 1 / 2 |
| `oracle <id>@<ver> \| <profile>@<ver>` | serves the spec (or the profile's model) over adapter protocol v1 (§8) on stdin/stdout | replies only, one line per request | 0 at end of input; unknown target → 2 |
| `index [--check]` | regenerates `index.json` from the library tree (registry + removed-entry records); `--check` compares instead | `Wrote index.json (<n> entries)` / `index.json is current` / `index.json differs from the library` | 0 / 1 (`--check` differs) / 2 |

`<profile>` = `<eco>:<pkg>@<pkgver>[#<variant>]` (`docs/library.md` Profiles); `[@<ver>]` after it = the profile's own entry version.

## 4 Verdict block (check, lock, upgrade)

- Line 1 = one of:
  - `PROVEN <id>@<ver> <impl>`
  - `NOT PROVEN <id>@<ver>: <reason>`
  - `MATCHED <id>@<ver> <impl> (test evidence, not delivered)`
  - `MISMATCH <id>@<ver> <impl>: input <x>: implementation <got>, spec <want>`
- Then zero or more detail lines, each indented two spaces:
  - `  not delivered: retracted (<reason>); replacement <ver>` / `…; no replacement` — a retracted module keeps its verdict; it is never delivered.
  - `  not delivered: proof required by fvdep.toml` — MATCHED under proof policy.
  - `  fvdep.lock: current` / `  fvdep.lock: out of date (<what changed>); run "fvdep lock"` / `  fvdep.lock: no entry` — check only, when `fvdep.lock` exists.
- After the last block: `Trusted base: <list>` when any line 1 is PROVEN; `Status as of <UTC time> (<commit>)`, or `Status as of library commit <sha> (never fetched)` before the first successful fetch (status = the pinned snapshot's own notices).
- `<reason>` names the failing step + its object, e.g. `implementation uses run_cmd (Impl.lean:12)`, `kernel nanoda rejected the proof`, `kernel con-leche timed out after <s> s`, `the proof depends on axiom <name>`, `the proof does not prove the required statement`, `the implementation changed between phases`, `proof build failed (Proof.lean:7: <first Lean error line>)`.
- Delivered (derived, never stored; `status`) = PROVEN under the current verification profile with a lock receipt matching the current inputs ∧ not retracted in the status snapshot. `check`, `lock` + `upgrade` judge the fresh result; C-library delivery = `build-lib`.

## 5 Policy

- `fvdep.toml` `[policy] proof = "required"` (default; absent key = required): `check`, `lock` + `upgrade` accept a module whose fresh verdict is PROVEN + not retracted; `status` accepts a DELIVERED module. `"development"`: MATCHED + a retracted PROVEN also meet it, both labelled not delivered; NOT PROVEN + MISMATCH never do (a proof entry never falls back to differential evidence).
- `lock`, `upgrade` + growth follow the saved policy; no flag overrides it.

## 6 `--json` (schema 1)

- Envelope (every `--json` command): `{"schema":1,"command":<str>,"exit":<0|1|2>,"error":null|{"code":<code>,"detail":<str>},"result":<result>,"trusted":[<str>…],"status":{"commit":<str|null>,"fetched":<UTC str|null>,"fetch_error":<str|null>}}`; `error` = the exit-2 cause that stopped the command, `result` then holds what completed. Keys sorted; codec profile per `Decisions` Data formats.
- `<result>` per command:
  - `check`, `lock`, `upgrade`: `{"modules":[<module>…],"wrote":[<file>…],"library":null|{"from":<commit>,"to":<commit>}}` (`library` = `upgrade` moving the pin).
  - `<module>` = `{"module":<id>,"version":<str>,"impl":<str|null>,"evidence":"proof"|"differential","verdict":"proven"|"not_proven"|"matched"|"mismatch","policy_met":<bool>,"retracted":null|{"reason":<str>,"replacement":<str|null>},"reasons":[{"code":<code>,"detail":<str>}…],"lock":null|"current"|"out_of_date"|"no_entry","receipt":null|<receipt>}`; `lock` = `check` with a `fvdep.lock` present, else null.
  - `<receipt>` = `{"checked":<UTC str>,"digests":{"adapter":<hex|null>,"impl_sources":<hex|null>,"phase1_export":<hex|null>,"proof_sources":<hex|null>,"solution_export":<hex|null>,"spec_closure":<hex>},"evidence":"proof"|"differential","library":<commit>,"policy":"required"|"development","request":{"adapter":[<str>…]|null,"impl":<str|null>,"module":<id>,"proof":<str|null>,"shape":"fn"|"abi"|null,"version":<str>},"verification_profile":<str>}` (`fvdep.lock` stores the same object per module). Proof evidence: every digest but `adapter` set; differential evidence: `spec_closure` + `adapter` (SHA-256 over the argv + the bytes of each argv element naming a file under the project) set, the rest null.
  - Build record `fvdep-build.json` (`build-lib`) = `{"built":<UTC str>,"header":<hex>,"library":<hex>,"module":<id>,"receipt":<hex: SHA-256 of the receipt's canonical JSON>,"schema":1,"shape":<abi shape>,"shim":<str>,"verification_profile":<str>,"version":<str>}`.
  - `status`: `{"modules":[{"module":<id>,"version":<str>,"impl":<str|null>,"delivered":<bool>,"reason":null|{"code":<code>,"detail":<str>}}…]}`.
  - `list`: `{"operations":[{"id":<id>,"version":<str>,"obligations":{"proven":<n>,"total":<n>}}…],"profiles":[{"id":<profile>,"version":<str>,"area":"published"|"preview","operations":[{"name":<str>,"contract":<id@ver>,"status":"published"|"preview"}…]}…]}`.
  - `outdated`: `{"modules":[{"module":<id>,"pinned":<str>,"latest":<str>,"compat":"same_behaviour"|"not_stated"|"major"|"up_to_date","retracted":null|{"reason":<str>,"replacement":<str|null>}}…]}`.
  - `scan`: `{"dependencies":[{"ecosystem":<str>,"package":<str>,"resolved":<str|null>,"range":<str|null>,"scope":"direct"|"indirect","coverage":"covered"|"conditional"|"preview"|"not_covered"|"unresolved","operations":null|{"proven":<k>,"total":<n>},"suggestions":[<profile>…],"assumes":[<str>…],"lockfile":<path>}…]}`.
- Codes: `profile_construct`, `import_not_allowed`, `reserved_module`, `build_failed`, `statement_mismatch`, `graph_mismatch`, `axiom`, `kernel_reject`, `kernel_crash`, `kernel_timeout`, `kernel_decline`, `sandbox_setup`, `tool_missing`, `stale_receipt`, `retracted`, `policy_proof_required`, `mismatch`, `not_delivered`, `usage`, `no_project`, `schema`, `toolchain`, `adapter`, `fetch_failed`, `io`, `commit_io`.
- Text only in v1: `show`, `profile`, `trust`, `admit`, `fvdep-grow` (`.agent/deferred.md`).

## 7 `fvdep.toml` schema 1

```toml
schema = 1

[library]
commit = "<40 hex>"

[policy]
proof = "required"            # or "development"

[modules."base64.encode"]
version = "1.0.0"
shape = "fn"                  # "fn" | "abi"
impl_modules = ["Impl"]       # implementation modules (Lean), checked against the implementation profile
proof_modules = ["Proof"]     # proof modules (any Lean)
impl = "Impl.encode"          # implementation constant
proof = "Proof.encode_eq"     # proof constant: proves the statement fvdep builds

[modules."base64.decode"]
version = "1.0.0"
evidence = "differential"     # development evidence: adapter speaks §8
adapter = ["python3", "impl/decode.py"]
```

- Top level: `schema` (= 1), `[library] commit` (40 lowercase hex), optional `[policy] proof`, `[modules."<id>"]` tables (zero or more; `<id>` = a library operation id).
- Proof entry: `version`, `shape`, `impl_modules`, `proof_modules`, `impl`, `proof`, all required. Differential entry: `version`, `evidence = "differential"`, `adapter`, all required; proof-entry keys forbidden there.
- Module lists: nonempty, no repeats, no module in both lists; module `A.B` = file `A/B.lean` under the project directory; reserved prefixes (`docs/library.md` Naming) refused. `adapter` = nonempty argv, run from the project directory.
- Unknown key, duplicate key, missing required key, forbidden key, wrong type, unknown `schema` → exit 2 naming it.

## 8 Adapter protocol v1 (differential checks + package profiles)

- The adapter = a program reading JSON request lines on stdin, writing one JSON reply line per request on stdout. Request `{"op":<str>,"args":[<value>…]}`; reply `{"ok":<value>}` | `{"err":<str>}` (input rejected; the text is never compared) | `{"unsupported":true}` | `{"invalid":<str>}` (the request itself is malformed: bad JSON, unknown op, wrong arity, a value outside its encoding). The spec oracle (`fvdep oracle`) speaks the same protocol, answers `invalid` + continues with the next line.
- `op` = the spec function name (`encode`, `decode`, `encodeUrl`, `decodeUrl`, `parse`, `compare`) for a spec target; the package operation name (`docs/library.md` Profiles) for a profile target.
- Values by type: bytes (`List UInt8`, `ByteArray`) = lowercase hex string, even length; text (`List Char`) = JSON string of Unicode scalar values (an escaped lone surrogate = invalid); UTF-16 text (JavaScript strings in a profile) = array of code units 0–65535; `Nat`/`Int` = JSON integer within ±(2^53−1), beyond it a canonical decimal string (digits without leading zeros, `-` for negative `Int`; a string inside the range = invalid); `Option α`: `none` = reply `err`, `some x` = reply `ok` with `x`; `Ordering` = `"lt"` | `"eq"` | `"gt"`; `Version` = `{"build":[<str>…],"major":<nat>,"minor":<nat>,"patch":<nat>,"pre":[{"num":<nat>}|{"alnum":<str>}…]}` (identifiers tagged: `num` + `alnum` never share an encoding).
- Differential runs compare `ok` values exactly, `err` against `err` (any text), and skip `unsupported`. An adapter that crashes, prints a non-JSON line, misses or adds a reply, or answers `invalid` → exit 2 naming the adapter + the input; an operation whose every request was `unsupported` → exit 2 (never MATCHED). Domain bound = the codec limits (strings ≤ 64 KiB); larger inputs are outside differential evidence.

## 9 Growth job `fvdep-grow` (vflab; `docs` for operators)

- `fvdep-grow next`: read-only; the target the next run would pick + why (user queue first, then the ranking snapshot), each skipped candidate with its reason (attempted, in progress, backoff, budget, not eligible).
- `fvdep-grow run`: one scheduler step: reserve budget → one attempt (pre-staged inputs → staging copy → drafting agent → `fvdep admit`) → record + settle budget; prints `ATTEMPT <eco>:<pkg>@<ver> <result>` with result ∈ `drafted`, `refused: <reason>`, `admitted-unpublished`, or `NOTHING TO DO: <reason>`. Exit 0 = attempt recorded (any result) or nothing to do; 2 = infrastructure (agent service or login unavailable included).
- `fvdep-grow queue add <eco>:<pkg>[@<ver>]`, `fvdep-grow queue list`: the user queue.
- `fvdep-grow status`: today's budget (used/total), recent attempts + results, admitted-unpublished entries, oldest pending admission age.
- State directory `FVDEP_GROWTH_STATE` (default `/srv/data/fvdep/growth`); ranking snapshot file + daily budget in its `config.toml`; agent command `FVDEP_AGENT` (default `claude -p`; tests use a stub agent).
