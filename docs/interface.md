# fvdep public interface v1 (contract; agent-read)

Binding source = `.agent/spec.md` `Decisions` (Public interface, Data formats, Lifecycle, Conformance method). Quoted output strings = exact UI copy; `<…>` = a value; `[…]` = optional. Tests pin behaviour through this file + `Decisions`; wording outside quoted strings is free.

## 1 Invocation

- `fvdep <command> [args]`. `fvdep --version` → stdout `fvdep <version>`, exit 0. `fvdep help [<command>]`, `fvdep --help`, `fvdep <command> --help` → usage on stdout, exit 0. No command, unknown command, unknown option, missing or extra argument → usage on stderr, exit 2, no effect.
- Project = nearest ancestor of the working directory holding `fvdep.toml`, or `--project <dir>`. A command needing a project outside one → stderr `No fvdep.toml found. Run "fvdep init" in your project directory.`, exit 2.
- Library snapshot = the full commit in `fvdep.toml` `[library] commit`. fvdep fetches + builds that commit in its own cache (never the project's `.lake/packages` copy). A consumer Lean package that requires `fvdep` at another commit → exit 2 naming both commits.
- Library source = environment variable `FVDEP_LIBRARY_URL` (any git remote or local repository path; default `https://github.com/veriformatics/fvdep`). It serves the pinned snapshot + the lifecycle feed (the source's `main` head). Tests + offline use point it at a local repository.
- One fvdep version checks library snapshots of one Lean toolchain (its verification profile). A snapshot pinning another toolchain → stderr `Library commit <sha> uses Lean <x>; this fvdep checks Lean <y>. Install the matching fvdep or change the library pin.`, exit 2.
- stdout = results; stderr = progress + diagnostics. `--json` (where listed) replaces stdout with one JSON document (§6); stderr unchanged.

## 2 Exit codes (every command)

- 0 = the command did what was asked + every requested module meets the saved policy (report commands: the report completed).
- 1 = a negative result: NOT PROVEN, MISMATCH, MODEL DIFFERS, a policy failure (MATCHED or retracted under proof policy, stale receipt), an admission refusal.
- 2 = the command could not run as asked: usage, missing project/library/module, unknown schema/field, setup or sandbox failure, tool or kernel binary missing or mismatched, fetch failure, I/O failure.
- Several modules: highest code wins (2 > 1 > 0).
- Exit 1 or 2 ⇒ `fvdep.toml` + `fvdep.lock` stay byte-identical (only fvdep's own cache may change).

## 3 Commands

| command | effect | output (stdout) | exit |
|---|---|---|---|
| `init [--development]` | creates `fvdep.toml` (`schema = 1`, `[library] commit` = this tool's library commit, `[policy] proof = "required"`, or `"development"` with the flag), no modules | `Created fvdep.toml (proof required)` / `(development: test evidence accepted, never delivered)` | 0; file exists → 2, unchanged |
| `list [--previews] [--json]` | none | one line per library operation at its latest version: `<id>@<ver>  <proven>/<total> obligations proven`; then per published profile `<eco>:<pkg>@<ver>  published  <n> operations`; `--previews` adds preview profiles labelled `preview` | 0 |
| `show <id>[@<ver>] \| <eco>:<pkg>[@<ver>] [--json]` | none | module: versions, statement, obligations + status, compat edges, notices; profile: package identity (artifact, runtime, options), domain, operations + status, deviations, package API it does not cover | 0; unknown → 2 |
| `check [<id>…] [--json]` | read-only (caches excepted); rechecks the modules + compares each result with its `fvdep.lock` entry | one verdict block per requested module (§4), default = every manifest module | §2 |
| `status [--json]` | read-only, no rebuild: compares `fvdep.toml`, `fvdep.lock`, the current input digests + the status snapshot | per manifest module `DELIVERED <id>@<ver> <impl>` or `NOT DELIVERED <id>@<ver>: <reason>`, reason ∈ `no lock entry`, `lock entry is stale (<what changed>)`, `fvdep.lock and fvdep.toml disagree (<what>)`, `retracted (<reason>); replacement <ver>\|no replacement`, `test evidence only`, `the proof was checked under an older verification profile` | 0 all delivered (development policy: all meet it); else 1/2 |
| `lock [--json]` | checks every manifest module; all meet the policy → writes `fvdep.lock` | verdict blocks, then `Wrote fvdep.lock (<n> modules)` | 0; else 1/2 + lock untouched |
| `upgrade <id> [--to <ver>] [--json]` | checks `<id>` at the target (default: latest non-retracted), proof transported through a proven compat theorem where one exists; meets the policy → writes lock, then manifest | verdict block, then `Upgraded <id> from <old> to <new>` | 0; else 1/2 + both files untouched |
| `fetch` | refreshes the lifecycle status snapshot from the feed | `Fetched library status at <commit> (<UTC time>)` | 0; failure → stderr `Fetch failed: <reason>. Last successful fetch: <UTC time>\|never.`, 2 |
| `outdated [--json]` | fetches as `fetch`, then reports per manifest module | `<id>  <pinned> → <latest>  <compat>` with `<compat>` ∈ `same behaviour (proven)`, `compatibility not stated`, `major version: prove again`, or `<id>  <pinned>  up to date`; retraction lines (§4); last line `Status as of <UTC time> (<commit>)` | 0; failed fetch → report from the last snapshot (or the pinned snapshot: `Status as of library commit <sha> (never fetched)`), `Fetch failed …` on stderr, 2 |
| `diff <id> <from> <to>` | none | statement change + compat classification | 0; unknown → 2 |
| `scan [<dir>] [--json]` | none; reads lock files (`pnpm-lock.yaml`, `package-lock.json`, `Cargo.lock`, `uv.lock`, `lake-manifest.json`) | per dependency: `<eco>:<pkg>@<resolved>  direct\|indirect  covered\|preview\|not covered[  suggestion: <eco>:<pkg>@<other>][  assumes: <configuration>]`; unresolved ranges `<eco>:<pkg> <range>  unresolved`. `covered` = a published profile for the exact resolved version whose configuration matches everything the lock file records; configuration the lock file does not record is printed after `assumes:` | 0; no lock file → 2; lock file outside the supported format subset → 2 naming it |
| `profile <eco>:<pkg>@<ver> --check [--json]` | runs model vs real package differentially (development evidence) | `MODEL MATCHES <eco>:<pkg>@<ver> (<n> inputs)` / `MODEL DIFFERS <eco>:<pkg>@<ver> <op>: input <x>: package <got>, model <want>` | 0 / 1 / 2 |
| `build-lib <id> [--out <dir>]` | needs a current delivered receipt of shape `abi`; builds the C library + header from the frozen phase-1 outputs | `Built <path> for <id>@<ver> (<abi shape>)` | 0; else 1/2 |
| `brief <id>[@<ver>]` | none | implementer brief: statement, implementation profile rules, proof freedom, manifest entry, check command | 0; unknown → 2 |
| `trust [--json]` | none | verification profile (toolchain, kernels + modes + digests, axioms, implementation profile version) + trusted residue with reasons | 0 |
| `admit <dir> [--base <rev>] [--json]` | library admission of a library working copy (maintainers, growth); writes nothing | per entry `ADMITTED <entry>` / `PREVIEW <entry>: <missing proofs>` / `REFUSED <entry>: <reason>` | 0 (admitted or preview) / 1 / 2 |
| `index [--check]` | regenerates `index.json` from the registry; `--check` compares instead | `Wrote index.json (<n> entries)` / `index.json is current` / `index.json differs from the registry` | 0 / 1 (`--check` differs) / 2 |

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
- After the last block: `Trusted base: <list>` when any line 1 is PROVEN; `C-ABI delivery also trusts: <shim>, <binding>` when a delivered module has shape `abi`; `Status as of <UTC time> (<commit>)`, or `Status as of library commit <sha> (never fetched)` before the first successful fetch (status = the pinned snapshot's own notices).
- `<reason>` names the failing step + its object, e.g. `implementation uses run_cmd (Impl.lean:12)`, `kernel nanoda rejected the proof`, `kernel con-leche timed out after <s> s`, `the proof depends on axiom <name>`, `the proof does not prove the required statement`, `the implementation changed between phases`, `proof build failed`.
- Delivered (derived, never stored) = PROVEN under the current verification profile with a receipt matching the current inputs ∧ not retracted in the status snapshot.

## 5 Policy

- `fvdep.toml` `[policy] proof = "required"` (default; absent key = required): only delivered modules meet the policy. `"development"`: MATCHED + a retracted PROVEN also meet it, both labelled not delivered; NOT PROVEN + MISMATCH never do.
- `lock`, `upgrade` + growth follow the saved policy; no flag overrides it.

## 6 `--json` (schema 1)

One object: `{"schema":1,"command":<str>,"exit":<0|1|2>,"error":null|{"code":<code>,"detail":<str>},"results":[<result>…],"trusted":[<str>…],"status":{"commit":<str|null>,"fetched":<UTC str|null>,"fetch_error":<str|null>}}`; `error` = the exit-2 cause that stopped the command (usage, project, schema, setup, fetch), `results` then holds what completed. `<result>` = `{"module":<id>,"version":<str>,"impl":<str|null>,"evidence":"proof"|"differential","verdict":"proven"|"not_proven"|"matched"|"mismatch","delivered":<bool>,"retracted":null|{"reason":<str>,"replacement":<str|null>},"reasons":[{"code":<code>,"detail":<str>}…],"receipt":<object|null>}`. Codes: `profile_construct`, `import_not_allowed`, `reserved_module`, `build_failed`, `statement_mismatch`, `graph_mismatch`, `axiom`, `kernel_reject`, `kernel_crash`, `kernel_timeout`, `kernel_decline`, `sandbox_setup`, `tool_missing`, `stale_receipt`, `retracted`, `policy_proof_required`, `mismatch`, `usage`, `no_project`, `schema`, `library_pin`, `toolchain`, `fetch_failed`, `io`. Keys sorted; codec profile per `Decisions` Data formats.

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

Unknown key, duplicate key, missing required key, unknown `schema` → exit 2 naming it.

## 8 Adapter protocol v1 (differential checks + package profiles)

- The adapter = a program reading JSON request lines on stdin, writing one JSON reply line per request on stdout. Request `{"op":<str>,"args":[<value>…]}`; reply `{"ok":<value>}` | `{"err":<str>}` (input rejected) | `{"unsupported":true}`. Bytes = lowercase hex strings; text = JSON strings; integers within ±(2^53−1), larger ones as decimal strings. The spec oracle (built from the library) speaks the same protocol.
