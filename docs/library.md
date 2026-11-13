# fvdep library API v1 — launch set (contract; agent-read)

Binding source = `.agent/spec.md` `Decisions` (Spec modularity, Domains + deviation algebra, C ABI, Launch set, Library layout + identity, Profile shape). Names + types below = public + immutable once published; definitions (bodies) + obligations = unit U4. Every version starts at 1.0.0 (the prototype library was never published).

## Naming

- Module id `<dep>.<op>`: `<dep>` = `[a-z][a-z0-9]*`; `<op>` = one or more `_`-joined segments, each `[a-z][a-z0-9]*` (a segment starts with a letter, so the Lean module name below determines the id); entry version `x.y.z` = three decimal numbers without leading zeros (no pre-release or build part), ordered numerically by field.
- Lean module `Fvdep.<Dep>.<Op>.V<x>_<y>_<z>` (UpperCamelCase of each part: `encode_url` → `EncodeUrl`); spec constant = `<Lean module>.<fn>`.
- Shared definitions = their own versioned modules (immutable once a published entry imports them).
- Reserved consumer module names: the first name component is `Init`, `Std`, `Lean` or `Lake`, or starts with `Fvdep` (fvdep's libraries + tool: `Fvdep`, `FvdepPreview`, `FvdepProofs`, `FvdepCore`, `FvdepIO`, …).

## Operations (shape `fn` statement: `@<impl> = @<spec constant>`)

| id@version | Lean module | spec constant : type | semantics source |
|---|---|---|---|
| `base64.encode@1.0.0` | `Fvdep.Base64.Encode.V1_0_0` | `encode : List UInt8 → List Char` | RFC 4648 §4 alphabet, `=` padding |
| `base64.decode@1.0.0` | `Fvdep.Base64.Decode.V1_0_0` | `decode : List Char → Option (List UInt8)` | RFC 4648 §4 strict: alphabet only, mandatory padding, unused bits zero (§3.5 canonical) ⇒ exact inverse of `base64.encode@1.0.0` |
| `base64.encode_url@1.0.0` | `Fvdep.Base64.EncodeUrl.V1_0_0` | `encodeUrl : List UInt8 → List Char` | RFC 4648 §5 alphabet, `=` padding |
| `base64.decode_url@1.0.0` | `Fvdep.Base64.DecodeUrl.V1_0_0` | `decodeUrl : List Char → Option (List UInt8)` | RFC 4648 §5, strict as `base64.decode` |
| `semver.parse@1.0.0` | `Fvdep.Semver.Parse.V1_0_0` | `parse : List Char → Option Fvdep.Semver.Version.V1_0_0.Version` | SemVer 2.0.0 §2, §9, §10 grammar; no `v` prefix, no whitespace |
| `semver.compare@1.0.0` | `Fvdep.Semver.Compare.V1_0_0` | `compare : Version → Version → Ordering` | SemVer 2.0.0 §11 precedence, extended to the whole type (below) |

Shared type module `Fvdep.Semver.Version.V1_0_0`: `inductive Ident | num (n : Nat) | alnum (s : List Char)`; `structure Version where major minor patch : Nat; pre : List Ident; build : List (List Char)` (deriving `DecidableEq`, `Repr`).

- `parse` returns only valid values: `num n` for an identifier of digits alone (no leading zero unless `0`), `alnum s` for one holding a non-digit (`[0-9A-Za-z-]+`), build identifiers nonempty over `[0-9A-Za-z-]`.
- `compare` is total over the whole type, valid or not: `major`, `minor`, `patch` numerically, in that order; then `pre`: empty > nonempty; two nonempty lists element by element (`num` vs `num` numerically, `alnum` vs `alnum` lexicographically by code point, `num` < `alnum`), a list that is a proper prefix of the other is lower; `build` ignored. Obligations: `compare a b = (compare b a).swap`; transitivity; `compare a b = .eq ↔ {a with build := []} = {b with build := []}` (a total preorder; versions differing in build metadata alone compare `.eq`).

## C ABI shapes (shape `abi` statement: `@<impl> = Fvdep.Abi.V1_0_0.<shape> @<spec constant>`)

Module `Fvdep.Abi.V1_0_0`; whole domain, lossless (Decisions C ABI):
- `encoder : (List UInt8 → List Char) → ByteArray → ByteArray` = `fun f b => (String.ofList (f b.toList)).toUTF8` (base64 encode ops).
- `decoder : (List Char → Option (List UInt8)) → ByteArray → Option ByteArray` = `fun f b => (String.fromUTF8? b).bind fun s => (f s.toList).map fun l => ⟨l.toArray⟩` (base64 decode ops; bytes that are not UTF-8 = rejected, inside the statement).
- C side = bytes in, bytes out: (pointer, length) buffers, no other conversion outside the statement. Launch C library = base64 (encode + decode at least) with Rust, Python + Node bindings.

## Registry (how the library declares entries; fixture libraries follow it)

Phase-aware: everything an entry's identity covers builds in phase 1 under the implementation profile; proofs are phase 2 (any Lean) and never part of the identity.

- Registry types module `Fvdep.Registry.Types.V1` (versioned; immutable once a published entry imports it; a change = `V2` beside it).
- Spec module `Fvdep/<Dep>/<Op>/V<x>_<y>_<z>.lean` (phase 1): imports Init/Std + shared versioned modules only; defines the spec constant + each obligation as a named proposition `def <name> : Prop := …`.
- Entry module `Fvdep/Registry/<Dep>/<Op>/V<x>_<y>_<z>.lean` (phase 1): imports its spec module + `Fvdep.Registry.Types.V1`; `def entry : Fvdep.Registry.Types.V1.Module := { id := "base64.encode", version := "1.0.0", spec := ``Fvdep.Base64.Encode.V1_0_0.encode, obligations := [``…], abi := some ``Fvdep.Abi.V1_0_0.encoder, compat := none }`; `compat := some "1.0.0"` declares the new spec equal to that older version (fvdep builds the statement `new spec = old spec`). Double-backtick names fail the library build when they dangle; typed validation checks role + type + unique id@version.
- Proof registry module `FvdepProofs/Registry/<Dep>/<Op>/V<x>_<y>_<z>.lean` (phase 2, lean_lib `FvdepProofs`, never imported by `Fvdep`): `def proofs : Fvdep.Registry.Types.V1.Proofs := { obligations := [(``<obligation>, ``<theorem>)…], compat := none | some ``<theorem> }`; each theorem's type must equal the statement fvdep builds (the obligation constant itself; for compat `new spec = old spec`), judged under the verification profile. Obligation status = derived from the judged proofs (`#print axioms`), never written.
- Identity of a published entry = SHA-256 of the framed source closure of its entry module inside the library (entry module + spec module + shared versioned modules + registry types), proofs + proof registry excluded. Adding an unrelated entry changes no identity; changing any byte in the closure does.
- Notices: `Fvdep/Registry/Notices.lean`: `def notices : List Fvdep.Registry.Types.V1.Notice := [{ id := "<id>", version := "<ver>", reason := "<text>", replacement := some "<ver>" }]` (append-only).
- Removed entries: `Fvdep/Registry/Removed.lean`: `def removed : List Fvdep.Registry.Types.V1.Removed := [{ id, version, kind, digest, toolchain, lastCommit }]` (append-only; an entry leaves the tree only through a toolchain bump it fails, with a notice; `lastCommit` = the last commit holding it; its full metadata = the index at `lastCommit`).
- Root `Fvdep/Registry.lean`: `def modules : List Fvdep.Registry.Types.V1.Module` + `def profiles : List Fvdep.Registry.Types.V1.Profile` listing every entry once (gate: each entry module listed exactly once). Profiles: same pattern under `Fvdep/Registry/Profiles/…` + `FvdepProofs/Registry/Profiles/…` (fields: profile id, entry version, identity facts (artifact, runtime, options), operations each with package operation name + contract id@version + model + domain + adapters + ordered deviations (name, guard, behaviour, witness), uncovered package API names) — field-level schema = U10 contract.
- `index.json` = a pure function of the library tree (registry + notices + removed): per entry id, version, kind (operation | profile), area (published | preview; profiles), digest, toolchain, obligations + status, compat edges, notices; a removed entry = id, version, kind, digest, toolchain, `lastCommit` alone. Gate: the committed bytes = regenerated; every identity listed by the index at HEAD and at each of HEAD's parents stays listed with an equal digest (a shallow clone fails the check).
- Launch library = one version per operation, no compat edge, no notice ⇒ tests of `upgrade`, `outdated`, `diff` + retraction build a fixture library: a git copy of the library with added versions/notices per this section, served through `FVDEP_LIBRARY_URL`.

## Profiles (launch set: re-checked → published or preview)

- Profile id = `<eco>:<pkg>@<pkgver>[#<variant>]`: the package's own version string (exact match, never ordered; `#` appears in no supported ecosystem's versions) + an optional variant `[a-z0-9-]+` naming one configuration where a package version needs several; entry versions `x.y.z` per (area, profile id) (a revision = a new entry version, never an edit).
- Identity facts (artifact, runtime, options) are part of the entry; per-call options (e.g. Python `validate=True`) = distinct operations.
- Area: the published profile (`Fvdep`) lists its proven operations alone, each `published`; unproven operations of the same profile id sit in a preview entry (`FvdepPreview`), each `preview`; at the latest versions an operation sits in one area alone; promotion = a new published version adding the operation + a new preview version without it (an empty preview leaves the area); `list` + `show` print the area + each operation's status.
- Deviation witness: inside the declared domain, inside its own guard, outside every earlier guard, behaviour ≠ contract there (kernel-checked).

| profile | operations → contract | notes |
|---|---|---|
| `cpython:base64@3.14` (CPython stdlib module `base64`) | `b64encode` → `base64.encode`, `b64decode` → `base64.decode` | identity names runtime + options (e.g. `validate`) |
| `npm:base64-js@1.5.1` | `fromByteArray` → `base64.encode`, `toByteArray` → `base64.decode` | JS strings = UTF-16 code units (adapter in the statement) |
| `crates:base64@0.22.1` | `STANDARD.encode` → `base64.encode`, `STANDARD.decode` → `base64.decode` | engine + config named in identity |
| `npm:semver@7.7.3` | `parse`/`valid` → `semver.parse`, `compare` → `semver.compare` | numbers > 2^53−1 + loose mode = deviations or out of domain |

Exact operation names, domains, deviation lists + the typed exact relation (model, domain, guards, behaviours, input/output adapters incl. partial conversions) = the U10 contract (algebra in Decisions); acceptance tests of profile statements + `profile --check` wait for it.
