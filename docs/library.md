# fvdep library API v1 — launch set (contract; agent-read)

Binding source = `.agent/spec.md` `Decisions` (Spec modularity, Domains + deviation algebra, C ABI, Launch set, Library layout + identity). Names + types below = public + immutable once published; definitions (bodies) + obligations = unit U4. Every version starts at 1.0.0 (the prototype library was never published).

## Naming

- Module id `<dep>.<op>` (lowercase; `_` inside `<op>`); version `x.y.z` (SemVer 2.0.0).
- Lean module `Fvdep.<Dep>.<Op>.V<x>_<y>_<z>` (UpperCamelCase of each part: `encode_url` → `EncodeUrl`); spec constant = `<Lean module>.<fn>`.
- Shared definitions = their own versioned modules (immutable once a published entry imports them).
- Reserved Lean module prefixes for consumers: `Init`, `Std`, `Lean`, `Lake`, `Fvdep`, `FvdepPreview`, `FvdepTool`.

## Operations (shape `fn` statement: `@<impl> = @<spec constant>`)

| id@version | Lean module | spec constant : type | semantics source |
|---|---|---|---|
| `base64.encode@1.0.0` | `Fvdep.Base64.Encode.V1_0_0` | `encode : List UInt8 → List Char` | RFC 4648 §4 alphabet, `=` padding |
| `base64.decode@1.0.0` | `Fvdep.Base64.Decode.V1_0_0` | `decode : List Char → Option (List UInt8)` | RFC 4648 §4 strict: alphabet only, mandatory padding, unused bits zero (§3.5 canonical) ⇒ exact inverse of `base64.encode@1.0.0` |
| `base64.encode_url@1.0.0` | `Fvdep.Base64.EncodeUrl.V1_0_0` | `encodeUrl : List UInt8 → List Char` | RFC 4648 §5 alphabet, `=` padding |
| `base64.decode_url@1.0.0` | `Fvdep.Base64.DecodeUrl.V1_0_0` | `decodeUrl : List Char → Option (List UInt8)` | RFC 4648 §5, strict as `base64.decode` |
| `semver.parse@1.0.0` | `Fvdep.Semver.Parse.V1_0_0` | `parse : List Char → Option Fvdep.Semver.Version.V1_0_0.Version` | SemVer 2.0.0 §2, §9, §10 grammar; no `v` prefix, no whitespace |
| `semver.compare@1.0.0` | `Fvdep.Semver.Compare.V1_0_0` | `compare : Version → Version → Ordering` | SemVer 2.0.0 §11 precedence; build metadata ignored |

Shared type module `Fvdep.Semver.Version.V1_0_0`: `inductive Ident | num (n : Nat) | alnum (s : List Char)`; `structure Version where major minor patch : Nat; pre : List Ident; build : List (List Char)` (deriving `DecidableEq`, `Repr`).

## C ABI shapes (shape `abi` statement: `@<impl> = Fvdep.Abi.V1_0_0.<shape> @<spec constant>`)

Module `Fvdep.Abi.V1_0_0`; whole domain, lossless (Decisions C ABI):
- `encoder : (List UInt8 → List Char) → ByteArray → ByteArray` = `fun f b => (String.ofList (f b.toList)).toUTF8` (base64 encode ops).
- `decoder : (List Char → Option (List UInt8)) → ByteArray → Option ByteArray` = `fun f b => (String.fromUTF8? b).bind fun s => (f s.toList).map fun l => ⟨l.toArray⟩` (base64 decode ops; bytes that are not UTF-8 = rejected, inside the statement).
- C side = bytes in, bytes out: (pointer, length) buffers, no other conversion outside the statement. Launch C library = base64 (encode + decode at least) with Rust, Python + Node bindings.

## Registry (how the library declares entries; fixture libraries follow it)

- Spec module `Fvdep/<Dep>/<Op>/V<x>_<y>_<z>.lean`: imports Init/Std + shared versioned modules only; defines the spec constant + obligation theorems.
- Entry module `Fvdep/Registry/<Dep>/<Op>/V<x>_<y>_<z>.lean`: imports its spec module + `Fvdep.Registry.Types`; `def entry : Fvdep.Registry.Module := { id := "base64.encode", version := "1.0.0", spec := ``Fvdep.Base64.Encode.V1_0_0.encode, obligations := [``…], abi := some ``Fvdep.Abi.V1_0_0.encoder, compat := none }` — `compat := some ("1.0.0", ``<theorem : new spec = old spec>``)` for a new version proven equal to an older one. Double-backtick names fail the library build when they dangle; typed validation checks role + type + unique id@version.
- Notices: `Fvdep/Registry/Notices.lean`: `def notices : List Fvdep.Registry.Notice := [{ id := "<id>", version := "<ver>", reason := "<text>", replacement := some "<ver>" }]` (append-only).
- Root `Fvdep/Registry.lean`: `def modules : List Fvdep.Registry.Module` + `def profiles : List Fvdep.Registry.Profile` listing every entry once (gate: each entry module listed exactly once). Profiles: same pattern under `Fvdep/Registry/Profiles/…` (fields: ecosystem, package, version, identity, operations with contract id@version, model, domain, adapters, ordered deviations (guard, behaviour, witness), proof, uncovered API) — field-level schema = U4/U10 contract.
- Launch library = one version per operation, no compat edge, no notice ⇒ tests of `upgrade`, `outdated`, `diff` + retraction build a fixture library: a git copy of the library with added versions/notices per this section, served through `FVDEP_LIBRARY_URL`.

## Profiles (launch set: re-checked → published or preview)

| profile | operations → contract | notes |
|---|---|---|
| `cpython:base64@3.14` (CPython stdlib module `base64`) | `b64encode` → `base64.encode`, `b64decode` → `base64.decode` | package identity names runtime + options (e.g. `validate`) |
| `npm:base64-js@1.5.1` | `fromByteArray` → `base64.encode`, `toByteArray` → `base64.decode` | JS strings = UTF-16 code units (adapter in the statement) |
| `crates:base64@0.22.1` | `STANDARD.encode` → `base64.encode`, `STANDARD.decode` → `base64.decode` | engine + config named in identity |
| `npm:semver@7.7.3` | `parse`/`valid` → `semver.parse`, `compare` → `semver.compare` | numbers > 2^53−1 + loose mode = deviations or out of domain |

Exact profile ids, domains + deviation lists = unit U8 (exact-relation algebra in Decisions).
