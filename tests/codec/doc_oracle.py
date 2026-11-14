"""D1–D8 reference: layouts, schema walk, typed domains + error text; no Doc implementation input."""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, Any, Callable

if TYPE_CHECKING:
    from . import oracle as o
else:
    o = sys.modules["fvdep_codec_oracle"]

COMMANDS = ["check", "list", "lock", "outdated", "scan", "status", "upgrade"]
CODES = ["profile_construct", "import_not_allowed", "reserved_module", "build_failed", "statement_mismatch",
         "graph_mismatch", "axiom", "kernel_reject", "kernel_crash", "kernel_timeout", "kernel_decline",
         "sandbox_setup", "tool_missing", "stale_receipt", "retracted", "policy_proof_required", "mismatch",
         "not_delivered", "usage", "no_project", "schema", "toolchain", "adapter", "fetch_failed", "io",
         "commit_io", "internal", "busy"]


def object_value(fields: dict[str, o.V]) -> o.V:
    return o.obj(sorted(fields.items(), key=lambda p: p[0].encode()))


def optional(value: str | None) -> o.V:
    return o.null() if value is None else o.string(value)


def utf8_size(s: str) -> int:
    return len(s.encode())


def clip(s: str) -> str:
    if utf8_size(s) <= 65_536:
        return s
    return s.encode()[:65_520].decode("utf-8", "ignore") + " [truncated]"


def commit(s: str) -> bool:
    return re.fullmatch(r"[0-9a-f]{40}", s) is not None


def digest(s: str) -> bool:
    return re.fullmatch(r"[0-9a-f]{64}", s) is not None


def utc(s: str) -> bool:
    match = re.fullmatch(r"[0-9]{4}-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})Z", s)
    if match is None:
        return False
    month, day, hour, minute, second = map(int, match.groups())
    return 1 <= month <= 12 and 1 <= day <= 31 and hour <= 23 and minute <= 59 and second <= 60


def module_syntax(s: str) -> bool:
    return re.fullmatch(r"[a-z][a-z0-9]*\.[a-z][a-z0-9]*(?:_[a-z][a-z0-9]*)*", s) is not None


def module_id(s: str) -> bool:
    return utf8_size(s) <= 65_536 and module_syntax(s)


def version_syntax(s: str) -> bool:
    return re.fullmatch(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", s) is not None


def version(s: str) -> bool:
    return utf8_size(s) <= 65_536 and version_syntax(s)


def constant(s: str) -> bool:
    return 1 <= utf8_size(s) <= 1024 and all(ord(c) >= 32 and ord(c) != 127 for c in s)


def profile(s: str) -> bool:
    return 1 <= utf8_size(s) <= 256 and re.fullmatch(r"[A-Za-z0-9._@+\-]+", s) is not None


def argv_valid(argv: tuple[str, ...]) -> bool:
    return bool(argv) and all((1 if i == 0 else 0) <= utf8_size(s) <= 65_536 and "\0" not in s for i, s in enumerate(argv))


@dataclass(frozen=True)
class Receipt:
    tag: str = "proof"
    decl_kind: str = "proof"
    module: str = "base64.encode"
    version: str = "1.0.0"
    shape: str | None = "fn"
    impl: str | None = "Impl.encode"
    proof: str | None = "Proof.encode_eq"
    argv: tuple[str, ...] | None = None
    spec: str = "a" * 64
    impl_sources: str | None = "b" * 64
    proof_sources: str | None = "c" * 64
    adapter: str | None = None
    phase1: str = "d" * 64
    solution: str = "e" * 64
    library: str = "0123456789abcdef0123456789abcdef01234567"
    profile: str = "lean4.35@v1+qualified"
    policy: str = "required"
    checked: str = "2026-02-31T23:59:60Z"


def differential(**kw: Any) -> Receipt:
    base = Receipt(tag="differential", decl_kind="differential", shape=None, impl=None, proof=None,
                   argv=("python3", "adapter.py", ""), impl_sources=None, proof_sources=None,
                   adapter="f" * 64, phase1="", solution="")
    return replace(base, **kw)


def receipt_layout(r: Receipt) -> o.V:
    return object_value({
        "checked": o.string(r.checked),
        "digests": object_value({"adapter": optional(r.adapter), "impl_sources": optional(r.impl_sources),
                                 "phase1_export": optional(r.phase1 if r.tag == "proof" else None),
                                 "proof_sources": optional(r.proof_sources),
                                 "solution_export": optional(r.solution if r.tag == "proof" else None),
                                 "spec_closure": o.string(r.spec)}),
        "evidence": o.string(r.tag), "library": o.string(r.library), "policy": o.string(r.policy),
        "request": object_value({"adapter": o.null() if r.argv is None else o.array(map(o.string, r.argv)),
                                 "impl": optional(r.impl), "module": o.string(r.module), "proof": optional(r.proof),
                                 "shape": optional(r.shape), "version": o.string(r.version)}),
        "verification_profile": o.string(r.profile),
    })


def receipt_transport(r: Receipt) -> o.V:
    assert r.tag in ("proof", "differential") and r.decl_kind in ("proof", "differential")
    assert module_syntax(r.module) and version_syntax(r.version) and commit(r.library)
    assert r.policy in ("required", "development") and r.shape in (None, "fn", "abi")
    assert r.tag == "proof" or (r.phase1 == "" and r.solution == "")
    return o.array([o.string(r.tag), o.string(r.decl_kind), o.string(r.module), o.string(r.version),
                    optional(r.shape), optional(r.impl), optional(r.proof),
                    o.null() if r.argv is None else o.array(map(o.string, r.argv)), o.string(r.spec),
                    optional(r.impl_sources), optional(r.proof_sources), optional(r.adapter),
                    o.string(r.phase1), o.string(r.solution), o.string(r.library), o.string(r.profile),
                    o.string(r.policy), o.string(r.checked)])


@dataclass(frozen=True)
class Lock:
    library: str
    entries: tuple[Receipt, ...] = ()


def lock_layout(l: Lock) -> o.V:
    return object_value({"library": o.string(l.library), "modules": o.array(map(receipt_layout, l.entries)), "schema": o.integer(1)})


def lock_transport(l: Lock) -> o.V:
    assert commit(l.library)
    return o.array([o.string(l.library), o.array(map(receipt_transport, l.entries))])


@dataclass(frozen=True)
class Envelope:
    command: int = 0
    exit: int = 0
    error: tuple[int, str] | None = None
    result: tuple[tuple[str, o.V], ...] = ()
    commit: str | None = None
    fetched: str | None = None
    fetch_error: str | None = None
    trusted: tuple[str, ...] = ()


def envelope_layout(e: Envelope) -> o.V:
    return object_value({"command": o.string(COMMANDS[e.command]),
                         "error": o.null() if e.error is None else object_value({"code": o.string(CODES[e.error[0]]), "detail": o.string(clip(e.error[1]))}),
                         "exit": o.integer(e.exit), "result": o.obj(e.result), "schema": o.integer(1),
                         "status": object_value({"commit": optional(e.commit), "fetch_error": optional(None if e.fetch_error is None else clip(e.fetch_error)), "fetched": optional(e.fetched)}),
                         "trusted": o.array(o.string(clip(s)) for s in e.trusted)})


def envelope_transport(e: Envelope) -> o.V:
    assert 0 <= e.command < 7 and e.exit in (0, 1, 2)
    assert e.error is None or 0 <= e.error[0] < 28
    assert e.commit is None or commit(e.commit)
    return o.array([o.integer(e.command), o.integer(e.exit),
                    o.null() if e.error is None else o.array([o.integer(e.error[0]), o.string(e.error[1])]),
                    o.obj(e.result), o.array([optional(e.commit), optional(e.fetched), optional(e.fetch_error)]),
                    o.array(map(o.string, e.trusted))])


@dataclass(frozen=True)
class Error:
    path: tuple[o.Segment, ...]
    kind: str
    value: o.V | None = None

    def transport(self) -> o.V:
        return o.array([path_transport(self.path), o.string(self.kind), o.array([] if self.value is None else [self.value])])

    def output(self) -> str:
        return "doc-error:" + o.wire(self.transport()).hex()


def path_transport(path: tuple[o.Segment, ...]) -> o.V:
    return o.array(o.array([o.string("index"), o.integer(p)]) if isinstance(p, int)
                   else o.array([o.string("key"), o.string(p)]) for p in path)


def pointer(path: tuple[o.Segment, ...]) -> str:
    return "".join("/" + str(p).replace("~", "~0").replace("/", "~1") for p in path)


def render(error: Error) -> str:
    pieces = [pointer(error.path), error.kind]
    if error.kind != "missing_field":
        assert error.value is not None
        b = o.canonical(error.value)
        pieces.append(b.decode() if len(b) <= 64 else {"str": "string", "arr": "array", "obj": "object"}.get(error.value.tag, error.value.tag))
    return " ".join(pieces[1:] if pieces[0] == "" else pieces)


@dataclass(frozen=True)
class Field:
    kinds: tuple[str, ...]
    predicate: Callable[[o.V], bool] = lambda _: True
    object_rule: Callable[[o.V], dict[str, Field]] | None = None
    discriminator: str | None = None
    element: Callable[[o.V, tuple[o.Segment, ...]], Error | None] | None = None
    ordering: bool = False


def text_field(check: Callable[[str], bool], nullable: bool = False, must_null: bool | None = None) -> Field:
    kinds = ("str", "null") if nullable else ("str",)
    def predicate(v: o.V) -> bool:
        if must_null is True:
            return v.tag == "null"
        if v.tag == "null":
            return must_null is not False
        return check(o.as_string(v))
    return Field(kinds, predicate)


def obj_walk(v: o.V, path: tuple[o.Segment, ...], fields: Callable[[o.V], dict[str, Field]],
             discriminator: str | None = None) -> Error | None:
    if v.tag != "obj":
        return Error(path, "wrong_type", v)
    ms = dict(v.members)
    if discriminator is not None:
        if discriminator not in ms:
            return Error((*path, discriminator), "missing_field")
        x = ms[discriminator]
        expected_kind = "int" if discriminator == "schema" else "str"
        if x.tag != expected_kind:
            return Error((*path, discriminator), "wrong_type", x)
        if (discriminator == "schema" and o.as_int(x) != 1) or (discriminator == "evidence" and o.as_string(x) not in ("proof", "differential")):
            return Error((*path, discriminator), "bad_value", x)
    schema = fields(v)
    unknown = sorted(ms.keys() - schema.keys(), key=lambda s: s.encode())
    if unknown:
        return Error((*path, unknown[0]), "unknown_field", ms[unknown[0]])
    missing = sorted(schema.keys() - ms.keys(), key=lambda s: s.encode())
    if missing:
        return Error((*path, missing[0]), "missing_field")
    for key in sorted(schema, key=lambda s: s.encode()):
        error = field_walk(ms[key], (*path, key), schema[key])
        if error is not None:
            return error
    return None


def field_walk(v: o.V, path: tuple[o.Segment, ...], rule: Field) -> Error | None:
    if v.tag not in rule.kinds:
        return Error(path, "wrong_type", v)
    if not rule.predicate(v):
        return Error(path, "bad_value", v)
    if v.tag == "obj" and rule.object_rule is not None:
        return obj_walk(v, path, rule.object_rule, rule.discriminator)
    if v.tag == "arr" and rule.element is not None:
        for i, x in enumerate(v.items):
            error = rule.element(x, (*path, i))
            if error is not None:
                return error
        if rule.ordering:
            previous: bytes | None = None
            for i, x in enumerate(v.items):
                module = o.as_string(dict(dict(x.members)["request"].members)["module"])
                current = module.encode()
                if previous is not None and current <= previous:
                    return Error((*path, i, "request", "module"), "bad_value", o.string(module))
                previous = current
    return None


def receipt_fields(v: o.V) -> dict[str, Field]:
    proof = o.as_string(dict(v.members)["evidence"]) == "proof"
    def digests(_: o.V) -> dict[str, Field]:
        return {"adapter": text_field(digest, True, proof),
                "impl_sources": text_field(digest, True, not proof),
                "phase1_export": text_field(digest, True, not proof),
                "proof_sources": text_field(digest, True, not proof),
                "solution_export": text_field(digest, True, not proof), "spec_closure": text_field(digest)}
    def arguments(x: o.V, path: tuple[o.Segment, ...]) -> Error | None:
        first = path[-1] == 0
        return field_walk(x, path, text_field(lambda s: (1 if first else 0) <= utf8_size(s) <= 65_536 and "\0" not in s))
    def request(_: o.V) -> dict[str, Field]:
        return {"adapter": Field(("arr", "null"), lambda x: x.tag == "null" if proof else x.tag == "arr" and bool(x.items), element=arguments),
                "impl": text_field(constant, True, not proof), "module": text_field(module_id),
                "proof": text_field(constant, True, not proof),
                "shape": text_field(lambda s: s in ("fn", "abi"), True, not proof), "version": text_field(version)}
    return {"checked": text_field(utc), "digests": Field(("obj",), object_rule=digests),
            "evidence": text_field(lambda s: s in ("proof", "differential")), "library": text_field(commit),
            "policy": text_field(lambda s: s in ("required", "development")),
            "request": Field(("obj",), object_rule=request), "verification_profile": text_field(profile)}


def receipt_error(v: o.V, path: tuple[o.Segment, ...] = ()) -> Error | None:
    return obj_walk(v, path, receipt_fields, "evidence")


def lock_fields(_: o.V) -> dict[str, Field]:
    return {"library": text_field(commit), "modules": Field(("arr",), element=receipt_error, ordering=True),
            "schema": Field(("int",), lambda v: o.as_int(v) == 1)}


def lock_error(v: o.V) -> Error | None:
    return obj_walk(v, (), lock_fields, "schema")


def receipt_from_layout(v: o.V) -> Receipt:
    ms = dict(v.members)
    ds, rq = dict(ms["digests"].members), dict(ms["request"].members)
    def opt(x: o.V) -> str | None:
        return None if x.tag == "null" else o.as_string(x)
    tag = o.as_string(ms["evidence"])
    return Receipt(tag=tag, decl_kind=tag, module=o.as_string(rq["module"]), version=o.as_string(rq["version"]),
                   shape=opt(rq["shape"]), impl=opt(rq["impl"]), proof=opt(rq["proof"]),
                   argv=None if rq["adapter"].tag == "null" else tuple(map(o.as_string, rq["adapter"].items)),
                   spec=o.as_string(ds["spec_closure"]), impl_sources=opt(ds["impl_sources"]),
                   proof_sources=opt(ds["proof_sources"]), adapter=opt(ds["adapter"]),
                   phase1=opt(ds["phase1_export"]) or "", solution=opt(ds["solution_export"]) or "",
                   library=o.as_string(ms["library"]), profile=o.as_string(ms["verification_profile"]),
                   policy=o.as_string(ms["policy"]), checked=o.as_string(ms["checked"]))


def receipt_wf(r: Receipt) -> bool:
    return r.tag == r.decl_kind and receipt_error(receipt_layout(r)) is None


def lock_wf(l: Lock) -> bool:
    return commit(l.library) and all(map(receipt_wf, l.entries)) and lock_error(lock_layout(l)) is None


def envelope_wf(e: Envelope) -> bool:
    value = o.obj(e.result)
    return (e.error is not None) == (e.exit == 2) and o.valid(value) and o.depth(value) <= 31 and (e.fetched is None or utc(e.fetched)) and (e.commit is None or commit(e.commit))


def decode_receipt_output(v: o.V) -> str:
    assert o.valid(v)
    error = receipt_error(v)
    return error.output() if error is not None else o.value_out(receipt_transport(receipt_from_layout(v)))


def decode_lock_value_output(v: o.V) -> str:
    assert o.valid(v)
    error = lock_error(v)
    if error is not None:
        return error.output()
    ms = dict(v.members)
    l = Lock(o.as_string(ms["library"]), tuple(map(receipt_from_layout, ms["modules"].items)))
    return o.value_out(lock_transport(l))


def decode_lock_output(b: bytes) -> str:
    decoded = o.decode(b)
    if decoded.kind != "ok":
        return "lock-text:" + decoded.output()
    assert decoded.value is not None
    return decode_lock_value_output(decoded.value)
