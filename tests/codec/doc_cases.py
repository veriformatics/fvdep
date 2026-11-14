"""Batch-2 cases from D1–D8; J/H builders and their PRNG stream stay untouched."""

from __future__ import annotations

import json
import random
import sys
from dataclasses import replace
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from . import doc_oracle as d
    from . import oracle as o
    from .suite import Suite
else:
    o = sys.modules["fvdep_codec_oracle"]
    d = sys.modules["fvdep_codec_doc_oracle"]


def at(v: o.V, path: tuple[o.Segment, ...]) -> o.V:
    for p in path:
        v = v.items[p] if isinstance(p, int) else dict(v.members)[p]
    return v


def update(v: o.V, path: tuple[o.Segment, ...], value: o.V | None) -> o.V:
    if not path:
        assert value is not None
        return value
    key, *rest = path
    if isinstance(key, int):
        xs = list(v.items)
        if rest:
            xs[key] = update(xs[key], tuple(rest), value)
        elif value is None:
            del xs[key]
        else:
            xs[key] = value
        return o.array(xs)
    ms = dict(v.members)
    if rest:
        ms[key] = update(ms[key], tuple(rest), value)
    elif value is None:
        del ms[key]
    else:
        ms[key] = value
    return d.object_value(ms)


def add(s: Suite, id: str, op: str, value: o.V, expected: str, clauses: tuple[str, ...], method: str = "example") -> None:
    if op in ("D.receipt.decode", "D.lock.decodeValue"):
        assert o.valid(value), id + ": value-level decoder domain"
    s.add(id, op, o.wire(value), expected, clauses, method)


def receipt_decode(s: Suite, id: str, value: o.V, clauses: tuple[str, ...],
                   error: tuple[tuple[o.Segment, ...], str] | None = None,
                   method: str = "example", wrapped: bool = True) -> None:
    assert o.valid(value), id + ": value-level decoder domain"
    expected = d.decode_receipt_output(value)
    if error is not None:
        actual = d.receipt_error(value)
        assert actual is not None and (actual.path, actual.kind) == error, (id, actual, error)
    add(s, id + ".value", "D.receipt.decode", value, expected, clauses, method)
    if wrapped:
        lock = d.object_value({"library": o.string(d.Receipt().library), "modules": o.array([value]), "schema": o.integer(1)})
        b = o.canonical(lock)
        s.add(id + ".lock", "D.lock.decode", b, d.decode_lock_output(b), clauses, method)


def receipt_cases(s: Suite, id: str, r: d.Receipt, clauses: tuple[str, ...] = (), method: str = "example") -> None:
    assert d.receipt_wf(r), id
    raw, layout = d.receipt_transport(r), d.receipt_layout(r)
    assert o.valid(layout)
    add(s, id + ".encode", "D.receipt.encode", raw, o.value_out(layout), (*clauses, "D3-layout"), method)
    add(s, id + ".wf", "D.receipt.wf", raw, o.value_out(o.boolean(True)), (*clauses, "D8-checks"), method)
    add(s, id + ".roundtrip", "D.receipt.roundtrip", raw, o.value_out(raw), (*clauses, "D3-roundtrip"), method)
    add(s, id + ".valid", "D.receipt.valid", raw, o.value_out(layout), (*clauses, "D7-valid"), method)
    receipt_decode(s, id + ".decode", layout, (*clauses, "D3-roundtrip"), method=method, wrapped=False)


def lock_cases(s: Suite, id: str, l: d.Lock, method: str = "example") -> None:
    assert d.lock_wf(l), id
    raw, layout = d.lock_transport(l), d.lock_layout(l)
    assert o.valid(layout)
    add(s, id + ".encode", "D.lock.encode", raw, "bytes:" + o.canonical(layout).hex(), ("D4-lock-layout",), method)
    add(s, id + ".value", "D.lock.value", raw, o.value_out(layout), ("D4-lock-layout",), method)
    add(s, id + ".wf", "D.lock.wf", raw, o.value_out(o.boolean(True)), ("D8-checks",), method)
    add(s, id + ".roundtrip", "D.lock.roundtrip", raw, o.value_out(raw), ("D4-lock-roundtrip",), method)
    add(s, id + ".valid", "D.lock.valid", raw, o.value_out(layout), ("D7-valid",), method)
    b = b" \r\n" + o.canonical(layout) + b"\t "
    s.add(id + ".decode", "D.lock.decode", b, o.value_out(raw), ("D4-lock-roundtrip",), method)


def envelope_cases(s: Suite, id: str, e: d.Envelope, method: str = "example") -> None:
    raw, layout = d.envelope_transport(e), d.envelope_layout(e)
    add(s, id + ".encode", "D.envelope.encode", raw, o.value_out(layout), ("D6-envelope-layout",), method)
    add(s, id + ".wf", "D.envelope.wf", raw, o.value_out(o.boolean(d.envelope_wf(e))), ("D6-wellformed", "D8-checks"), method)
    if d.envelope_wf(e):
        assert o.valid(layout)
        add(s, id + ".valid", "D.envelope.valid", raw, o.value_out(layout), ("D7-valid",), method)


def bytes_text(size: int, char: str, prefix: str = "") -> str:
    b = prefix.encode()
    assert len(b) <= size
    width = len(char.encode())
    return prefix + char * ((size - len(b)) // width) + "a" * ((size - len(b)) % width)


def random_text(rng: random.Random, n: int = 16) -> str:
    parts: list[str] = []
    for _ in range(rng.randrange(n + 1)):
        if rng.randrange(3):
            parts.append(rng.choice(["a", "é", "中", "😀", "\0", "\n", "/", "~", '"', "\\", "\x7f", "￿"]))
        else:
            cp = rng.randrange(0x110000 - 0x800)
            parts.append(chr(cp if cp < 0xD800 else cp + 0x800))
    return "".join(parts)


def random_value(rng: random.Random, fuel: int = 3) -> o.V:
    tag = rng.randrange(6 if fuel else 4)
    if tag == 0:
        return o.null()
    if tag == 1:
        return o.boolean(bool(rng.randrange(2)))
    if tag == 2:
        return o.integer(rng.randint(-o.MAX_INT, o.MAX_INT))
    if tag == 3:
        return o.string(random_text(rng))
    if tag == 4:
        return o.array(random_value(rng, fuel - 1) for _ in range(rng.randrange(5)))
    return d.object_value({random_text(rng, 6): random_value(rng, fuel - 1) for _ in range(rng.randrange(5))})


def random_receipt(rng: random.Random, i: int) -> d.Receipt:
    r = d.Receipt() if rng.randrange(2) else d.differential()
    digits = "0123456789abcdef"
    n = lambda k: "".join(rng.choice(digits) for _ in range(k))
    argv = ((random_text(rng).replace("\0", "") or "x"), random_text(rng).replace("\0", ""), "", random_text(rng).replace("\0", "")) if r.tag == "differential" else None
    safe_constant = lambda: "".join(c for c in random_text(rng) if ord(c) >= 32 and ord(c) != 127) or "X"
    return replace(r, module=f"p{i}.op_{rng.choice(['read', 'write', 'encode'])}",
                   impl=safe_constant() if r.tag == "proof" else None,
                   proof=safe_constant() if r.tag == "proof" else None,
                   version=f"{rng.getrandbits(rng.randrange(129))}.{rng.randrange(10000)}.{rng.randrange(10000)}",
                   shape=rng.choice(["fn", "abi"]) if r.tag == "proof" else None,
                   argv=argv, spec=n(64), impl_sources=n(64) if r.tag == "proof" else None,
                   proof_sources=n(64) if r.tag == "proof" else None, adapter=n(64) if r.tag == "differential" else None,
                   phase1=n(64) if r.tag == "proof" else "", solution=n(64) if r.tag == "proof" else "",
                   library=n(40), profile="".join(rng.choice("AaZz09._@+-") for _ in range(rng.randrange(1, 257))),
                   policy=rng.choice(["required", "development"]),
                   checked=f"{rng.randrange(10000):04}-{rng.randrange(1,13):02}-{rng.randrange(1,32):02}T{rng.randrange(24):02}:{rng.randrange(60):02}:{rng.randrange(61):02}Z")


def add_clips(s: Suite, rng: random.Random) -> None:
    for name, text in [("empty", ""), ("nul", "\0"), ("marker-content", " [truncated]"), ("mixed", 'é😀\0\n"\\')]:
        add(s, "D.clip." + name, "D.clip", o.string(text), o.value_out(o.string(d.clip(text))), ("D1-clip",))
    for width, char in [(1, "a"), (2, "é"), (3, "中"), (4, "😀")]:
        for size in [65_535, 65_536, 65_537]:
            for offset in range(width):
                text = bytes_text(size, char, "x" * offset)
                expected = d.clip(text)
                assert len(expected.encode()) <= 65_536
                add(s, f"D.clip.bound.{width}.{size}.{offset}", "D.clip", o.string(text), o.value_out(o.string(expected)), ("D1-clip",))
    for i in range(48):
        size = rng.choice([rng.randrange(65_580), 65_536 + rng.randrange(-5, 10)])
        char = rng.choice(["a", "é", "中", "😀", "\0", "￿"])
        text = bytes_text(size, char, "x" * rng.randrange(4)) if size >= 4 else "a" * size
        expected = d.clip(text)
        assert len(expected.encode()) <= 65_536
        assert expected == text if len(text.encode()) <= 65_536 else expected.endswith(" [truncated]")
        add(s, f"D.clip.gen.{i:03}", "D.clip", o.string(text), o.value_out(o.string(expected)), ("D1-clip",), "property(seed)")


def add_field_examples(s: Suite) -> None:
    proof, diff = d.receipt_layout(d.Receipt()), d.receipt_layout(d.differential())
    for name, n, base, path in [("commit", 40, proof, ("library",)), ("spec", 64, proof, ("digests", "spec_closure")),
                                ("adapter", 64, diff, ("digests", "adapter"))]:
        for i, text in enumerate(["", "a" * (n - 1), "a" * (n + 1), "A" * n, "g" + "0" * (n - 1), "0" * (n - 1) + "\0", "é" * (n // 2), " " + "0" * (n - 1)]):
            receipt_decode(s, f"D.syntax.hex.{name}.{i}", update(base, path, o.string(text)), ("D2-commit-digest",), (path, "bad_value"))
    valid_times = ["0000-01-01T00:00:00Z", "9999-12-31T23:59:60Z", "2025-02-31T00:00:00Z", "2026-04-31T12:30:59Z"]
    for i, text in enumerate(valid_times):
        receipt_cases(s, f"D.utc.valid.{i}", replace(d.Receipt(), checked=text), ("D2-utc",))
    bad_times = ["", "2026-00-01T00:00:00Z", "2026-13-01T00:00:00Z", "2026-01-00T00:00:00Z",
                 "2026-01-32T00:00:00Z", "2026-01-01T24:00:00Z", "2026-01-01T00:60:00Z",
                 "2026-01-01T00:00:61Z", "2026-1-01T00:00:00Z", "2026/01/01T00:00:00Z",
                 "2026-01-01t00:00:00Z", "2026-01-01T00:00:00z", "2026-01-01T00:00:00+00:00",
                 "2026-01-01T00:00:00.0Z", "２０２６-01-01T00:00:00Z", "2026-01-01T00:00:00Z\0"]
    for i, text in enumerate(bad_times):
        receipt_decode(s, f"D.utc.invalid.{i}", update(proof, ("checked",), o.string(text)), ("D2-utc",), (("checked",), "bad_value"))
    for name, path, spellings in [
        ("id", ("request", "module"), ["", "A.b", "a.B", "a.1b", "a.b__c", "a.b_1c", "a..b", "a", "a.b@1.0.0", "é.b", "a.b-c"]),
        ("version", ("request", "version"), ["", "01.0.0", "1.00.0", "1.0.00", "1.0", "1.0.0.0", "v1.2.3", "-1.0.0", "1.0.0-pre", "+1.0.0", "١.0.0"]),
    ]:
        for i, text in enumerate(spellings):
            receipt_decode(s, f"D.syntax.{name}.{i}", update(proof, path, o.string(text)), ("D2-id-version",), (path, "bad_value"))
    for field in ["impl", "proof"]:
        path = ("request", field)
        for i, text in enumerate(["", "a" * 1025, "é" * 512 + "a", *["X" + chr(cp) for cp in [*range(32), 127]]]):
            receipt_decode(s, f"D.constant.invalid.{field}.{i:02}", update(proof, path, o.string(text)), ("D2-constant-profile",), (path, "bad_value"))
        for i, text in enumerate(["x", "a" * 1024, "é" * 512, "a /~.😀", "\u0085", "￿"]):
            r = replace(d.Receipt(), impl=text) if field == "impl" else replace(d.Receipt(), proof=text)
            receipt_cases(s, f"D.constant.valid.{field}.{i}", r, ("D2-constant-profile",))
    for i, text in enumerate(["", "a" * 257, "a b", "x/y", "x:y", "é", "x\0", "x\x7f"]):
        receipt_decode(s, f"D.profile.invalid.{i}", update(proof, ("verification_profile",), o.string(text)),
                       ("D2-constant-profile",), (("verification_profile",), "bad_value"))
    for i, text in enumerate(["a", "@", "+-._", "A" * 256, "aZ09._@+-"]):
        receipt_cases(s, f"D.profile.valid.{i}", replace(d.Receipt(), profile=text), ("D2-constant-profile",))
    argv_cases: list[tuple[str, tuple[str, ...], tuple[o.Segment, ...] | None]] = [
        ("empty-array", (), ("request", "adapter")), ("empty-program", ("",), ("request", "adapter", 0)),
        ("nul-program", ("x\0",), ("request", "adapter", 0)),
        ("nul-later", ("python3", "x\0"), ("request", "adapter", 1)),
        ("later-empty", ("python3", ""), None), ("later-controls", ("python3", "\n\t\x7f"), None),
        ("all-non-nul-controls", ("x", "".join(chr(cp) for cp in [*range(1, 32), 127])), None),
        ("unicode-program", ("é😀", ""), None), ("repeat", ("x", "x", "x"), None),
    ]
    for name, argv, error_path in argv_cases:
        r = replace(d.differential(), argv=argv)
        if error_path is None:
            receipt_cases(s, "D.argv." + name, r, ("D2-argv", "D3-decl-argv"))
        else:
            receipt_decode(s, "D.argv." + name, d.receipt_layout(r), ("D2-argv",), (error_path, "bad_value"))
    for index in [0, 1]:
        for i, x in enumerate([o.null(), o.boolean(False), o.integer(0), o.array([]), o.obj([])]):
            value = update(diff, ("request", "adapter"), o.array([x] if index == 0 else [o.string("python3"), x]))
            receipt_decode(s, f"D.argv.kind.{index}.{i}", value, ("D2-argv", "D5-types-values"), (("request", "adapter", index), "wrong_type"))


def add_boundaries(s: Suite) -> None:
    for size in [65_536, 65_537]:
        id_text = "a" * (size - 2) + ".b"
        version_text = "1" + "0" * (size - 5) + ".0.0"
        for name, r in [("id", replace(d.Receipt(), module=id_text)), ("version", replace(d.Receipt(), version=version_text))]:
            raw = d.receipt_transport(r)
            add(s, f"D.bound.{name}.{size}.wf", "D.receipt.wf", raw,
                o.value_out(o.boolean(size <= 65_536)), ("D2-id-version", "D8-checks"))
            if size == 65_536:
                receipt_decode(s, f"D.bound.{name}.{size}.decode", d.receipt_layout(r), ("D2-id-version",), wrapped=False)
            else:
                l = d.Lock(r.library, (r,))
                b = o.canonical(d.lock_layout(l))
                s.add(f"D.bound.{name}.{size}.text", "D.lock.decode", b, d.decode_lock_output(b), ("D2-id-version", "D5-text"))
    for position in [0, 1]:
        for size in [65_536, 65_537]:
            arg = bytes_text(size, "😀", "x")
            argv = (arg,) if position == 0 else ("python3", arg)
            r = replace(d.differential(), argv=argv)
            add(s, f"D.bound.argv.{position}.{size}.wf", "D.receipt.wf", d.receipt_transport(r),
                o.value_out(o.boolean(size <= 65_536)), ("D2-argv", "D8-checks"))
            if size == 65_536:
                receipt_decode(s, f"D.bound.argv.{position}.{size}.decode", d.receipt_layout(r), ("D2-argv",), wrapped=False)
            else:
                b = o.canonical(d.lock_layout(d.Lock(r.library, (r,))))
                s.add(f"D.bound.argv.{position}.{size}.text", "D.lock.decode", b, d.decode_lock_output(b), ("D2-argv", "D5-text"))


def add_schema_cases(s: Suite) -> None:
    leaves = [(k,) for k in ["checked", "digests", "evidence", "library", "policy", "request", "verification_profile"]]
    leaves += [("digests", k) for k in ["adapter", "impl_sources", "phase1_export", "proof_sources", "solution_export", "spec_closure"]]
    leaves += [("request", k) for k in ["adapter", "impl", "module", "proof", "shape", "version"]]
    kinds = [o.null(), o.boolean(False), o.integer(5), o.string("bad"), o.array([]), o.obj([])]
    for tag, r in [("proof", d.Receipt()), ("diff", d.differential())]:
        base = d.receipt_layout(r)
        for i, path in enumerate(leaves):
            for j, value in enumerate(kinds):
                receipt_decode(s, f"D.kinds.{tag}.{i:02}.{j}", update(base, path, value), ("D5-types-values",))
            receipt_decode(s, f"D.missing.{tag}.{i:02}", update(base, path, None),
                           ("D5-unknown-missing",), (path, "missing_field"))
        for i, parent in enumerate([(), ("digests",), ("request",)]):
            value = update(base, (*parent, "x/y~z"), o.integer(9))
            receipt_decode(s, f"D.unknown.{tag}.{i}", value, ("D5-unknown-missing", "D5-pointer"), ((*parent, "x/y~z"), "unknown_field"))
        nullness = [("digests", k) for k in ["adapter", "impl_sources", "phase1_export", "proof_sources", "solution_export"]]
        nullness += [("request", k) for k in ["adapter", "impl", "proof", "shape"]]
        for i, path in enumerate(nullness):
            old = at(base, path)
            value = o.null() if old.tag != "null" else (o.array([o.string("x")]) if path == ("request", "adapter") else o.string("f" * 64 if path[0] == "digests" else "fn"))
            receipt_decode(s, f"D.nullness.{tag}.{i}", update(base, path, value), ("D3-nullness",), (path, "bad_value"))
    for i, value in enumerate(kinds[:-1]):
        receipt_decode(s, f"D.receipt.root.{i}", value, ("D5-root-discriminator",), ((), "wrong_type"), wrapped=False)
    lock = d.lock_layout(d.Lock(d.Receipt().library))
    for i, value in enumerate(kinds[:-1]):
        add(s, f"D.lock.root.{i}", "D.lock.decodeValue", value, d.decode_lock_value_output(value), ("D5-root-discriminator",))
    for i, value in enumerate([None, o.integer(0), o.integer(2), o.string("1"), o.null(), o.boolean(True)]):
        v = update(lock, ("schema",), value)
        add(s, f"D.schema.{i}", "D.lock.decodeValue", v, d.decode_lock_value_output(v), ("D5-root-discriminator",))
    for i, value in enumerate([None, o.integer(1), o.string("Proof"), o.string("other"), o.null(), o.boolean(True)]):
        receipt_decode(s, f"D.evidence.{i}", update(d.receipt_layout(d.Receipt()), ("evidence",), value), ("D5-root-discriminator",))
    for i, key in enumerate(["library", "modules"]):
        v = update(lock, (key,), None)
        add(s, f"D.lock.missing.{i}", "D.lock.decodeValue", v, d.decode_lock_value_output(v), ("D5-unknown-missing",))
    for key in ["", "~", "/", "😀", "￿"]:
        v = update(lock, (key,), o.integer(0))
        id = "D.lock.unknown." + key.encode().hex()
        add(s, id, "D.lock.decodeValue", v, d.decode_lock_value_output(v), ("D5-unknown-missing", "D5-pointer"))


def add_precedence(s: Suite) -> None:
    r = d.receipt_layout(d.Receipt())
    l = d.lock_layout(d.Lock(d.Receipt().library, (d.Receipt(),)))
    variants: list[tuple[str, o.V]] = [
        ("schema-missing-first", update(update(l, ("schema",), None), ("/unknown",), o.integer(0))),
        ("schema-kind-first", update(update(l, ("schema",), o.string("1")), ("/unknown",), o.integer(0))),
        ("schema-value-first", update(update(l, ("schema",), o.integer(2)), ("/unknown",), o.integer(0))),
        ("unknown-before-missing", update(update(l, ("library",), None), ("zz",), o.integer(0))),
        ("unknown-byte-order", update(update(l, ("~",), o.integer(1)), ("/",), o.integer(2))),
        ("root-missing-before-child", update(update(l, ("library",), None), ("modules", 0, "checked"), o.integer(0))),
        ("root-values-key-order", update(update(l, ("library",), o.string("bad")), ("modules", 0, "evidence"), o.integer(0))),
        ("receipt-disc-first", update(update(l, ("modules", 0, "evidence"), o.integer(0)), ("modules", 0, "a"), o.integer(0))),
        ("receipt-unknown-before-missing", update(update(l, ("modules", 0, "checked"), None), ("modules", 0, "zz"), o.integer(0))),
        ("receipt-missing-before-child", update(update(l, ("modules", 0, "checked"), None), ("modules", 0, "digests", "zz"), o.integer(0))),
        ("nested-unknown-before-missing", update(update(l, ("modules", 0, "digests", "adapter"), None), ("modules", 0, "digests", "zz"), o.integer(0))),
        ("nested-values-key-order", update(update(l, ("modules", 0, "digests", "impl_sources"), o.string("bad")), ("modules", 0, "digests", "spec_closure"), o.string("bad"))),
        ("values-before-later-object", update(update(l, ("modules", 0, "digests", "spec_closure"), o.string("bad")), ("modules", 0, "request", "a"), o.integer(0))),
    ]
    for name, value in variants:
        assert o.valid(value)
        expected = d.decode_lock_value_output(value)
        add(s, "D.precedence." + name, "D.lock.decodeValue", value, expected, ("D5-precedence",))
    # Array ordering is checked only after all elements' recursive schema checks.
    entries = (replace(d.Receipt(), module="z.z"), replace(d.Receipt(), module="a.a"), replace(d.Receipt(), module="b.b"))
    bad = d.lock_layout(d.Lock(d.Receipt().library, entries))
    later_error = update(bad, ("modules", 2, "checked"), o.string("bad"))
    error = d.lock_error(later_error)
    assert error is not None and error.path == ("modules", 2, "checked")
    add(s, "D.precedence.elements-before-order", "D.lock.decodeValue", later_error,
        d.decode_lock_value_output(later_error), ("D5-precedence", "D4-order"))
    for name, ordered_entries in [("unsorted", entries), ("repeat", (entries[1], replace(entries[1], version="2.0.0"))),
                                  ("first-offense", (entries[0], entries[1], entries[1]))]:
        value = d.lock_layout(d.Lock(d.Receipt().library, ordered_entries))
        error = d.lock_error(value)
        assert error is not None and error.path == ("modules", 1, "request", "module")
        add(s, "D.order." + name, "D.lock.decodeValue", value, d.decode_lock_value_output(value), ("D4-order",))
    array_bad = update(d.object_value({"library": o.string(d.Receipt().library), "modules": o.array([r, r]), "schema": o.integer(1)}),
                       ("modules", 1, "evidence"), o.integer(0))
    array_bad = update(array_bad, ("modules", 0, "zz"), o.integer(0))
    add(s, "D.precedence.array-index", "D.lock.decodeValue", array_bad, d.decode_lock_value_output(array_bad), ("D5-precedence",))


def add_text_and_render(s: Suite, rng: random.Random) -> None:
    examples = [b"", b"x", b'{"schema":1}x', b"x" + b"[" * 33, b'"' + b"[" * 33,
                b'{"schema":1,"schema":1}', b'{"schema":1,"x":{"a":1,"a":2}}',
                b'{"schema":1,"~x/y":0,"~x/y":1}', b'"' + b"a" * 65_537 + b'"',
                b'"' + b"a" * 65_537 + b'"x', b"\xef\xbb\xbf{}", b'"\xff"']
    for i, b in enumerate(examples):
        expected = d.decode_lock_output(b)
        s.add(f"D.text.{i:02}", "D.lock.decode", b, expected, ("D5-text",))
        decoded = o.decode(b)
        if decoded.kind != "ok":
            text = {"malformed": "malformed", "tooLarge": "too_large"}.get(decoded.kind)
            if decoded.kind == "duplicate":
                assert decoded.site is not None
                path, key = decoded.site
                text = "duplicate_key " + d.pointer((*path, key))
            assert text is not None
            s.add(f"D.text.render.{i:02}", "D.lock.render", b, o.value_out(o.string(text)), ("D5-render", "D5-pointer"))
    paths: list[tuple[o.Segment, ...]] = [(), ("",), ("a/b", "m~n", 2), ("~01", "/~", 0), ("\0é😀", 2**64), (0,), ("0",)]
    paths.extend(tuple(rng.choice([random_text(rng), rng.randrange(1000)]) for _ in range(rng.randrange(8))) for _ in range(64))
    for i, path in enumerate(paths):
        add(s, f"D.pointer.{i:03}", "D.pointer", d.path_transport(path), o.value_out(o.string(d.pointer(path))), ("D5-pointer",), "example" if i < 7 else "property(seed)")
    values = [o.null(), o.boolean(False), o.integer(-o.MAX_INT), o.string("x"), o.string("a" * 62),
              o.string("a" * 63), o.string("é" * 31), o.string("é" * 31 + "a"),
              o.string("\0" * 10), o.string("\0" * 11), o.array([o.integer(0)] * 31),
              o.array([o.integer(0)] * 32), o.array([o.integer(0)] * 30 + [o.integer(10)]),
              d.object_value({"a": o.string("x" * 56)}),
              d.object_value({"a": o.string("x" * 57)})]
    for kind in ["missing_field", "unknown_field", "wrong_type", "bad_value"]:
        for i, value in enumerate(values if kind != "missing_field" else [None]):
            for root in [True, False]:
                error = d.Error(() if root else ("modules", 1, "a/b~"), kind, value)
                add(s, f"D.render.{kind}.{i:02}.{int(root)}", "D.error.render", error.transport(),
                    o.value_out(o.string(d.render(error))), ("D5-render", "D5-pointer"))
    assert d.render(d.Error((), "wrong_type", o.integer(5))) == "wrong_type 5"
    for i in range(64):
        kind = rng.choice(["missing_field", "unknown_field", "wrong_type", "bad_value"])
        path = tuple(rng.choice([random_text(rng), rng.randrange(1000)]) for _ in range(rng.randrange(6)))
        error = d.Error(path, kind, None if kind == "missing_field" else random_value(rng))
        add(s, f"D.render.gen.{i:03}", "D.error.render", error.transport(),
            o.value_out(o.string(d.render(error))), ("D5-render", "D5-pointer"), "property(seed)")
    for i, value in enumerate([o.integer(5), d.object_value({"schema": o.integer(2)}),
                               d.object_value({"schema": o.integer(1)}),
                               d.object_value({"schema": o.integer(1), "library": o.integer(0), "modules": o.array([])}),
                               d.object_value({"schema": o.integer(1), "~/": o.string("value")})]):
        error = d.lock_error(value)
        assert error is not None
        s.add(f"D.doc.render.{i}", "D.lock.render", o.canonical(value), o.value_out(o.string(d.render(error))),
              ("D5-render", "D5-pointer"))


def add_envelopes(s: Suite, rng: random.Random) -> None:
    for i, command in enumerate(d.COMMANDS):
        add(s, f"D.command.{i}", "D.command", o.integer(i), o.value_out(o.string(command)), ("D6-codes",))
    for i, code in enumerate(d.CODES):
        add(s, f"D.code.{i:02}", "D.code", o.integer(i), o.value_out(o.string(code)), ("D6-codes",))
        envelope_cases(s, f"D.envelope.code.{i:02}", d.Envelope(command=i % 7, exit=2, error=(i, "cause")))
    for i in range(64):
        ci, pi = rng.randrange(7), rng.randrange(28)
        add(s, f"D.command.gen.{i:03}", "D.command", o.integer(ci), o.value_out(o.string(d.COMMANDS[ci])), ("D6-codes",), "property(seed)")
        add(s, f"D.code.gen.{i:03}", "D.code", o.integer(pi), o.value_out(o.string(d.CODES[pi])), ("D6-codes",), "property(seed)")
    for exit in range(3):
        for present in [False, True]:
            e = d.Envelope(exit=exit, error=(20, "cause") if present else None)
            envelope_cases(s, f"D.envelope.error-law.{exit}.{int(present)}", e)
    for result_depth in [1, 30, 31, 32]:
        child = o.null()
        for _ in range(result_depth - 1):
            child = o.array([child])
        e = d.Envelope(result=(("x", child),))
        assert o.depth(o.obj(e.result)) == result_depth
        envelope_cases(s, f"D.envelope.depth.{result_depth}", e)
    for key_size in [65_536, 65_537]:
        envelope_cases(s, f"D.envelope.result-key.{key_size}", d.Envelope(result=(("a" * key_size, o.null()),)))
    extremes = d.object_value({"max": o.integer(o.MAX_INT), "min": o.integer(-o.MAX_INT), "text": o.string("x" * 65_536)})
    envelope_cases(s, "D.envelope.result-extremes", d.Envelope(result=extremes.members))
    for i in range(24):
        depth = rng.randrange(1, 37)
        child = o.null()
        for _ in range(depth - 1):
            child = o.array([child])
        e = d.Envelope(result=(("x", child),))
        add(s, f"D.envelope.depth.gen.{i:03}", "D.envelope.wf", d.envelope_transport(e),
            o.value_out(o.boolean(depth <= 31)), ("D6-wellformed", "D8-checks"), "property(seed)")
    for name, result in [("unsorted", (("z", o.null()), ("a", o.null()))),
                         ("repeat", (("a", o.integer(1)), ("a", o.integer(2)))),
                         ("integer", (("x", o.integer(2**53)),)),
                         ("string", (("x", o.string("x" * 65_537)),))]:
        envelope_cases(s, "D.envelope.invalid-result." + name, d.Envelope(result=result))
    for i, fetched in enumerate([None, "", "2026-02-31T23:59:60Z", "2026-13-01T00:00:00Z", "0000-01-01T00:00:00Z"]):
        envelope_cases(s, f"D.envelope.fetched.{i}", d.Envelope(fetched=fetched))
    for size in [65_535, 65_536, 65_537]:
        for width, char in [(1, "a"), (2, "é"), (3, "中"), (4, "😀")]:
            text = bytes_text(size, char, "x")
            e = d.Envelope(exit=2, error=(27, text), fetch_error=text, trusted=(text, "", "keep"))
            envelope_cases(s, f"D.envelope.clip.{size}.{width}", e)
    for i in range(48):
        exit = rng.randrange(3)
        result = d.object_value({f"k{j}": random_value(rng) for j in range(rng.randrange(6))})
        e = d.Envelope(command=rng.randrange(7), exit=exit,
                       error=(rng.randrange(28), random_text(rng)) if exit == 2 else None,
                       result=result.members, commit=None if rng.randrange(2) else d.Receipt().library,
                       fetched=None if rng.randrange(2) else f"{rng.randrange(10000):04}-{rng.randrange(1,13):02}-{rng.randrange(1,32):02}T{rng.randrange(24):02}:{rng.randrange(60):02}:{rng.randrange(61):02}Z",
                       fetch_error=None if rng.randrange(2) else random_text(rng),
                       trusted=tuple(random_text(rng) for _ in range(rng.randrange(5))))
        envelope_cases(s, f"D.envelope.gen.{i:03}", e, "property(seed)")
        bad = replace(e, error=(20, "extra")) if exit != 2 else replace(e, error=None)
        assert not d.envelope_wf(bad)
        add(s, f"D.envelope.wf.gen-invalid.{i:03}", "D.envelope.wf", d.envelope_transport(bad),
            o.value_out(o.boolean(False)), ("D6-wellformed", "D8-checks"), "property(seed)")


def add_typed_checks(s: Suite, rng: random.Random) -> None:
    bad_receipts = [replace(d.Receipt(), checked="bad"), replace(d.Receipt(), spec="bad"),
                    replace(d.Receipt(), profile=""), replace(d.Receipt(), shape=None),
                    replace(d.Receipt(), impl=""), replace(d.Receipt(), proof="x\0"),
                    replace(d.Receipt(), impl_sources=None), replace(d.Receipt(), adapter="f" * 64),
                    replace(d.Receipt(), argv=("x",)), replace(d.differential(), argv=None),
                    replace(d.differential(), argv=()), replace(d.differential(), shape="abi")]
    for i, r in enumerate(bad_receipts):
        assert not d.receipt_wf(r)
        add(s, f"D.receipt.wf.invalid.{i:02}", "D.receipt.wf", d.receipt_transport(r), o.value_out(o.boolean(False)), ("D8-checks",))
        add(s, f"D.receipt.layout.invalid.{i:02}", "D.receipt.encode", d.receipt_transport(r),
            o.value_out(d.receipt_layout(r)), ("D3-layout",))
    for i, r in enumerate([replace(d.Receipt(), decl_kind="differential"), replace(d.differential(), decl_kind="proof")]):
        add(s, f"D.receipt.kind-mismatch.{i}.wf", "D.receipt.wf", d.receipt_transport(r),
            o.value_out(o.boolean(False)), ("D8-checks",))
        add(s, f"D.receipt.kind-mismatch.{i}.layout", "D.receipt.encode", d.receipt_transport(r),
            o.value_out(d.receipt_layout(r)), ("D3-layout",))
    bad_array = update(d.receipt_layout(d.Receipt()), ("request", "adapter"), o.array([o.integer(1)]))
    receipt_decode(s, "D.nullness.before-elements", bad_array, ("D3-nullness", "D5-precedence"),
                   (("request", "adapter"), "bad_value"))
    for i in range(64):
        r = random_receipt(rng, i + 1000)
        if i % 3 == 0:
            changed = replace(r, decl_kind="differential" if r.tag == "proof" else "proof")
        else:
            changed = replace(r, checked="invalid") if i % 2 else replace(r, spec="A" + r.spec[1:])
        add(s, f"D.receipt.wf.gen-invalid.{i:03}", "D.receipt.wf", d.receipt_transport(changed),
            o.value_out(o.boolean(False)), ("D8-checks",), "property(seed)")
        add(s, f"D.receipt.layout.gen-invalid.{i:03}", "D.receipt.encode", d.receipt_transport(changed),
            o.value_out(d.receipt_layout(changed)), ("D3-layout",), "property(seed)")
    for i, r in enumerate([d.Receipt(), d.differential(), replace(d.Receipt(), argv=("x",)), replace(d.differential(), argv=None)]):
        valid_shape = r.argv is None if r.decl_kind == "proof" else r.argv is not None
        add(s, f"D.decl.shaped.{i}", "D.decl.shaped", d.receipt_transport(r), o.value_out(o.boolean(valid_shape)), ("D3-decl-argv",))
    for i in range(40):
        r = replace(d.differential(), argv=("python3", random_text(rng), "", "same"))
        changed = replace(r, argv=(*r.argv, "")) if r.argv is not None else r
        for suffix, other, expected in [("same", r, []), ("changed", changed, [o.string("declaration")])]:
            payload = o.array([d.receipt_transport(r), d.receipt_transport(other)])
            for op in ["changes", "agreement"]:
                add(s, f"D.decl.{op}.{i:03}.{suffix}", "D.decl." + op, payload, o.value_out(o.array(expected)),
                    ("D3-decl-argv",), "property(seed)")


def add_properties(s: Suite, rng: random.Random) -> None:
    for i in range(64):
        r = random_receipt(rng, i)
        receipt_cases(s, f"D.receipt.gen.{i:03}", r, ("D2-commit-digest", "D2-utc", "D2-id-version", "D2-constant-profile", "D2-argv"), "property(seed)")
    for i in range(40):
        count = [0, 1, rng.randrange(2, 8)][i % 3]
        library = "".join(rng.choice("0123456789abcdef") for _ in range(40))
        entries = tuple(sorted((random_receipt(rng, i * 10 + j) for j in range(count)), key=lambda r: r.module.encode()))
        l = d.Lock(library, entries)
        lock_cases(s, f"D.lock.gen.{i:03}", l, "property(seed)")
        shuffled = list(entries)
        if shuffled and i % 2:
            shuffled.append(replace(shuffled[0], profile="duplicate-marker"))
        rng.shuffle(shuffled)
        unsorted = d.Lock(library, tuple(shuffled))
        normalized = d.Lock(library, tuple(sorted(shuffled, key=lambda r: r.module.encode())))
        add(s, f"D.normalize.gen.{i:03}", "D.lock.normalize", d.lock_transport(unsorted), o.value_out(d.lock_transport(normalized)), ("D4-normalize",), "property(seed)")
        add(s, f"D.normalize.wf.{i:03}", "D.lock.normalizeWf", d.lock_transport(unsorted), o.value_out(o.boolean(d.lock_wf(normalized))), ("D4-normalize", "D8-checks"), "property(seed)")
        add(s, f"D.lock.wf.input.{i:03}", "D.lock.wf", d.lock_transport(unsorted), o.value_out(o.boolean(d.lock_wf(unsorted))), ("D8-checks", "D4-order"), "property(seed)")
        value = d.lock_layout(unsorted)
        add(s, f"D.order.gen.{i:03}", "D.lock.decodeValue", value, d.decode_lock_value_output(value),
            ("D4-order",), "property(seed)")
    # Named stability witness: the two equal ids differ in checked/profile/evidence fields.
    a = d.Receipt(module="b.b", profile="first")
    b = replace(d.differential(), module="a.a", profile="middle")
    c = replace(d.differential(), module="b.b", profile="last")
    l = d.Lock(d.Receipt().library, (a, b, c))
    normalized = d.Lock(l.library, (b, a, c))
    add(s, "D.normalize.stable", "D.lock.normalize", d.lock_transport(l), o.value_out(d.lock_transport(normalized)), ("D4-normalize",))
    for i in range(48):
        r = random_receipt(rng, i + 2000)
        base = d.receipt_layout(r)
        choice = rng.randrange(4)
        if choice == 0:
            value = update(base, ("checked",), o.string("bad"))
        elif choice == 1:
            value = update(base, ("request", "module"), o.string("BAD.id"))
        elif choice == 2:
            value = update(base, ("digests", "spec_closure"), o.string("A" * 64))
        else:
            value = update(base, ("verification_profile",), o.string("bad/profile"))
        receipt_decode(s, f"D.schema.gen.{i:03}", value,
                       ("D5-types-values", "D2-commit-digest", "D2-utc", "D2-id-version", "D2-constant-profile"), method="property(seed)")
    for i in range(32):
        r = d.receipt_layout(random_receipt(rng, i + 3000))
        value = update(update(r, ("evidence",), o.string("other")), ("/unknown~",), o.integer(1))
        value = update(value, ("checked",), None)
        receipt_decode(s, f"D.precedence.gen.{i:03}", value, ("D5-precedence", "D5-root-discriminator", "D5-unknown-missing"),
                       (("evidence",), "bad_value"), "property(seed)")
    for i in range(32):
        base = d.receipt_layout(random_receipt(rng, i + 4000))
        parent = rng.choice([(), ("digests",), ("request",)])
        if i % 2:
            member = rng.choice(list(dict(at(base, parent).members)))
            value = update(base, (*parent, member), None)
        else:
            value = update(base, (*parent, "/~" + random_text(rng)), random_value(rng))
        receipt_decode(s, f"D.members.gen.{i:03}", value, ("D5-unknown-missing", "D5-pointer"), method="property(seed)")
    for i in range(24):
        b = o.canonical(d.lock_layout(d.Lock(d.Receipt().library))) + rng.choice([b"x", b"\0", b"[" * 33])
        s.add(f"D.text.gen.{i:03}", "D.lock.decode", b, d.decode_lock_output(b), ("D5-text",), "property(seed)")
    for i in range(64):
        b = bytes(rng.randrange(256) for _ in range(rng.randrange(100)))
        s.add(f"D.text.bytes.{i:03}", "D.lock.decode", b, d.decode_lock_output(b), ("D5-text",), "property(seed)")


def controls(s: Suite) -> None:
    from_case = type(s.cases[0])
    for i, r in enumerate([d.Receipt(), replace(d.Receipt(), shape="abi", policy="development"), d.differential()]):
        value = d.receipt_transport(r)
        s.extra_controls.append(from_case(f"control.doc.receipt.{i}", "D.receipt.transport", o.wire(value), o.value_out(value), ()))
    l = d.Lock(d.Receipt().library, (d.Receipt(), replace(d.differential(), module="semver.parse")))
    value = d.lock_transport(l)
    s.extra_controls.append(from_case("control.doc.lock", "D.lock.transport", o.wire(value), o.value_out(value), ()))


def oracle_controls() -> None:
    r = d.Receipt()
    layout = d.receipt_layout(r)
    assert {k for k, _ in layout.members} == {"checked", "digests", "evidence", "library", "policy", "request", "verification_profile"}
    assert d.receipt_error(layout) is None and d.receipt_from_layout(layout) == r
    assert d.receipt_error(d.receipt_layout(d.differential())) is None
    proof_golden = ('{"checked":"2026-02-31T23:59:60Z","digests":{"adapter":null,"impl_sources":"' + "b" * 64 +
                    '","phase1_export":"' + "d" * 64 + '","proof_sources":"' + "c" * 64 + '","solution_export":"' + "e" * 64 +
                    '","spec_closure":"' + "a" * 64 + '"},"evidence":"proof","library":"0123456789abcdef0123456789abcdef01234567",' +
                    '"policy":"required","request":{"adapter":null,"impl":"Impl.encode","module":"base64.encode","proof":"Proof.encode_eq",' +
                    '"shape":"fn","version":"1.0.0"},"verification_profile":"lean4.35@v1+qualified"}').encode()
    diff_golden = ('{"checked":"2026-02-31T23:59:60Z","digests":{"adapter":"' + "f" * 64 +
                   '","impl_sources":null,"phase1_export":null,"proof_sources":null,"solution_export":null,"spec_closure":"' + "a" * 64 +
                   '"},"evidence":"differential","library":"0123456789abcdef0123456789abcdef01234567","policy":"required",' +
                   '"request":{"adapter":["python3","adapter.py",""],"impl":null,"module":"base64.encode","proof":null,"shape":null,' +
                   '"version":"1.0.0"},"verification_profile":"lean4.35@v1+qualified"}').encode()
    assert o.canonical(layout) == proof_golden
    assert o.canonical(d.receipt_layout(d.differential())) == diff_golden
    assert d.utc("2026-02-31T23:59:60Z") and not d.utc("2026-13-01T00:00:00Z")
    assert d.pointer(("a/b", "m~n", 1)) == "/a~1b/m~0n/1"
    assert d.clip("x" * 65_536) == "x" * 65_536
    assert d.clip("x" * 65_537) == "x" * 65_520 + " [truncated]"
    assert o.canonical(d.lock_layout(d.Lock("0" * 40))) == b'{"library":"0000000000000000000000000000000000000000","modules":[],"schema":1}'
    assert o.canonical(d.envelope_layout(d.Envelope())) == b'{"command":"check","error":null,"exit":0,"result":{},"schema":1,"status":{"commit":null,"fetch_error":null,"fetched":null},"trusted":[]}'
    for value in [layout, d.receipt_layout(d.differential()), d.lock_layout(d.Lock(r.library, (r,))), d.envelope_layout(d.Envelope())]:
        assert o.valid(value)
        assert json.loads(o.canonical(value)) is not None
    print("CONTROL independent-D-goldens layouts=4 PASS", flush=True)


def add_cases(s: Suite) -> None:
    rng = random.Random(s.seed ^ 0xD0C50002)
    add_clips(s, rng)
    receipt_cases(s, "D.receipt.proof", d.Receipt())
    receipt_cases(s, "D.receipt.abi", replace(d.Receipt(), shape="abi", policy="development"))
    receipt_cases(s, "D.receipt.diff", d.differential())
    lock_cases(s, "D.lock.empty", d.Lock(d.Receipt().library))
    lock_cases(s, "D.lock.one", d.Lock(d.Receipt().library, (d.Receipt(),)))
    lock_cases(s, "D.lock.distinct-libraries", d.Lock("0" * 40, (replace(d.Receipt(), library="1" * 40),)))
    add_field_examples(s)
    add_boundaries(s)
    add_schema_cases(s)
    add_precedence(s)
    add_text_and_render(s, rng)
    add_envelopes(s, rng)
    add_typed_checks(s, rng)
    add_properties(s, rng)
    controls(s)
    oracle_controls()
