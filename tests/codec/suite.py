"""Contract-only compiled boundary checks; regenerate every input from the printed seed."""

from __future__ import annotations

import argparse
import csv
import fnmatch
import hashlib
import importlib.util
import json
import os
import random
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable

if TYPE_CHECKING:
    from . import oracle as o
else:
    # -I keeps ambient paths out; load only this suite's exact reference source.
    spec = importlib.util.spec_from_file_location("fvdep_codec_oracle", Path(__file__).with_name("oracle.py"))
    assert spec is not None and spec.loader is not None
    o = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = o
    spec.loader.exec_module(o)


@dataclass(frozen=True)
class Case:
    id: str
    op: str
    payload: bytes
    expected: str
    clauses: tuple[str, ...]
    method: str = "example"


@dataclass(frozen=True)
class Relation:
    id: str
    targets: tuple[str, ...]
    check: Callable[[list[str]], bool]
    clauses: tuple[str, ...]
    method: str = "property(seed)"


class Suite:
    def __init__(self, seed: int) -> None:
        self.seed = seed
        self.rng = random.Random(seed)
        self.cases: list[Case] = []
        self.relations: list[Relation] = []
        self.extra_controls: list[Case] = []
        self.print_values: list[o.V] = []
        self.positive_texts: list[bytes] = []

    def add(self, id: str, op: str, payload: bytes, expected: str,
            clauses: tuple[str, ...], method: str = "example") -> None:
        self.cases.append(Case(id, op, payload, expected, clauses, method))

    def text(self, id: str, b: bytes, clauses: tuple[str, ...],
             named: str | o.V | o.Site | None = None, method: str = "example") -> None:
        result = o.decode(b)
        if isinstance(named, o.V):
            assert result == o.Outcome("ok", value=named), (id, result, named)
        elif isinstance(named, str):
            assert result.kind == named, (id, result, named)
        elif named is not None:
            assert result == o.Outcome("duplicate", site=named), (id, result, named)
        if result.kind == "ok":
            self.positive_texts.append(b)
        self.add(id, "decode", b, result.output(), (*clauses, "J-oracle"), method)

    def value(self, id: str, v: o.V, clauses: tuple[str, ...],
              method: str = "example") -> None:
        assert o.valid(v)
        self.print_values.append(v)
        self.add(id + ".print", "print", o.wire(v), "bytes:" + o.canonical(v).hex(),
                 (*clauses, "J4-canonical", "J4-jq"), method)
        self.add(id + ".roundtrip", "roundtrip", o.wire(v), o.value_out(v),
                 (*clauses, "J6-roundtrip", "J1-valid"), method)

    def frame(self, id: str, tag: str, files: list[tuple[str, bytes]],
              method: str = "example") -> None:
        assert len({p for p, _ in files}) == len(files)
        b = o.frame(tag, files)
        expected = o.unframe_out((tag, sorted(files, key=lambda p: p[0].encode())))
        assert o.unframe(b) == (tag, sorted(files, key=lambda p: p[0].encode()))
        self.add(id + ".encode", "frame", o.frame_args(tag, files), "bytes:" + b.hex(),
                 ("H2-frame",), method)
        self.add(id + ".decode", "unframe", b, expected, ("H2-unframe-ok",), method)
        self.add(id + ".roundtrip", "frameRound", o.frame_args(tag, files), expected,
                 ("H2-unframe-ok", "H4-injective"), method)


def gen_string(rng: random.Random, cap: int = 20) -> str:
    alphabet = ["", "a", "Z", "0", " ", "/", "~", "\\", '"', "\x00", "\x08", "\t", "\n", "\x1f",
                "\x7f", "é", "€", "中", " ", " ", "﻿", "﷐", "￾",
                "￿", "😀", "𝄞", "\U00010000", "\U0010ffff", "é"]
    parts: list[str] = []
    for _ in range(rng.randrange(cap + 1)):
        if rng.randrange(4) == 0:
            cp = rng.randrange(0x110000 - 0x800)
            parts.append(chr(cp if cp < 0xD800 else cp + 0x800))
        else:
            parts.append(rng.choice(alphabet))
    return "".join(parts)


def gen_value(rng: random.Random, fuel: int = 4) -> o.V:
    tag = rng.randrange(6 if fuel else 4)
    if tag == 0:
        return o.null()
    if tag == 1:
        return o.boolean(bool(rng.randrange(2)))
    if tag == 2:
        return o.integer(rng.choice([0, 1, -1, o.MAX_INT, -o.MAX_INT, rng.randint(-o.MAX_INT, o.MAX_INT)]))
    if tag == 3:
        return o.string(gen_string(rng))
    if tag == 4:
        return o.array(gen_value(rng, fuel - 1) for _ in range(rng.randrange(5)))
    keys = {gen_string(rng, 7) for _ in range(rng.randrange(6))}
    return o.obj((k, gen_value(rng, fuel - 1)) for k in sorted(keys, key=lambda s: s.encode()))


def alternative_text(v: o.V, rng: random.Random) -> bytes:
    """Grammar-derived noncanonical spelling; no production output reused."""
    ws = lambda: rng.choice([b"", b" ", b"\n\t", b"\r\n", b" \t\r\n"])

    def quoted(s: str) -> bytes:
        if rng.randrange(2):
            return o.quote(s)
        out = bytearray(b'"')
        for c in s:
            cp = ord(c)
            if cp > 0xFFFF:
                cp -= 0x10000
                out.extend(f"\\u{0xD800 + (cp >> 10):04X}\\u{0xDC00 + (cp & 1023):04x}".encode())
            elif rng.randrange(2) or cp < 32 or c in ('"', "\\"):
                out.extend(f"\\u{cp:04X}".encode())
            else:
                out.extend(c.encode())
        out.append(34)
        return bytes(out)

    def body(x: o.V) -> bytes:
        if x.tag == "str":
            return quoted(o.as_string(x))
        if x.tag == "arr":
            return b"[" + ws() + (b"," + ws()).join(body(y) + ws() for y in x.items) + b"]"
        if x.tag == "obj":
            ms = list(x.members)
            rng.shuffle(ms)
            return b"{" + ws() + (b"," + ws()).join(
                quoted(k) + ws() + b":" + ws() + body(y) + ws() for k, y in ms
            ) + b"}"
        return o.canonical(x)

    return ws() + body(v) + ws()


def add_json_examples(s: Suite) -> None:
    s.add("J.limits", "limits", b"", f"limits:{o.MAX_INT}:65536:32", ("J1-valid",))
    primitives = [o.null(), o.boolean(False), o.boolean(True), o.integer(0), o.string(""), o.array([]), o.obj([])]
    for i, v in enumerate(primitives):
        s.text(f"J.top.{i}", o.canonical(v), ("J2-literals-ws", "J1-valid"), v)
        s.value(f"J.scalar.{i}", v, ("J6-valid-unique",))
    for i, space in enumerate([b" ", b"\t", b"\n", b"\r", b" \t\r\n"]):
        s.text(f"J.ws.{i}", space + b"true" + space, ("J2-literals-ws",), o.boolean(True))
    for i, space in enumerate([b"\x0b", b"\x0c", b"\xc2\xa0", b"\xe2\x80\xa8"]):
        s.text(f"J.ws.invalid.{i}", space + b"true", ("J2-literals-ws",), "malformed")
    for i, literal in enumerate([b"True", b"False", b"NULL", b"Null", b"undefined", b"nil", b"tru", b"fal se"]):
        s.text(f"J.literal.invalid.{i}", literal, ("J2-literals-ws",), "malformed")
    integers = [0, 1, -1, 10, -10, o.MAX_INT - 1, o.MAX_INT, -o.MAX_INT + 1, -o.MAX_INT]
    for i, n in enumerate(integers):
        s.text(f"J.int.valid.{i}", str(n).encode(), ("J2-integers", "J1-valid"), o.integer(n))
        s.value(f"J.int.value.{i}", o.integer(n), ("J2-integers",))
    invalid_numbers = [b"-0", b"00", b"01", b"-01", b"+0", b"+1", b"1.0", b"1.", b".1", b"1e0", b"1E+1",
                       b"1e-1", b"-", b"--1", b"NaN", b"Infinity", str(1 << 53).encode(),
                       str(-(1 << 53)).encode(), b"9" * 10_000, b"-" + b"9" * 10_000, b"0x10"]
    for i, b in enumerate(invalid_numbers):
        s.text(f"J.int.invalid.{i}", b, ("J2-integers",), "malformed")
    escapes = [(b'"\\\""', '"'), (b'"\\\\"', "\\"), (b'"\\/"', "/"), (b'"\\b"', "\b"),
               (b'"\\f"', "\f"), (b'"\\n"', "\n"), (b'"\\r"', "\r"), (b'"\\t"', "\t"),
               (b'"\\u0000"', "\0"), (b'"\\u00e9"', "é"), (b'"\\u00E9"', "é"),
               (b'"\\uD834\\uDD1E"', "𝄞"), (b'"\\ud800\\udc00"', "\U00010000"),
               (b'"\\udbff\\udfff"', "\U0010ffff")]
    for i, (b, text) in enumerate(escapes):
        s.text(f"J.escape.valid.{i}", b, ("J2-strings",), o.string(text))
    for i, b in enumerate([b'"\\v"', b'"\\x41"', b'"\\U00000041"', b'"\\u123"', b'"\\uGGGG"', b'"\\uD800"',
                           b'"\\uD800x"', b'"\\uD800\\u0041"', b'"\\uD800\\uD800"', b'"\\uDC00"',
                           b'"\\uDFFF\\uD800"', b'"\\uD800 \\uDC00"', b'"\\', b'"abc']):
        s.text(f"J.escape.invalid.{i}", b, ("J2-strings",), "malformed")
    for cp in range(32):
        s.text(f"J.raw.control.{cp:02x}", b'"' + bytes([cp]) + b'"', ("J2-strings",), "malformed")
        s.value(f"J.print.control.{cp:02x}", o.string(chr(cp)), ("J2-strings", "J6-roundtrip"))
    content = ["\x7f", "/", " ", " ", "﻿", "﷐", "￾", "￿", "😀", "\U0010ffff"]
    for i, text in enumerate(content):
        s.text(f"J.content.{i}", b'"' + text.encode() + b'"', ("J2-strings",), o.string(text))
        s.value(f"J.content.value.{i}", o.string(text), ("J2-strings",))
    for cp in [0x20, 0x7E, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF]:
        v = o.string(chr(cp))
        s.text(f"J.utf8.valid.{cp:x}", b'"' + chr(cp).encode() + b'"', ("J2-utf8",), v)
        s.value(f"J.utf8.value.{cp:x}", v, ("J2-utf8",))
    invalid_utf8 = [b"\x80", b"\xbf", b"\xc0\x80", b"\xc1\xbf", b"\xe0\x80\x80", b"\xf0\x80\x80\x80",
                    b"\xed\xa0\x80", b"\xed\xbf\xbf", b"\xf4\x90\x80\x80", b"\xf5\x80\x80\x80", b"\xff",
                    b"\xfe", b"\xc2", b"\xe1\x80", b"\xf1\x80\x80", b"\xc2A", b"\xe1A\x80", b"\xf0\x90A\x80"]
    for i, b in enumerate(invalid_utf8):
        s.text(f"J.utf8.invalid.{i}", b'"' + b + b'"', ("J2-utf8",), "malformed")
        s.text(f"J.utf8.key.{i}", b'{"' + b + b'":0}', ("J2-utf8",), "malformed")
    structural = [b"", b" ", b"[", b"{", b"[1,]", b"[,1]", b"[1 2]", b'{"a" 1}', b'{a:1}',
                  b'{"a":}', b'{"a":1,}', b"{,}", b"[]{}", b"true false", b"nullx", b"[}", b"{]",
                  b"\xef\xbb\xbfnull", b"null\x00", b"/*a*/null", b"//x\nnull"]
    for i, b in enumerate(structural):
        s.text(f"J.structure.invalid.{i}", b, ("J2-structure",), "malformed")
    structured = b' \n{ "z" : [true, null, {"b":2,"a":1}], "a": [] }\t'
    expected = o.obj([("a", o.array([])), ("z", o.array([o.boolean(True), o.null(), o.obj([("a", o.integer(1)), ("b", o.integer(2))])]))])
    s.text("J.structure.valid", structured, ("J2-structure", "J3-canon"), expected)
    for n in [0, 1, 2, 31, 32, 33, 34]:
        v = o.null()
        for _ in range(n):
            v = o.array([v])
        s.text(f"J.depth.array.{n}", b"[" * n + b"null" + b"]" * n,
               ("J1-depth", "J3-precedence"), "tooLarge" if n > 32 else v)
        b = b'{"a":' * n + b"0" + b"}" * n
        s.text(f"J.depth.object.{n}", b, ("J1-depth", "J3-precedence"), "tooLarge" if n > 32 else None)
        if n <= 32:
            s.value(f"J.depth.print.{n}", v, ("J1-depth",))
    for n in [31, 32, 33]:
        s.text(f"J.depth.empty.{n}", b"[" * n + b"]" * n, ("J1-depth",), "tooLarge" if n > 32 else None)
    for kind, unit in [("ascii", b"a"), ("two", "é".encode()), ("four", "😀".encode())]:
        for size in [65_535, 65_536, 65_537]:
            content_bytes = unit * (size // len(unit)) + b"a" * (size % len(unit))
            target = o.string(content_bytes.decode())
            named = "tooLarge" if size > 65_536 else target
            s.text(f"J.length.{kind}.{size}", b'"' + content_bytes + b'"',
                   ("J1-valid", "J2-strings", "J3-precedence"), named)
            s.text(f"J.keylength.{kind}.{size}", b'{"' + content_bytes + b'":0}',
                   ("J1-valid", "J3-precedence"), "tooLarge" if size > 65_536 else None)
    # A cap applies to decoded UTF-8, not source spelling or scalar count.
    s.text("J.length.escaped-cap", b'"' + b"\\u0061" * 65_536 + b'"',
           ("J1-valid", "J3-precedence"), o.string("a" * 65_536))
    s.text("J.length.escaped-over", b'"' + b"\\u00e9" * 32_769 + b'"',
           ("J1-valid", "J3-precedence"), "tooLarge")
    over = b'"' + b"a" * 65_537 + b'"'
    consequences = [
        ("garbage-depth", b"x" + b"[" * 33, "tooLarge"),
        ("unclosed-string-depth", b'"' + b"[" * 33, "malformed"),
        ("over-then-garbage", over + b"x", "malformed"),
        ("over-and-duplicate", b'{"a":' + over + b',"a":0}', "tooLarge"),
        ("duplicate-then-garbage", b'{"a":1,"a":2}x', "malformed"),
        ("depth-before-invalid-utf8", b'"\xff"' + b"[" * 33, "tooLarge"),
        ("escaped-quote-depth", b'"\\\"' + b"[" * 33, "malformed"),
        ("escaped-backslash-depth", b'"\\\\"' + b"[" * 33, "tooLarge"),
        ("closing-clamps-at-zero", b"]}" * 40 + b"[" * 33, "tooLarge"),
        ("mismatched-opens-count", b"[{" * 17, "tooLarge"),
    ]
    for name, b, kind in consequences:
        s.text("J.precedence." + name, b, ("J3-precedence",), kind)
    duplicates: list[tuple[str, bytes, o.Site]] = [
        ("root", b'{"a":1,"a":2}', ((), "a")),
        ("ancestor-first", b'{"a":{"b":1,"b":2},"a":3}', ((), "a")),
        ("array-least", b'[{"x":1},{"y":1,"y":2,"c":3,"c":4}]', ((1,), "c")),
        ("escape-alias", b'{"a":0,"\\u0061":1}', ((), "a")),
        ("slash-alias", b'{"a/b":0,"a\\/b":1}', ((), "a/b")),
        ("preorder-text-not-sort", b'{"z":{"b":1,"b":2},"a":{"a":1,"a":2}}', (("z",), "b")),
        ("least-not-first-repeat", b'{"z":0,"z":1,"a":2,"a":3}', ((), "a")),
        ("mixed-path", b'{"a/b":[null,{"~":{"":1,"":2}}]}', (("a/b", 1, "~"), "")),
        ("nul", b'{"\\u0000":0,"\\u0000":1}', ((), "\0")),
        ("nonbmp", '{"😀":0,"😀":1,"￿":2,"￿":3}'.encode(), ((), "￿")),
    ]
    for name, b, site in duplicates:
        s.text("J.site." + name, b, ("J3-site",), site)
    s.text("J.keys.scalar-sequence", '{"é":0,"é":1}'.encode(), ("J3-site", "J3-canon"),
           o.obj([("é", o.integer(1)), ("é", o.integer(0))]))
    unicode_keys = ["😀", "￿", "\U00010000", "", "é", "é", "\x00", "a", "", "/", "~"]
    raw = o.obj((k, o.obj([("z", o.integer(i)), ("a", o.integer(-i))])) for i, k in enumerate(unicode_keys))
    s.text("J.canon.unicode-nested", o.canonical(raw), ("J3-canon",), o.canonicalize(raw))
    # Lexical guard must keep the compiled decoder away from recursive million-deep input.
    s.text("J.deep.million-open", b"[" * 1_000_000, ("J3-deep", "J3-precedence"), "tooLarge")
    s.text("J.deep.million-closed", b"[" * 1_000_000 + b"0" + b"]" * 1_000_000,
           ("J3-deep", "J3-precedence"), "tooLarge")
    s.text("J.deep.quoted-million-open", b'"' + b"[" * 1_000_000,
           ("J3-deep", "J3-precedence"), "malformed")
    s.text("J.deep.long-digits", b"9" * 1_000_000, ("J3-deep", "J2-integers"), "malformed")
    s.text("J.deep.flat-array", b"[" + b",".join([b"0"] * 4096) + b"]", ("J3-deep", "J2-structure"))
    all_escapes = o.string('"\\/\b\f\n\r\t' + "".join(map(chr, range(32))) + "\x7fé  ﻿﷐￾￿😀")
    s.value("J.print.all-escapes", all_escapes, ("J4-canonical",))
    s.value("J.print.key-byte-order", o.canonicalize(raw), ("J4-canonical", "J6-valid-unique"))
    for size in [65_535, 65_536]:
        s.value(f"J.print.cap.{size}", o.string("a" * size), ("J1-valid",))


def add_json_properties(s: Suite) -> None:
    values = [gen_value(s.rng) for _ in range(128)]
    for i, v in enumerate(values):
        s.value(f"J.gen.value.{i:03}", v, ("J6-valid-unique",), "property(seed)")
        text = alternative_text(v, s.rng)
        s.text(f"J.gen.text.{i:03}", text, ("J1-valid", "J2-literals-ws", "J2-strings", "J3-canon"),
               v, "property(seed)")
        # Alternate text and canonical text have the same meaning; no decoder output seeds another case.
        canon_id = f"J.gen.canon.{i:03}"
        s.text(canon_id, o.canonical(v), ("J6-valid-unique",), v, "property(seed)")
        s.relations.append(Relation(f"J.prop.text-unique.{i:03}", (f"J.gen.text.{i:03}", canon_id),
                                    lambda got: got[0] == got[1], ("J6-valid-unique",)))
    for i in range(256):
        b = bytearray(alternative_text(s.rng.choice(values), s.rng))
        kind = i % 5
        pos = s.rng.randrange(len(b) + 1)
        if kind == 0:
            b[pos:pos] = bytes([s.rng.randrange(256)])
        elif kind == 1 and b:
            del b[min(pos, len(b) - 1)]
        elif kind == 2 and b:
            b[min(pos, len(b) - 1)] = s.rng.randrange(256)
        elif kind == 3:
            b.extend(s.rng.choice([b"x", b"\x00", b"[" * 33, b'"', b",", b" "]))
        else:
            b = b[:pos]
        s.text(f"J.gen.mutate.{i:03}", bytes(b), ("J2-structure", "J3-precedence"), method="property(seed)")
    for i in range(128):
        b = bytes(s.rng.randrange(256) for _ in range(s.rng.randrange(80)))
        s.text(f"J.gen.bytes.{i:03}", b, ("J2-utf8", "J3-precedence"), method="property(seed)")
    for i in range(48):
        key = gen_string(s.rng, 8)
        other = key + "a"
        repeated = o.obj([(other, o.integer(1)), (other, o.integer(2)), (key, o.null()), (key, o.boolean(True))])
        path: tuple[o.Segment, ...] = ()
        wrapped = repeated
        for _ in range(s.rng.randrange(5)):
            if s.rng.randrange(2):
                parent_key = gen_string(s.rng, 6)
                wrapped = o.obj([(parent_key, wrapped)])
                path = (parent_key, *path)
            else:
                n = s.rng.randrange(4)
                wrapped = o.array([o.null()] * n + [wrapped])
                path = (n, *path)
        s.text(f"J.gen.site.{i:03}", alternative_text(wrapped, s.rng), ("J3-site",),
               (path, min([key, other], key=lambda x: x.encode())), "property(seed)")
    # Canonical injectivity: use a guaranteed distinct scalar vs array, not an accidental random collision.
    for i in range(48):
        v = gen_value(s.rng)
        w = o.array([v])
        a, b = f"J.injective.{i:03}.left", f"J.injective.{i:03}.right"
        s.add(a, "print", o.wire(v), "bytes:" + o.canonical(v).hex(), ("J6-valid-unique",), "property(seed)")
        s.add(b, "print", o.wire(w), "bytes:" + o.canonical(w).hex(), ("J6-valid-unique",), "property(seed)")
        s.relations.append(Relation(f"J.prop.injective.{i:03}", (a, b),
                                    lambda got: got[0] != got[1], ("J6-valid-unique",)))


def add_boundary_properties(s: Suite) -> None:
    for i in range(64):
        n = s.rng.randint(-o.MAX_INT, o.MAX_INT)
        s.text(f"J.prop.integer.{i:03}", str(n).encode(), ("J2-integers", "J1-valid"),
               o.integer(n), "property(seed)")
        bad = s.rng.choice([b"+" + str(abs(n)).encode(), str(n).encode() + b".0",
                            str(n).encode() + b"e0", b"0" + str(abs(n) + 1).encode(),
                            str((1 << 53) + abs(n)).encode()])
        s.text(f"J.prop.integer-refuse.{i:03}", bad, ("J2-integers",), "malformed", "property(seed)")
        nesting = s.rng.randrange(41)
        b = b"0"
        for _ in range(nesting):
            b = b"[" + b + b"]" if s.rng.randrange(2) else b'{"x":' + b + b"}"
        s.text(f"J.prop.depth.{i:03}", b, ("J1-depth", "J1-valid", "J3-precedence"),
               "tooLarge" if nesting > 32 else None, "property(seed)")
        text = gen_string(s.rng, 30)
        v = o.string(text)
        s.text(f"J.prop.escapes.{i:03}", alternative_text(v, s.rng), ("J2-strings",), v, "property(seed)")
        # Each invalid raw scalar family remains invalid with any safe ASCII prefix/suffix.
        broken = s.rng.choice([b"\xc0\x80", b"\xed\xa0\x80", b"\xf4\x90\x80\x80", b"\x80", b"\xf0\x90"])
        b = b'"' + b"a" * s.rng.randrange(9) + broken + b"z" * s.rng.randrange(9) + b'"'
        s.text(f"J.prop.utf8-refuse.{i:03}", b, ("J2-utf8",), "malformed", "property(seed)")
    for i in range(18):
        width = s.rng.choice([1, 2, 3, 4])
        char = {1: "x", 2: "é", 3: "中", 4: "😀"}[width]
        size = 65_536 + s.rng.choice([-1, 0, 1])
        b = char.encode() * (size // width) + b"x" * (size % width)
        text = b'"' + b + b'"'
        s.text(f"J.prop.string-bound.{i:03}", text, ("J1-valid", "J3-precedence"),
               "tooLarge" if size > 65_536 else o.string(b.decode()), "property(seed)")
        s.text(f"J.prop.string-bound-malformed.{i:03}", text + b"x", ("J3-precedence",),
               "malformed", "property(seed)")
    for i in range(8):
        cp = s.rng.randrange(0x110000 - 0x800)
        char = chr(cp if cp < 0xD800 else cp + 0x800)
        text = char * s.rng.randrange(o.MAX_STRING // len(char.encode()) + 1)
        v = o.string(text)
        s.value(f"J.prop.string-interior.{i:03}", v, ("J1-valid", "J2-strings"), "property(seed)")
        s.text(f"J.prop.string-interior-text.{i:03}", alternative_text(v, s.rng),
               ("J1-valid", "J2-strings"), v, "property(seed)")
    for i in range(12):
        n = s.rng.randrange(33, 257)
        s.text(f"J.prop.lexical.{i:03}", b"garbage" + b"[" * n,
               ("J1-depth", "J3-precedence"), "tooLarge", "property(seed)")
        s.text(f"J.prop.lexical-quoted.{i:03}", b'"' + b"[" * n,
               ("J3-precedence",), "malformed", "property(seed)")


def add_accessor_cases(s: Suite) -> None:
    too_deep = o.null()
    for _ in range(33):
        too_deep = o.array([too_deep])
    values = [o.null(), o.boolean(False), o.boolean(True), o.integer(-o.MAX_INT), o.string("\0é😀"),
              o.array([]), o.array([o.null(), o.integer(1)]), o.obj([]), o.obj([("a", o.null())]),
              o.integer(o.MAX_INT + 1), o.integer(-o.MAX_INT - 1), o.integer(10**100),
              o.string("a" * 65_537), too_deep,
              o.obj([("z", o.integer(1)), ("a", o.null()), ("a", o.integer(2))])]
    named_count = len(values)
    values.extend(gen_value(s.rng) for _ in range(64))
    for i, v in enumerate(values):
        candidates = ["bool", "int", "str", "arr", "obj"]
        expected = o.array(o.array([v]) if v.tag == tag else o.array([]) for tag in candidates)
        s.add(f"J.as.{i:03}", "as", o.wire(v), o.value_out(expected), ("J5-as",),
              "example" if i < named_count else "property(seed)")
        for j, key in enumerate(["missing", "a", "\0", "é", "é"]):
            found = next((x for k, x in v.members if k == key), None) if v.tag == "obj" else None
            expect = o.array([] if found is None else [found])
            s.add(f"J.get.{i:03}.{j}", "get", o.wire(o.array([v, o.string(key)])), o.value_out(expect),
                  ("J5-get",), "example" if i < named_count else "property(seed)")
    for name, members in [("empty", []), ("singleton", [("é", o.null())])]:
        v = o.obj(members)
        s.add("J.object." + name, "object", o.wire(v), o.value_out(v), ("J5-object",))
    # Constructors accept unsorted/repeated outer members; children remain byte-for-byte unchanged.
    raw_child = o.obj([("z", o.integer(1)), ("a", o.integer(2)), ("z", o.integer(3))])
    named = [("z", o.null()), ("a", o.integer(1)), ("a", o.integer(2)), ("", raw_child),
             ("😀", o.integer(4)), ("￿", o.integer(5))]
    for i in range(65):
        ms = list(named) if i == 0 else [(gen_string(s.rng, 3), gen_value(s.rng, 2)) for _ in range(s.rng.randrange(12))]
        if i and ms:
            ms.extend([(ms[0][0], o.integer(100 + i)), (ms[0][0], o.null())])
        s.rng.shuffle(ms)
        expected = o.obj(sorted(ms, key=lambda p: p[0].encode()))
        s.add(f"J.object.{i:03}", "object", o.wire(o.obj(ms)), o.value_out(expected), ("J5-object",),
              "example" if i == 0 else "property(seed)")
        if ms:
            key = ms[0][0]
            s.add(f"J.get.repeat.{i:03}", "get", o.wire(o.array([o.obj(ms), o.string(key)])),
                  o.value_out(o.array([ms[0][1]])), ("J5-get",), "property(seed)")
    for text, label in [("é", "precomposed"), ("é", "decomposed")]:
        v = o.obj([("é", o.integer(1)), ("é", o.integer(2))])
        expected = o.integer(2 if text == "é" else 1)
        s.add("J.get.unicode." + label, "get", o.wire(o.array([v, o.string(text)])),
              o.value_out(o.array([expected])), ("J5-get",))


def add_hash_cases(s: Suite) -> None:
    for name, b in [("empty", b""), ("all-bytes", bytes(range(256))), ("nibbles", b"\x00\x01\x0f\x10\x7f\x80\xfe\xff")]:
        s.add("H.hex." + name, "hex", b, "text:" + b.hex().encode().hex(), ("H1-hex",))
    for i in range(64):
        b = bytes(s.rng.randrange(256) for _ in range(s.rng.randrange(513)))
        s.add(f"H.hex.gen.{i:03}", "hex", b, "text:" + b.hex().encode().hex(), ("H1-hex",), "property(seed)")
    s.frame("H.frame.empty", "", [])
    s.frame("H.frame.named", "fvdep/spec-closure/1", [("z", b"\0\xff"), ("a", b"hello"), ("", b"")])
    s.frame("H.frame.multibyte", "é😀\0", [("😀", b"a"), ("￿", b"b"), ("é", b"c"), ("é", b"d")])
    s.frame("H.frame.paths-verbatim", "tag", [("a/../b", b"x"), ("b", b"y"), ("/b", b"z"), ("a//b", b"q")])
    for i in range(96):
        tag = gen_string(s.rng, 12)
        paths = list({gen_string(s.rng, 7) for _ in range(s.rng.randrange(8))})
        paths.sort(key=lambda p: p.encode())
        s.rng.shuffle(paths)
        files = [(p, bytes(s.rng.randrange(256) for _ in range(s.rng.randrange(80)))) for p in paths]
        id = f"H.frame.gen.{i:03}"
        s.frame(id, tag, files, "property(seed)")
        perm = list(files)
        s.rng.shuffle(perm)
        alt_id = f"H.permute.{i:03}"
        s.add(alt_id, "frame", o.frame_args(tag, perm), "bytes:" + o.frame(tag, files).hex(),
              ("H4-injective",), "property(seed)")
        s.relations.append(Relation(f"H.prop.permute.{i:03}", (id + ".encode", alt_id),
                                    lambda got: got[0] == got[1], ("H4-injective",)))
        # Changing only the domain tag must change the frame; tags include NUL/UTF-8 too.
        other = f"H.tag-distinct.{i:03}"
        s.add(other, "frame", o.frame_args(tag + "x", files), "bytes:" + o.frame(tag + "x", files).hex(),
              ("H4-injective",), "property(seed)")
        s.relations.append(Relation(f"H.prop.injective.{i:03}", (id + ".encode", other),
                                    lambda got: got[0] != got[1], ("H4-injective",)))
        changed = list(files)
        if changed:
            p, content = changed[0]
            changed[0] = (p, content + b"x")
        else:
            changed = [("", b"")]
        changed_id = f"H.files-distinct.{i:03}"
        s.add(changed_id, "frame", o.frame_args(tag, changed), "bytes:" + o.frame(tag, changed).hex(),
              ("H4-injective", "H2-frame"), "property(seed)")
        s.relations.append(Relation(f"H.prop.files-injective.{i:03}", (id + ".encode", changed_id),
                                    lambda got: got[0] != got[1], ("H4-injective",)))
    # Independently construct forbidden layouts; do not call the encoder that sorts them.
    def layout(tag: bytes, files: list[tuple[bytes, bytes]]) -> bytes:
        return o.u64(len(tag)) + tag + o.u64(len(files)) + b"".join(
            o.u64(len(p)) + p + o.u64(len(b)) + b for p, b in files)
    malformed: list[tuple[str, bytes]] = [
        ("empty", b""), ("trailing", o.frame("t", []) + b"x"),
        ("unsorted", layout(b"t", [(b"b", b"1"), (b"a", b"2")])),
        ("repeat", layout(b"t", [(b"a", b"1"), (b"a", b"2")])),
        ("invalid-tag", layout(b"\xff", [])), ("invalid-path", layout(b"t", [(b"\xed\xa0\x80", b"")])),
        ("tag-length-past", o.u64(2**64 - 1) + b"t" + o.u64(0)),
        ("count-past", o.u64(0) + o.u64(2**64 - 1)),
        ("path-length-past", o.u64(0) + o.u64(1) + o.u64(2**64 - 1)),
        ("content-length-past", o.u64(0) + o.u64(1) + o.u64(0) + o.u64(2**64 - 1)),
        ("little-endian-tag", (1).to_bytes(8, "little") + b"t" + o.u64(0)),
    ]
    truncation = o.frame("é😀", [("a", b"\0\xff"), ("é", b"xyz")])
    malformed.extend((f"truncate-{i:03}", truncation[:i]) for i in range(len(truncation)))
    for name, b in malformed:
        assert o.unframe(b) is None, name
        s.add("H.unframe.refuse." + name, "unframe", b, "none", ("H2-unframe-refuse",))
    for i in range(128):
        if i % 2:
            b = bytearray(truncation)
            pos = s.rng.randrange(len(b))
            b[pos] ^= 1 << s.rng.randrange(8)
        else:
            b = bytearray(s.rng.randrange(256) for _ in range(s.rng.randrange(100)))
        decoded = o.unframe(bytes(b))
        expect = o.unframe_out(decoded)
        s.add(f"H.unframe.gen.{i:03}", "unframe", bytes(b), expect,
              ("H2-unframe-refuse", "H2-unframe-ok"), "property(seed)")
        if decoded is not None:
            tag, files = decoded
            assert o.frame(tag, files) == bytes(b)
            s.add(f"H.unframe.reencode.{i:03}", "frame", o.frame_args(tag, files), "bytes:" + bytes(b).hex(),
                  ("H2-unframe-ok", "H4-injective"), "property(seed)")
    tags = ["fvdep/spec-closure/1", "fvdep/impl-sources/1", "fvdep/proof-sources/1", "fvdep/adapter/1", "fvdep/entry/1"]
    s.add("H.tags", "tags", b"", o.value_out(o.array(map(o.string, tags))), ("H3-tags",))
    vectors = [[], [""], ["a", "a"], ["python3", "adapter.py", "--arg", "adapter.py"], ["é", "😀", "\0", "a\nb"]]
    vectors.extend([gen_string(s.rng) for _ in range(s.rng.randrange(9))] for _ in range(64))
    for i, argv in enumerate(vectors):
        s.add(f"H.argv.{i:03}", "argv", o.wire(o.array(map(o.string, argv))),
              "bytes:" + o.argv_bytes(argv).hex(), ("H3-argv",), "example" if i < 5 else "property(seed)")
        named = [("", b"drop"), ("b", b"first-b"), ("a", b"first-a"), ("b", b"second-b"), ("", b"drop-2"), ("é", b"\xff")]
        if i >= 5:
            named = [(gen_string(s.rng, 3), bytes([j])) for j in range(s.rng.randrange(12))]
            if named:
                named.extend([(named[0][0], b"different"), ("", b"drop")])
        payload = o.wire(o.array([o.array(map(o.string, argv)), o.files_value(named)]))
        s.add(f"H.adapter.{i:03}", "adapter", payload, o.value_out(o.files_value(o.adapter_entries(argv, named))),
              ("H3-adapter",), "example" if i < 5 else "property(seed)")
    adapter_argv = ["python3", "é.py", "é.py", "--x"]
    adapter_named = [("é.py", b"print(1)\n"), ("é.py", b"second must lose"), ("", b"drop")]
    s.frame("H.frame.adapter", "fvdep/adapter/1", o.adapter_entries(adapter_argv, adapter_named))


def python_value(x: Any) -> o.V:
    if isinstance(x, o.V):
        return x
    if x is None:
        return o.null()
    if type(x) is bool:
        return o.boolean(x)
    if type(x) is int:
        return o.integer(x)
    if isinstance(x, str):
        return o.string(x)
    if isinstance(x, list):
        return o.array(map(python_value, x))
    raise AssertionError(type(x))


def cross_checks(s: Suite) -> None:
    def reject(x: str) -> Any:
        raise ValueError(x)
    def strict_int(x: str) -> int:
        n = int(x)
        if x == "-0" or abs(n) > o.MAX_INT:
            raise ValueError(x)
        return n
    corpus = s.positive_texts
    for b in corpus:
        x = json.loads(b.decode("utf-8", "strict"), parse_int=strict_int, parse_float=reject,
                       parse_constant=reject,
                       object_pairs_hook=lambda ms: o.obj((k, python_value(v)) for k, v in ms))
        result = o.decode(b)
        assert result.kind == "ok" and result.value == o.canonicalize(python_value(x)), "Python corpus disagreement"
    negatives = [b"", b"[", b'{"a":}', b"[1,]", b'"\\x00"', b"nullx", b"{,}", b"true false"]
    for b in negatives:
        assert o.decode(b).kind == "malformed"
        try:
            json.loads(b, parse_int=strict_int, parse_float=reject, parse_constant=reject)
        except ValueError:
            pass
        else:
            raise AssertionError(f"strict Python accepted malformed corpus item {b!r}")
        result = subprocess.run(["jq", "-S", "-c", "."], input=b, capture_output=True, check=False, timeout=5)
        # jq reads a stream; a single JSON text must produce exactly one LF-terminated value.
        assert result.returncode != 0 or result.stdout.count(b"\n") != 1, f"jq accepted one malformed text {b!r}"
    print(f"CONTROL strict-python corpus={len(corpus)} negatives={len(negatives)} PASS", flush=True)
    jq_input = b"".join(o.canonical(v) + b"\n" for v in s.print_values)
    result = subprocess.run(["jq", "-S", "-c", "."], input=jq_input, capture_output=True, check=False, timeout=30)
    if result.returncode:
        raise AssertionError(f"jq rc={result.returncode}: {result.stderr[:200]!r}")
    lines = result.stdout.split(b"\n")
    assert lines[-1] == b"" and len(lines) == len(s.print_values) + 1
    for i, (v, actual) in enumerate(zip(s.print_values, lines[:-1], strict=True)):
        expected = o.canonical(v)
        if actual != expected:
            raise AssertionError(f"jq printer disagreement at {i}: {actual[:150]!r} != {expected[:150]!r}")
    version = subprocess.run(["jq", "--version"], text=True, capture_output=True, check=True).stdout.strip()
    print(f"CONTROL {version} canonical-values={len(s.print_values)} PASS", flush=True)
    # Named goldens prevent a self-consistent transport/oracle bug from grading the implementation.
    assert o.canonical(o.string('\0\b\t\n\f\r\x1f\x7f/é')) == b'"\\u0000\\b\\t\\n\\f\\r\\u001f\\u007f/\xc3\xa9"'
    assert o.frame("é", [("a", b"\0")]) == bytes.fromhex(
        "0000000000000002c3a90000000000000001000000000000000161000000000000000100")
    assert o.argv_bytes(["a", "a"]) == bytes.fromhex(
        "0000000000000002000000000000000161000000000000000161")
    print("CONTROL independent-goldens PASS", flush=True)


def short(value: str) -> str:
    if len(value) <= 110:
        return value
    return value[:65] + f"...len={len(value)},sha256={hashlib.sha256(value.encode()).hexdigest()}"


def execute(s: Suite, driver: Path, work: Path, report: Path) -> int:
    names = [c.id for c in s.cases] + [r.id for r in s.relations]
    assert len(names) == len(set(names)), "duplicate case id"
    work.mkdir(parents=True, exist_ok=True)
    requests = work / "requests.tsv"
    results = work / "results.tsv"
    controls = [o.null(), o.boolean(False), o.boolean(True), o.integer(-o.MAX_INT), o.integer(o.MAX_INT),
                o.string("\0é😀\n"), o.array([]), o.obj([]),
                o.obj([("z", o.array([o.null()])), ("a", o.integer(1)), ("a", o.integer(2))])]
    with requests.open("w", encoding="utf-8") as manifest:
        for i, v in enumerate(controls):
            path = work / f"control-{i}.input"
            path.write_bytes(o.wire(v))
            manifest.write(f"control.echo.{i}\techo\t{path.resolve()}\n")
        for i, c in enumerate(s.extra_controls):
            path = work / f"extra-control-{i}.input"
            path.write_bytes(c.payload)
            manifest.write(f"{c.id}\t{c.op}\t{path.resolve()}\n")
        for i, c in enumerate(s.cases):
            path = work / f"{i:05}.input"
            path.write_bytes(c.payload)
            manifest.write(f"{c.id}\t{c.op}\t{path.resolve()}\n")
    start = time.monotonic()
    command = [str(driver.resolve()), str(requests.resolve()), str(results.resolve())]
    try:
        completed = subprocess.run(command, capture_output=True, text=True, timeout=270, check=False,
                                   env={**os.environ, "LEAN_ABORT_ON_PANIC": "1"})
    except subprocess.TimeoutExpired:
        completed = subprocess.CompletedProcess(command, 124, "", "driver deadline exceeded (270 s)")
    elapsed = time.monotonic() - start
    observed: dict[str, str] = {}
    if results.exists():
        for line in results.read_text(encoding="utf-8").splitlines():
            id, sep, value = line.partition("\t")
            assert sep and id not in observed, "driver protocol duplicate/bad row"
            observed[id] = value
    if completed.returncode:
        print(f"DRIVER rc={completed.returncode} stderr={completed.stderr[-800:]!r}", flush=True)
    for i, v in enumerate(controls):
        assert observed.get(f"control.echo.{i}") == o.value_out(v), f"transport echo failed at {i}"
    print(f"CONTROL independent-transport values={len(controls)} PASS", flush=True)
    for c in s.extra_controls:
        assert observed.get(c.id) == c.expected, f"transport echo failed: {c.id}"
    if s.extra_controls:
        print(f"CONTROL independent-D-transport values={len(s.extra_controls)} PASS", flush=True)
    verdicts: dict[str, bool] = {}
    details: dict[str, str] = {}
    for c in s.cases:
        got = observed.get(c.id, "<driver missing result>")
        passed = got == c.expected
        verdicts[c.id] = passed
        detail = f"expected={short(c.expected)} got={short(got)}"
        details[c.id] = detail
        print(("PASS " + c.id) if passed else ("FAIL " + c.id + " " + detail), flush=True)
    for r in s.relations:
        present = all(id in observed for id in r.targets)
        passed = present and all(verdicts[id] for id in r.targets) and r.check([observed[id] for id in r.targets])
        verdicts[r.id] = passed
        detail = "targets=" + ",".join(r.targets)
        details[r.id] = detail
        print(("PASS " + r.id) if passed else ("FAIL " + r.id + " " + detail), flush=True)
    report.parent.mkdir(parents=True, exist_ok=True)
    with report.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(["id", "verdict", "op", "clauses", "method", "detail"])
        for c in s.cases:
            writer.writerow([c.id, "PASS" if verdicts[c.id] else "FAIL", c.op, ",".join(c.clauses), c.method, details[c.id]])
        for r in s.relations:
            writer.writerow([r.id, "PASS" if verdicts[r.id] else "FAIL", "relation", ",".join(r.clauses), r.method, details[r.id]])
    coverage: dict[str, list[str]] = {}
    methods: dict[str, set[str]] = {}
    for item in [*s.cases, *s.relations]:
        for clause in item.clauses:
            coverage.setdefault(clause, []).append(item.id)
            methods.setdefault(clause, set()).add(item.method)
    for clause, ids in coverage.items():
        p = sum(verdicts[id] for id in ids)
        print(f"CLAUSE {clause} {len(ids) - p}F/{p}P cases={','.join(ids)} methods={','.join(sorted(methods[clause]))}")
    passed = sum(verdicts.values())
    failed = len(verdicts) - passed
    print(f"SUMMARY seed={s.seed} cases={len(verdicts)} api={len(s.cases)} relations={len(s.relations)} pass={passed} fail={failed} driver_rc={completed.returncode} driver_seconds={elapsed:.3f}", flush=True)
    return 1 if failed or completed.returncode else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=Path("tests/codec/.results/latest.tsv"))
    parser.add_argument("--case", default=os.environ.get("FVDEP_CODEC_CASE"))
    args = parser.parse_args()
    seed = int(os.environ.get("FVDEP_TEST_SEED", "0xF7DE3001"), 0)
    print(f"SEED {seed} (FVDEP_TEST_SEED overrides)", flush=True)
    s = Suite(seed)
    add_json_examples(s)
    add_json_properties(s)
    add_boundary_properties(s)
    add_accessor_cases(s)
    add_hash_cases(s)
    cross_checks(s)
    for name in ["doc_oracle", "doc_cases"]:
        doc_spec = importlib.util.spec_from_file_location("fvdep_codec_" + name, Path(__file__).with_name(name + ".py"))
        assert doc_spec is not None and doc_spec.loader is not None
        document_module = importlib.util.module_from_spec(doc_spec)
        sys.modules[doc_spec.name] = document_module
        doc_spec.loader.exec_module(document_module)
    vars(sys.modules["fvdep_codec_doc_cases"])["add_cases"](s)
    if args.case:
        selected = {c.id for c in s.cases if fnmatch.fnmatchcase(c.id, args.case)}
        s.relations = [r for r in s.relations if fnmatch.fnmatchcase(r.id, args.case)]
        for r in s.relations:
            selected.update(r.targets)
        if not selected:
            parser.error("--case matches no case")
        s.cases = [c for c in s.cases if c.id in selected]
    return execute(s, args.driver, args.work, args.report)


if __name__ == "__main__":
    raise SystemExit(main())
