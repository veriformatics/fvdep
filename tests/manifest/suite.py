#!/usr/bin/env python3
"""Blind T1–T6 differential suite. Oracles = contract T3/T4 + Python UTF-8/tomllib."""
from __future__ import annotations

import argparse
import copy
import csv
import datetime
import hashlib
import json
import os
from pathlib import Path
import random
import re
import subprocess
import time
import tomllib
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

Tree = dict[str, Any]
Manifest = dict[str, Any]
SEED = 0xF4DE6304
CAP = 65_536
COMMIT = "0123456789abcdef0123456789abcdef01234567"
ID = re.compile(r"[a-z][a-z0-9]*\.[a-z][a-z0-9]*(?:_[a-z][a-z0-9]*)*\Z", re.ASCII)
VERSION = re.compile(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\Z", re.ASCII)
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z", re.ASCII)
ROOT = {"schema", "library", "policy", "modules"}
PROOF = {"version", "shape", "impl_modules", "proof_modules", "impl", "proof"}
DIFF = {"version", "evidence", "adapter"}
KNOWN = PROOF | DIFF


def jdump(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def node(tag: str, value: Any) -> Tree:
    return {"t": tag, "v": value}


def table(**members: Tree) -> Tree:
    return node("tbl", [[k, v] for k, v in members.items()])


def trees(value: Any) -> Tree:
    if isinstance(value, bool):
        return node("bool", value)
    if isinstance(value, str):
        return node("str", value)
    if isinstance(value, int):
        return node("int", value)
    if isinstance(value, float):
        return node("other", "float")
    if isinstance(value, (datetime.datetime, datetime.date, datetime.time)):
        return node("other", "datetime")
    if isinstance(value, list):
        return node("arr", [trees(x) for x in value])
    if isinstance(value, dict):
        return node("tbl", [[k, trees(v)] for k, v in value.items()])
    raise TypeError(type(value))


def sort_tree(t: Tree) -> Tree:
    if t["t"] == "tbl":
        return node("tbl", [[k, sort_tree(v)] for k, v in sorted(t["v"], key=lambda p: p[0].encode())])
    if t["t"] == "arr":
        return node("arr", [sort_tree(x) for x in t["v"]])
    return t


def set_member(t: Tree, path: list[str], value: Tree | None) -> Tree:
    out = copy.deepcopy(t)
    target = out
    for key in path[:-1]:
        target = next(v for k, v in target["v"] if k == key)
    target["v"] = [[k, v] for k, v in target["v"] if k != path[-1]]
    if value is not None:
        target["v"].append([path[-1], value])
    return out


def basic(s: str) -> str:
    escapes = {'"': '\\"', "\\": "\\\\", "\b": "\\b", "\t": "\\t", "\n": "\\n", "\f": "\\f", "\r": "\\r"}
    return '"' + "".join(escapes.get(c, f"\\u{ord(c):04X}" if ord(c) < 32 or ord(c) == 127 else c) for c in s) + '"'


def key_path(path: Sequence[str | int]) -> str:
    out = ""
    for item in path:
        if isinstance(item, int):
            out += f"[{item}]"
        else:
            out += ("." if out else "") + (item if re.fullmatch(r"[A-Za-z0-9_-]+", item, re.ASCII) else basic(item))
    return out


class Refusal(Exception):
    def __init__(self, path: list[str | int], kind: str, expected: str | None = None, name: str | None = None):
        self.value = {"path": path, "kind": kind, "expected": expected, "name": name}
        super().__init__(jdump(self.value))


def refuse(path: list[str | int], kind: str, expected: str | None = None, name: str | None = None) -> Any:
    raise Refusal(path, kind, expected, name)


def as_kind(t: Tree, tag: str, path: list[str | int], expected: str) -> Any:
    if t["t"] != tag:
        refuse(path, "wrong_type", expected)
    return t["v"]


def members(t: Tree, path: list[str | int]) -> dict[str, Tree]:
    pairs = as_kind(t, "tbl", path, "table")
    seen: set[str] = set()
    duplicates: set[str] = set()
    for key, _ in pairs:
        if key in seen:
            duplicates.add(key)
        seen.add(key)
    if duplicates:
        refuse(path, "duplicate_key", name=min(duplicates, key=lambda x: x.encode()))
    return dict(pairs)


def keys(d: dict[str, Tree], allowed: set[str], required: set[str], path: list[str | int], forbidden: set[str] | None = None) -> None:
    for key in sorted(set(d) - allowed, key=lambda x: x.encode()):
        refuse(path + [key], "unknown_field")
    for key in sorted(set(d) & (forbidden or set()), key=lambda x: x.encode()):
        refuse(path + [key], "forbidden_field")
    for key in sorted(required - set(d), key=lambda x: x.encode()):
        refuse(path + [key], "missing_field")


def string_value(t: Tree, path: list[str | int], predicate: Any) -> str:
    value = as_kind(t, "str", path, "string")
    if not predicate(value):
        refuse(path, "bad_value")
    return value


def list_value(t: Tree, path: list[str | int], adapter: bool) -> list[str]:
    xs = as_kind(t, "arr", path, "array")
    if not xs:
        refuse(path, "bad_value")
    out: list[str] = []
    for i, x in enumerate(xs):
        s = as_kind(x, "str", path + [i], "string")
        valid = (len(s.encode()) <= CAP and "\0" not in s and (i > 0 or bool(s))) if adapter else (
            len(s.encode()) <= 256 and NAME.fullmatch(s) is not None and
            s.split(".")[0] not in {"Init", "Std", "Lean", "Lake"} and not s.split(".")[0].startswith("Fvdep"))
        if not valid:
            refuse(path + [i], "bad_value")
        out.append(s)
    if not adapter:
        for i, s in enumerate(out):
            if s in out[:i]:
                refuse(path + [i], "bad_value")
    return out


def validate_entry(t: Tree, module_id: str, path: list[str | int]) -> Manifest:
    d = members(t, path)
    differential = "evidence" in d
    if differential:
        string_value(d["evidence"], path + ["evidence"], lambda s: s == "differential")
    required = DIFF if differential else PROOF
    forbidden = (PROOF - {"version"}) if differential else {"adapter"}
    keys(d, KNOWN, required, path, forbidden)
    result: Manifest = {"id": module_id, "kind": "differential" if differential else "proof", "shape": None,
                        "impl": None, "proof": None, "adapter": None, "impl_modules": [], "proof_modules": []}
    for key in sorted(d, key=lambda x: x.encode()):
        p = path + [key]
        if key == "evidence":
            continue
        if key == "version":
            result[key] = string_value(d[key], p, lambda s: len(s.encode()) <= CAP and VERSION.fullmatch(s) is not None)
        elif key == "shape":
            result[key] = string_value(d[key], p, lambda s: s in {"fn", "abi"})
        elif key in {"impl", "proof"}:
            result[key] = string_value(d[key], p, lambda s: len(s.encode()) <= 1024 and NAME.fullmatch(s) is not None)
        elif key in {"impl_modules", "proof_modules", "adapter"}:
            result[key] = list_value(d[key], p, key == "adapter")
    for name in result["impl_modules"]:
        if name in result["proof_modules"]:
            refuse(path, "in_both_lists", name=name)
    return result


def wire(m: Manifest) -> Manifest:
    return {"library": m["library"], "policy": m["policy"], "modules": [
        {"decl": {k: v for k, v in e.items() if k not in {"impl_modules", "proof_modules"}},
         "impl_modules": e["impl_modules"], "proof_modules": e["proof_modules"]} for e in m["modules"]]}


def validate(t: Tree) -> dict[str, Any]:
    try:
        d = members(t, [])
        if "schema" not in d:
            refuse(["schema"], "missing_field")
        schema = as_kind(d["schema"], "int", ["schema"], "integer")
        if schema != 1:
            refuse(["schema"], "bad_value")
        keys(d, ROOT, {"schema", "library"}, [])
        result: Manifest = {"library": None, "policy": "required", "modules": []}
        for key in sorted(d, key=lambda x: x.encode()):
            if key == "schema":
                continue
            value = members(d[key], [key])
            if key == "library":
                keys(value, {"commit"}, {"commit"}, [key])
                result[key] = string_value(value["commit"], [key, "commit"], lambda s: re.fullmatch(r"[0-9a-f]{40}", s, re.ASCII) is not None)
            elif key == "policy":
                keys(value, {"proof"}, set(), [key])
                if "proof" in value:
                    result[key] = string_value(value["proof"], [key, "proof"], lambda s: s in {"required", "development"})
            elif key == "modules":
                for name in sorted(value, key=lambda x: x.encode()):
                    p: list[str | int] = [key, name]
                    if len(name.encode()) > CAP or ID.fullmatch(name) is None:
                        refuse(p, "bad_value")
                    result[key].append(validate_entry(value[name], name, p))
        return {"ok": wire(result)}
    except Refusal as e:
        return {"error": e.value}


def canonical(m: Manifest) -> bytes:
    lines = ["schema = 1", "", "[library]", f"commit = {basic(m['library'])}", "", "[policy]", f"proof = {basic(m['policy'])}"]
    for e in sorted(m["modules"], key=lambda x: x["id"].encode()):
        lines += ["", f"[modules.{basic(e['id'])}]", f"version = {basic(e['version'])}"]
        if e["kind"] == "differential":
            lines += ['evidence = "differential"']
        for key in ["shape", "impl_modules", "proof_modules", "impl", "proof", "adapter"]:
            value = e[key]
            if value is None or (key in {"impl_modules", "proof_modules"} and e["kind"] == "differential"):
                continue
            rendered = "[" + ", ".join(basic(s) for s in value) + "]" if isinstance(value, list) else basic(value)
            lines.append(f"{key} = {rendered}")
    return ("\n".join(lines) + "\n").encode()


def manifest_tree(m: Manifest) -> Tree:
    out = trees({"schema": 1, "library": {"commit": m["library"]}, "policy": {"proof": m["policy"]}})
    if m["modules"]:
        pairs = []
        for e in m["modules"]:
            entry: dict[str, Any] = {"version": e["version"]}
            if e["kind"] == "differential":
                entry["evidence"] = "differential"
                entry["adapter"] = e["adapter"]
            else:
                for key in ["shape", "impl_modules", "proof_modules", "impl", "proof"]:
                    entry[key] = e[key]
            pairs.append([e["id"], trees(entry)])
        out["v"].append(["modules", node("tbl", pairs)])
    return out


def utf8_offset(b: bytes) -> int | None:
    try:
        b.decode("utf-8")
        return None
    except UnicodeDecodeError as e:
        return e.start


def text_stage(b: bytes) -> dict[str, Any]:
    if len(b) > CAP:
        return {"error": {"kind": "too_large"}}
    if b.startswith(b"\xef\xbb\xbf"):
        return {"error": {"kind": "bom"}}
    offset = utf8_offset(b)
    return {"ok": b.decode()} if offset is None else {"error": {"kind": "utf8", "offset": offset}}


def proof_entry(name: str = "base64.encode", **changes: Any) -> Manifest:
    return {"id": name, "version": "1.0.0", "kind": "proof", "shape": "fn", "impl": "Impl.encode", "proof": "Proof.encode_eq",
            "adapter": None, "impl_modules": ["Impl"], "proof_modules": ["Proof"], **changes}


def diff_entry(name: str = "base64.decode", **changes: Any) -> Manifest:
    return {"id": name, "version": "1.0.0", "kind": "differential", "shape": None, "impl": None, "proof": None,
            "adapter": ["python3", "impl/decode.py"], "impl_modules": [], "proof_modules": [], **changes}


def manifest(entries: list[Manifest] | None = None, policy: str = "required", commit: str = COMMIT) -> Manifest:
    return {"library": commit, "policy": policy, "modules": sorted(entries or [], key=lambda e: e["id"].encode())}


@dataclass
class Case:
    id: str
    coverage: str
    request: dict[str, Any]
    expected: Any
    method: str = "example"
    check: str = "exact"
    note: str = ""


def cases(seed: int) -> list[Case]:
    out: list[Case] = []
    rng = random.Random(seed)

    def add(case_id: str, row: str, op: str, expected: Any, method: str = "example", check: str = "exact", note: str = "", **request: Any) -> None:
        out.append(Case(case_id, row, {"op": op, **request}, expected, method, check, note))

    def text(name: str, b: bytes, row: str = "T1-textstage") -> None:
        add(name, row, "text", text_stage(b), "oracle", hex=b.hex())

    def val(name: str, t: Tree, row: str, method: str = "oracle") -> None:
        add(name, row, "validate", validate(t), method, "schema", tree=t)

    def read(name: str, text_value: str, row: str, method: str = "oracle") -> None:
        t = trees(tomllib.loads(text_value))
        expected = validate(t)
        if "error" in expected:
            expected = {"error": {"stage": "schema", "error": expected["error"]}, "code": "schema"}
        add(name, row, "read", expected, method, "read", hex=text_value.encode().hex())

    def parsed(name: str, source: str, row: str = "T1-ofLake") -> None:
        expected = {"tree": trees(tomllib.loads(source))}
        add(name + ".convert", row, "parse", expected, "oracle", "tree", text=source)

    add("T.maxBytes", "T1-size", "max", {"max": CAP})
    base_text = canonical(manifest()).decode()
    base_tree = manifest_tree(manifest([proof_entry()]))
    diff_tree = manifest_tree(manifest([diff_entry()]))
    for size in [0, 1, 65_535, 65_536, 65_537, 65_538]:
        b = b" " * size
        text(f"T.text.size.{size}", b, "T1-size")
    at_cap = base_text + "#" + "x" * (CAP - len(base_text.encode()) - 2) + "\n"
    assert len(at_cap.encode()) == CAP
    read("T.read.size.exact", at_cap, "T1-size")
    add("T.read.size.over", "T1-size", "read", {"error": {"stage": "text", "text": {"kind": "too_large"}}, "code": "schema"}, check="read", hex=(at_cap + " ").encode().hex())
    for suffix in [b"", b"schema = 1", b"\xff", b"\xef\xbb\xbf"]:
        text(f"T.bom.{suffix.hex() or 'empty'}", b"\xef\xbb\xbf" + suffix, "T1-bom")
    text("T.order.size-before-bom-utf8", b"\xef\xbb\xbf\xff" + b" " * CAP, "T1-textstage")
    for b in [b"", b"abc", "α😀\ufffe\U0010ffff".encode(), b"a\xef\xbb\xbfb", b"\0\r\n\t"]:
        text(f"T.text.valid.{b.hex() or 'empty'}", b)
    text("T.text.multibyte.exact", "😀".encode() * (CAP // 4), "T1-size")
    text("T.text.multibyte.over-truncated", "😀".encode() * (CAP // 4) + b"\xc2", "T1-textstage")
    add("T.utf8.leading-bom-is-valid", "T1-utf8", "utf8", {"offset": None}, "oracle", hex="efbbbf")
    invalids = [b"\xc0\x80", b"\xc1\xbf", b"\xe0\x80\x80", b"\xf0\x80\x80\x80", b"\xed\xa0\x80", b"\xed\xbf\xbf",
                b"\xf4\x90\x80\x80", b"\xf5\x80\x80\x80", b"\xff", b"\x80", b"\xbf", b"\xc2", b"\xe0\xa0", b"\xf0\x90\x80",
                b"\xc2A", b"\xe1\x80A", b"\xf0\x90A\x80", b"\xe2\x82", b"\xe1\x80\xff\xc0\x80"]
    for i, suffix in enumerate(invalids):
        for prefix in [b"", "aé😀".encode()]:
            b = prefix + suffix
            suffix_id = "prefixed" if prefix else "bare"
            add(f"T.utf8.invalid.{i}.{suffix_id}", "T1-utf8", "utf8", {"offset": utf8_offset(b)}, "oracle", hex=b.hex())
            text(f"T.text.invalid.{i}.{suffix_id}", b, "T1-utf8")
    for i in range(256):
        b = bytes([i])
        add(f"T.utf8.byte.{i:02x}", "T1-utf8", "utf8", {"offset": utf8_offset(b)}, "oracle", hex=b.hex())
    for i in range(160):
        b = rng.randbytes(rng.randrange(0, 24))
        if i % 3 == 0:
            b = "é😀".encode() + b
        add(f"T.utf8.generated.{i:03}", "T1-utf8", "utf8", {"offset": utf8_offset(b)}, "generator", hex=b.hex())
    for scalar in [0, 127, 128, 2047, 2048, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF]:
        b = chr(scalar).encode()
        add(f"T.utf8.scalar.{scalar:x}", "T1-utf8", "utf8", {"offset": None}, "oracle", hex=b.hex())
        text(f"T.text.scalar.{scalar:x}", b)

    bad_syntax = {"question": "?", "line2": "\n?", "array": "schema = [1,", "escape": 'schema = "\\q"',
                  "missing-value": "schema =\n", "control": 'x = "a\x1bb"', "unterminated": 'x = "unterminated'}
    duplicates = {"scalar": "schema = 1\nschema = 1\n", "quoted-alias": 'schema = 1\n"schema" = 2\n',
                  "table": "[library]\ncommit = 'a'\n[library]\ncommit = 'b'\n",
                  "dotted": "library.commit = 'a'\nlibrary.commit = 'b'\n",
                  "inline": "library = {commit='a', commit='b'}\n",
                  "redefined": "library = 'a'\n[library]\ncommit = 'b'\n",
                  "inline-extend": "library = {commit='a'}\nlibrary.extra = 1\n"}
    for row, fixtures in [("T1-syntax", bad_syntax), ("T1-dupkeys", duplicates)]:
        for name, source in fixtures.items():
            try:
                tomllib.loads(source)
            except tomllib.TOMLDecodeError:
                pass
            else:
                raise AssertionError(f"oracle fixture is not malformed: {name}")
            add(f"T.parse.{name}", row, "parse", {"syntax": "Lake first error"}, "oracle", "syntax", text=source)
            add(f"T.read.syntax.{name}", row, "read", {"syntax": "Lake first error", "code": "schema"}, "oracle", "syntax", hex=source.encode().hex())
    for name, source in {
        "open-arrays": "x=" + "[" * (CAP - 2),
        "closed-arrays": "x=" + "[" * ((CAP - 3) // 2) + "0" + "]" * ((CAP - 3) // 2),
        "inline-open": "x=" + "{a=" * ((CAP - 2) // 3),
        "array-tables": "[[a]]\n" * (CAP // 6),
    }.items():
        source += " " * (CAP - len(source.encode()))
        assert len(source.encode()) == CAP
        add(f"T.worst.{name}", "T1-worst", "read", {"outcome": "parse or schema refusal; process survives"}, check="safe", hex=source.encode().hex())
    add("T.message.control", "T1-worst", "error_code", {"code": "schema", "line": 7, "col": 3, "escaped": "\x1b\x00\x7f"}, check="render", kind="syntax", line=7, col=3, message="bad \x1b\0\x7f token")

    for name in [["anonymous"], ["num", ["anonymous"], 0], ["str", ["str", ["anonymous"], "a"], "b"],
                 ["str", ["num", ["anonymous"], 3], "x"]]:
        for nested in [False, True]:
            n = len(out)
            add(f"T.oflake.badkey.{n}", "T1-ofLake", "oflake_key", {"name": name}, name=name, nested=nested)
    for key in ["", "abc", "a.b", "é", "quote\"slash\\", "\0"]:
        add(f"T.oflake.stringkey.{len(out)}", "T1-ofLake", "oflake_key", {"tree": node("tbl", [[key, node("str", "payload")]])}, "oracle", "tree", name=["str", ["anonymous"], key], nested=False)
    for source in ["z=1\ny=2\nx=3\n", 'a.b.c = [3,1,2]\n"a.b" = ["z", "a", "z"]\n',
                   'root = { nested = { v = true }, arr = [3, "x", false, 2.5, 1979-05-27T07:32:00Z] }\n',
                   '[[a]]\nx=1\n[[a]]\nx=2\n', 'x=1979-05-27\ny=07:32:00\nz=1979-05-27T07:32:00-07:00\n']:
        parsed(f"T.lake.hand.{len(out)}", source)
    for kind in ["bom", "too_large", "utf8", "schema", "key"]:
        kwargs: dict[str, Any] = {"kind": kind, "offset": 19, "name": ["num", ["anonymous"], 8]}
        expected = {"code": "internal" if kind == "key" else "schema"}
        add(f"T.read.code.{kind}", "T1-readpath", "error_code", expected, check="code", **kwargs)
    for b in [b"\xff", b"\xef\xbb\xbf", b"\xef\xbb\xbf\xff", b"\xff" + b" " * CAP]:
        add(f"T.read.text.{len(out)}", "T1-readpath", "read", {"error": {"stage": "text", "text": text_stage(b)["error"]}, "code": "schema"}, "oracle", "read", hex=b.hex())
    read("T.read.empty-policy", 'schema=1\n[library]\ncommit="' + COMMIT + '"\n[policy]\n', "T1-readpath")

    kinds = [node("str", ""), node("int", 0), node("bool", False), node("arr", []), node("tbl", []), node("other", "float"), node("other", "datetime")]
    for i, t in enumerate(kinds):
        if t["t"] != "tbl":
            val(f"T.root.kind.{i}", t, "T3-root")
    val("T.schema.missing", set_member(base_tree, ["schema"], None), "T3-schema")
    for i, t in enumerate(kinds + [node("int", -1), node("int", 2), node("int", 2**64)]):
        val(f"T.schema.value.{i}", set_member(base_tree, ["schema"], t), "T3-schema")
    val("T.root.unknown", set_member(base_tree, ["z"], node("int", 1)), "T3-root")
    two_unknown = set_member(set_member(base_tree, ["é"], node("int", 1)), ["z"], node("int", 2))
    val("T.root.unknown-byte-order", two_unknown, "T3-root")
    val("T.root.missing-library", set_member(base_tree, ["library"], None), "T3-root")
    for key in ["library", "policy", "modules"]:
        row = {"library": "T3-library", "policy": "T3-policy", "modules": "T3-modules-key"}[key]
        for i, t in enumerate(kinds):
            if t["t"] != "tbl":
                val(f"T.{key}.table-kind.{i}", set_member(base_tree, [key], t), row)
    for source in ["", "0" * 39, "a" * 41, "A" * 40, "g" * 40, "é" * 20, "\0" * 40, "0" * 40 + "\n"]:
        val(f"T.commit.bad.{len(out)}", set_member(base_tree, ["library", "commit"], node("str", source)), "T3-library")
    for i, t in enumerate(kinds):
        if t["t"] != "str":
            val(f"T.commit.kind.{i}", set_member(base_tree, ["library", "commit"], t), "T3-library")
    val("T.library.unknown-before-missing", set_member(set_member(base_tree, ["library", "commit"], None), ["library", "a"], node("int", 0)), "T3-library")
    val("T.library.missing-commit", set_member(base_tree, ["library", "commit"], None), "T3-library")
    for v in ["required", "development", "", "Required", "proof", "required\n"]:
        val(f"T.policy.value.{len(out)}", set_member(base_tree, ["policy", "proof"], node("str", v)), "T3-policy")
    for i, t in enumerate(kinds):
        if t["t"] != "str":
            val(f"T.policy.kind.{i}", set_member(base_tree, ["policy", "proof"], t), "T3-policy")
    val("T.policy.absent", set_member(base_tree, ["policy"], None), "T3-policy")
    val("T.policy.empty", set_member(base_tree, ["policy"], table()), "T3-policy")
    val("T.policy.unknown", set_member(base_tree, ["policy", "z"], node("str", "x")), "T3-policy")
    for name in ["a.b", "base64.decode_url", "a0.b1_c2", "A.b", "a.B", "a.1b", "a.b_1c", "a.b__c", "a.b_", "a_b.c", "a.b.c", "a-b.c", "", "a.é", "a.b\0", "a.b ", "a.b/", "a.b'", "a.b" + "x" * (CAP - 3), "a.b" + "x" * (CAP - 2)]:
        t = set_member(base_tree, ["modules"], node("tbl", [[name, next(v for k, v in next(v for k, v in base_tree["v"] if k == "modules")["v"] if k == "base64.encode")]]))
        val(f"T.module-id.{len(out)}", t, "T3-modules-key")
    unordered = manifest_tree(manifest([proof_entry("z.z"), diff_entry("a.a"), proof_entry("m.m")]))
    next(v for k, v in unordered["v"] if k == "modules")["v"].reverse()
    val("T.modules.sort", unordered, "T3-modules-key")
    for i, pairs in enumerate([[["z.z", table()], ["a.a", node("int", 0)]],
                               [["z.z", node("int", 0)], [".bad", table()]],
                               [["z.z", table()], ["a.a", table()]]]):
        val(f"T.modules.error-key-order.{i}", set_member(base_tree, ["modules"], node("tbl", pairs)), "T3-modules-key")
    for i, t in enumerate(kinds + [node("str", "proof"), node("str", "Differential"), node("str", "differential")]):
        val(f"T.evidence.value.{i}", set_member(base_tree, ["modules", "base64.encode", "evidence"], t), "T3-evidence")
    val("T.evidence.absent-proof", base_tree, "T3-evidence")

    for t, name, required, forbidden in [(base_tree, "base64.encode", PROOF, {"adapter"}), (diff_tree, "base64.decode", DIFF - {"evidence"}, PROOF - {"version"})]:
        for key in sorted(required):
            val(f"T.entry.{name}.missing.{key}", set_member(t, ["modules", name, key], None), "T3-entry-keys")
        for key in sorted(forbidden):
            val(f"T.entry.{name}.forbidden.{key}", set_member(t, ["modules", name, key], node("bool", False)), "T3-entry-keys")
        val(f"T.entry.{name}.unknown", set_member(t, ["modules", name, "zzz"], node("int", 0)), "T3-entry-keys")
        for i, wrong in enumerate(kinds):
            if wrong["t"] != "tbl":
                val(f"T.entry.{name}.kind.{i}", set_member(t, ["modules", name], wrong), "T3-entry-keys")
    for key in ["version", "shape", "impl", "proof"]:
        for i, t in enumerate(kinds):
            if t["t"] != "str":
                val(f"T.field.{key}.kind.{i}", set_member(base_tree, ["modules", "base64.encode", key], t), "T3-values")
    values = {
        "version": ["0.0.0", "10.20.30", "01.0.0", "1.00.0", "1.0.01", "v1.0.0", "1.0", "1.0.0.0", "1.0.0-alpha", "1.0.0+build", "+1.0.0", "1.-1.0", "１.0.0", "1.0.0\n", "", "9" * (CAP - 4) + ".0.0", "9" * (CAP - 3) + ".0.0"],
        "shape": ["fn", "abi", "", "ABI", "fn\0"],
        "impl": ["a", "_A.x'", "Lean.x", "Init.x", "a" * 1024, "a" * 1025, "", "1x", ".x", "x.", "x..y", "x-y", "x y", "x\0", "x\x7f", "é"],
        "proof": ["p", "P.eq'", "FvdepProofs.eq", "p" * 1024, "p" * 1025, "", "3p", "P..eq", "p\n"],
    }
    for key, xs in values.items():
        for i, s in enumerate(xs):
            val(f"T.field.{key}.value.{i}", set_member(base_tree, ["modules", "base64.encode", key], node("str", s)), "T3-values")
    module_names = ["A", "_A.B'", "a" * 256, "a" * 257, "Init", "Init.X", "Std", "Lean.Parser", "Lake.X", "Fvdep", "FvdepWhatever.X", "FvdepCore.X", "init", "LeanX", "Lakehouse.X", "x.Init", "x.Fvdep", "_", "A''", "", "1A", "A.1B", ".A", "A.", "A..B", "A-B", "A/B", "A B", "é", "A\0", "A\n"]
    for key in ["impl_modules", "proof_modules"]:
        for i, t in enumerate(kinds):
            val(f"T.list.{key}.kind-or-empty.{i}", set_member(base_tree, ["modules", "base64.encode", key], t), "T3-lists")
        for i, name in enumerate(module_names):
            val(f"T.list.{key}.name.{i}", set_member(base_tree, ["modules", "base64.encode", key], trees([name])), "T3-lists")
        for i, xs in enumerate([["Z", "A", "Z"], ["A", "A", "B", "B"], ["Z", "A", "B"], ["A", "A", "1bad"], ["1bad", 3], ["Valid", 3, ""], ["X", "Y", "X", "Y"]]):
            val(f"T.list.{key}.order.{i}", set_member(base_tree, ["modules", "base64.encode", key], trees(xs)), "T3-lists")
    for i, t in enumerate(kinds):
        val(f"T.adapter.kind-or-empty.{i}", set_member(diff_tree, ["modules", "base64.decode", "adapter"], t), "T3-adapter")
    for i, xs in enumerate([[""], ["run", ""], ["run", "run", ""], ["\0"], ["run", "x\0y"], ["r" * CAP], ["r" * (CAP + 1)], ["run", "é" * (CAP // 2)], ["run", "é" * (CAP // 2) + "x"], ["run", True], ["run", "\x01\t\r\n\x7f"]]):
        val(f"T.adapter.value.{i}", set_member(diff_tree, ["modules", "base64.decode", "adapter"], trees(xs)), "T3-adapter")
    for i, (left, right) in enumerate([(["Z", "A"], ["A", "Z"]), (["Z", "A"], ["P", "A"]), (["A"], ["P"]), (["A", "A"], ["A"]), (["A"], ["A", "1bad"])]):
        t = set_member(set_member(base_tree, ["modules", "base64.encode", "impl_modules"], trees(left)), ["modules", "base64.encode", "proof_modules"], trees(right))
        val(f"T.overlap.{i}", t, "T3-overlap")
    for path in [[], ["library"], ["policy"], ["modules"], ["modules", "base64.encode"]]:
        t = copy.deepcopy(base_tree)
        target = t
        for key in path:
            target = next(v for k, v in target["v"] if k == key)
        target["v"] += [["z", node("int", 0)], ["a", node("int", 1)], ["z", node("bool", False)], ["a", node("int", 2)]]
        val(f"T.tree.duplicate.{len(out)}", t, "T3-dup-tree")
    val("T.tree.duplicate-before-schema", node("tbl", [["schema", node("int", 0)], ["schema", node("str", "x")]]), "T3-dup-tree")
    val("T.tree.duplicate-byte-min", node("tbl", [[k, node("int", 1)] for k in ["é", "\U00010000", "\uffff", "z", "é", "z", "\uffff", "\U00010000"]]), "T3-dup-tree")

    mixed = [
        set_member(set_member(base_tree, ["schema"], node("str", "1")), ["aaa"], node("int", 0)),
        set_member(set_member(base_tree, ["library"], None), ["zzz"], node("int", 0)),
        set_member(set_member(base_tree, ["library", "commit"], node("str", "bad")), ["aaa"], node("int", 0)),
        set_member(set_member(base_tree, ["policy"], node("int", 0)), ["library", "commit"], node("str", "bad")),
        set_member(set_member(base_tree, ["modules", "base64.encode", "impl"], None), ["modules", "base64.encode", "adapter"], trees([])),
        set_member(set_member(base_tree, ["modules", "base64.encode", "adapter"], trees([])), ["modules", "base64.encode", "zzz"], node("int", 0)),
        set_member(set_member(diff_tree, ["modules", "base64.decode", "adapter"], None), ["modules", "base64.decode", "shape"], node("str", "fn")),
        set_member(set_member(base_tree, ["modules", "base64.encode", "evidence"], node("int", 3)), ["modules", "base64.encode", "zzz"], node("int", 0)),
        set_member(set_member(base_tree, ["modules", "base64.encode", "impl_modules"], trees(["A", "A", "1bad"])), ["modules", "base64.encode", "version"], node("str", "bad")),
    ]
    for i, t in enumerate(mixed):
        val(f"T.order.mixed.{i}", t, "T3-order")
        rev = copy.deepcopy(t)
        def reverse_tables(x: Tree) -> None:
            if x["t"] == "tbl":
                x["v"].reverse()
                for _, child in x["v"]:
                    reverse_tables(child)
            elif x["t"] == "arr":
                for child in x["v"]:
                    reverse_tables(child)
        reverse_tables(rev)
        assert validate(rev) == validate(t)
        val(f"T.order.permuted.{i}", rev, "T3-order", "generator")
    for i in range(96):
        t = copy.deepcopy(base_tree if i % 2 else diff_tree)
        entry_id = "base64.encode" if i % 2 else "base64.decode"
        for _ in range(rng.randrange(1, 5)):
            choices = [(["schema"], rng.choice(kinds)), (["z"], node("str", "unknown")), (["library", "commit"], node("str", "bad")),
                       (["modules", entry_id, "adapter"], trees(["", "a\0"])), (["modules", entry_id, "version"], node("int", 2)),
                       (["modules", entry_id, "evidence"], node("str", "proof")), (["modules", entry_id, "zzz"], node("bool", True))]
            path, value = rng.choice(choices)
            t = set_member(t, path, value)
        val(f"T.order.generated.{i:03}", t, "T3-order", "generator")

    for path in [[], ["schema"], ["modules", "base64.encode", "impl_modules", 1], ["a-b", "0", "_"], ["", "a.b", "é", 0],
                 ['"', "\\", "a b", "\x1b", "\x7f"], ["a", 0, "b", 12], ["\U0001f600", "\ufffe", "\0"]]:
        add(f"T.path.{len(out)}", "T3-paths", "path", {"path": key_path(path)}, "oracle", path=path)
    for key in ["a.b", '"', "a\nb", "é", "\0", "~slash/"]:
        val(f"T.path.unknown.{len(out)}", set_member(base_tree, [key], node("int", 0)), "T3-paths")

    controls = [chr(i) for i in range(1, 32)] + [chr(127)]
    specials = ['"', "\\", "é", "😀", "\ufffe", "\uffff", "\U0010ffff", "\u2028", "\u2029", "\ufeff"]
    samples = [manifest(), manifest([proof_entry()]), manifest([diff_entry()]), manifest([proof_entry("z.z", shape="abi"), diff_entry("a.b")], "development")]
    samples += [manifest([diff_entry(adapter=["run", "", c, c + c])]) for c in controls + specials]
    samples += [manifest([diff_entry(adapter=["run", "".join(controls + specials), "", "run"])])]
    for i in range(64):
        entries = []
        for k in range(rng.randrange(0, 7)):
            name = f"pkg{i}.op{k}_test"
            if rng.getrandbits(1):
                entries.append(proof_entry(name, version=f"{rng.randrange(100)}.{rng.randrange(50)}.{rng.randrange(20)}", shape=rng.choice(["fn", "abi"]),
                                           impl_modules=[f"Impl{i}.Part{k}", f"Extra{k}"], proof_modules=[f"Proof{i}.Part{k}"], impl=f"Impl{i}.f{k}", proof=f"Proof{i}.eq{k}"))
            else:
                alphabet = controls + specials + list("aZ09 /_-[]#'")
                args = ["run"] + ["".join(rng.choice(alphabet) for _ in range(rng.randrange(0, 12))) for _ in range(rng.randrange(0, 6))]
                entries.append(diff_entry(name, adapter=args, version=f"{i}.{k}.0"))
        samples.append(manifest(entries, rng.choice(["required", "development"]), "".join(rng.choice("0123456789abcdef") for _ in range(40))))
    for i, m in enumerate(samples):
        encoded = canonical(m)
        source = encoded.decode()
        expected = {"ok": wire(m)}
        assert validate(manifest_tree(m)) == expected
        assert validate(trees(tomllib.loads(source))) == expected
        method = "generator" if i >= 4 + len(controls + specials) + 1 else "oracle"
        row = "T4-escapes" if 4 <= i < 4 + len(controls + specials) + 1 else "T4-layout"
        add(f"T.print.{i:03}", row, "print", {"hex": encoded.hex()}, method, manifest=m)
        add(f"T.toTree.{i:03}", "T5-roundtrip", "tree", {"tree": manifest_tree(m)}, method, manifest=m)
        add(f"T.treeRound.{i:03}", "T5-roundtrip", "tree_round", expected, method, "schema", manifest=m)
        add(f"T.round.{i:03}", "T5-roundtrip", "round", expected, method, "read", manifest=m)
        read(f"T.read.canonical.{i:03}", source, "T5-roundtrip", method)
        parsed(f"T.canonical.{i:03}", source)
        add(f"T.projection.{i:03}", "U2-projection", "projection", {"library": m["library"], "decls": [e["decl"] for e in wire(m)["modules"]]}, method, manifest=m)

    alternatives = [
        f'schema = 0x1\nlibrary.commit = \'{COMMIT}\'\n',
        f'  schema = +1 # comment\nlibrary = {{ commit = "{COMMIT}" }}\npolicy = {{}}\nmodules={{}}\n',
        f'library = {{commit = \'{COMMIT}\'}}\nschema = 1\npolicy.proof = "development"\n',
        f'"schema" = 1\n["library"]\n"commit" = \'{COMMIT}\'\n',
        base_text.replace("\n", "\r\n"),
        base_text + '[modules."base64.encode"]\nversion=\'1.0.0\'\nshape=\'abi\'\nimpl_modules=[\'Z\',\'A\',]\nproof_modules=[\'P\']\nimpl=\'Z.f\'\nproof=\'P.eq\'\n',
        f'schema=1\nlibrary.commit="{COMMIT}"\nmodules."base64.decode"={{version="1.0.0", evidence="differential", adapter=["run", "", "\\u00E9"]}}\n',
        base_text + '[modules."base64.decode"]\nversion="1.0.0"\nevidence="differential"\nadapter=["run", """multi\nline""", \'literal\\path\']\n',
        f'schema=1\nlibrary.commit="{COMMIT}"\npolicy.proof="required"\n[modules]\n',
    ]
    invalid_alternatives = [
        "schema = 1.0\n" + f'library.commit="{COMMIT}"\n',
        base_text.replace(f'commit = "{COMMIT}"', "commit = {x=1}"),
        base_text + '[[modules]]\nversion="1.0.0"\n',
        base_text.replace('proof = "required"', "proof = 1979-05-27T07:32:00Z"),
        base_text + '[modules."base64.encode"]\nversion=1.0\n',
        base_text.replace(f'commit = "{COMMIT}"', "commit = 1979-05-27"),
    ]
    for i, source in enumerate(alternatives + invalid_alternatives):
        read(f"T.alternative.{i}", source, "T6-altspell")
        parsed(f"T.alternative.{i}", source, "T6-altspell")
    assert len({c.id for c in out}) == len(out)
    return out


def no_raw_controls(detail: str, forbidden: str) -> bool:
    return all(c not in detail for c in forbidden)


def named_detail(actual: dict[str, Any], error: dict[str, Any]) -> str | None:
    detail = actual.get("detail")
    if not isinstance(detail, str) or not detail:
        return "missing refusal detail"
    names = [x for x in error["path"] if isinstance(x, str)]
    if error["name"] is not None:
        names.append(error["name"])
    if names:
        name = names[-1]
        rendered = basic(name)[1:-1]
        if name not in detail and rendered not in detail:
            return f"detail does not name {name!r}"
        controls = "".join(c for c in name if ord(c) < 32 or ord(c) == 127)
        if controls and not no_raw_controls(detail, controls):
            return "raw control character in refusal detail"
    return None


def core(actual: dict[str, Any]) -> dict[str, Any]:
    return {k: v for k, v in actual.items() if k != "detail"}


def check_case(c: Case, actual: dict[str, Any], call: Any) -> str | None:
    if "harness_error" in actual:
        raise RuntimeError(f"{c.id}: {actual}")
    if c.check == "syntax":
        source = c.request.get("text")
        if source is None:
            source = bytes.fromhex(c.request["hex"]).decode()
        ref = call({"op": "lake", "text": source})
        if "error" not in ref or ref["error"].get("stage") != "syntax":
            raise RuntimeError(f"independent Lake syntax control: {ref}")
        err = actual.get("error", {})
        oracle = ref["error"]
        if err != oracle:
            return "syntax payload differs from Lake's first error"
        if c.request["op"] == "read":
            if actual.get("code") != "schema":
                return "syntax public code is not schema"
            detail = actual.get("detail", "")
            position = f"{oracle['line']}:{oracle['col'] + 1}"
            if position not in detail or not detail:
                return "syntax detail lacks its 1-based line:column"
            controls = "".join(chr(i) for i in range(32) if i not in {9, 10, 13}) + "\x7f"
            if not no_raw_controls(detail, controls):
                return "syntax detail contains a raw control character"
        return None
    if c.check == "safe":
        if ("ok" in actual) or ("error" in actual and actual.get("code") == "schema"):
            return None
        return "no parse or schema refusal returned"
    if c.check == "code":
        return None if actual.get("code") == c.expected["code"] else "wrong public code"
    if c.check == "render":
        detail = actual.get("detail", "")
        if actual.get("code") != c.expected["code"]:
            return "wrong public code"
        if f"{c.expected['line']}:{c.expected['col'] + 1}" not in detail:
            return "detail lacks 1-based line:column"
        return None if no_raw_controls(detail, c.expected["escaped"]) else "raw control character in rendered error"
    if c.check == "tree":
        if c.request["op"] == "parse":
            lake = call({"op": "lake", "text": c.request["text"]})
            if "tree" not in lake or sort_tree(lake["tree"]) != sort_tree(c.expected["tree"]):
                return "Lake parser output violates its key/array/scalar assumptions or tomllib denotation"
        if "tree" not in actual or sort_tree(actual["tree"]) != sort_tree(c.expected["tree"]):
            return "tree/array/scalar differs from tomllib (table order ignored)"
        return None
    if core(actual) != c.expected:
        return "observable result differs from independent oracle"
    if c.check == "schema" and "error" in c.expected:
        return named_detail(actual, c.expected["error"])
    if c.check == "read" and c.expected.get("error", {}).get("stage") == "schema":
        return named_detail(actual, c.expected["error"]["error"])
    if c.request["op"] == "text" and c.expected.get("error", {}).get("kind") == "utf8":
        if str(c.expected["error"]["offset"]) not in actual.get("detail", ""):
            return "UTF-8 refusal detail lacks byte offset"
    if c.check == "read" and c.expected.get("error", {}).get("stage") == "text":
        t = c.expected["error"]["text"]
        if t["kind"] == "utf8" and str(t["offset"]) not in actual.get("detail", ""):
            return "read refusal detail lacks UTF-8 byte offset"
    return None


def short(value: Any) -> str:
    text = jdump(value)
    encoded = text.encode()
    if len(encoded) <= 1800:
        return text
    return f"sha256:{hashlib.sha256(encoded).hexdigest()} bytes:{len(encoded)} prefix:{text[:160]!r} [abbreviated]"


def selfcheck() -> None:
    assert basic('"\\\b\t\n\f\r\x01\x1f\x7fé😀') == '"\\"\\\\\\b\\t\\n\\f\\r\\u0001\\u001F\\u007Fé😀"'
    assert key_path(["modules", "base64.encode", "impl_modules", 1]) == 'modules."base64.encode".impl_modules[1]'
    assert utf8_offset(b"a\xc2A\xff") == 1
    assert text_stage(b"\xef\xbb\xbf\xff")["error"]["kind"] == "bom"
    assert validate(table())["error"] == {"kind": "missing_field", "path": ["schema"], "expected": None, "name": None}
    assert validate(trees({"schema": True}))["error"]["kind"] == "wrong_type"
    assert validate(trees({"schema": 1, "library": {"commit": COMMIT}, "policy": {}})) == {"ok": wire(manifest())}
    assert validate(manifest_tree(manifest([proof_entry(), diff_entry()]))) == {"ok": wire(manifest([proof_entry(), diff_entry()]))}
    try:
        tomllib.loads('x="\\q"')
    except tomllib.TOMLDecodeError:
        pass
    else:
        raise AssertionError("tomllib negative control")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--driver", type=Path)
    parser.add_argument("--report", type=Path, default=Path("tests/manifest/.results/latest.tsv"))
    parser.add_argument("--case")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--oracle-only", action="store_true")
    parser.add_argument("--label", default="stubG")
    args = parser.parse_args()
    seed = int(os.environ.get("FVDEP_TEST_SEED", str(SEED)), 0)
    selfcheck()
    all_cases = cases(seed)
    print(f"SEED {seed} (0x{seed:x}); CASES {len(all_cases)}; ORACLES T3/T4/Python UTF-8/tomllib", flush=True)
    if args.list:
        for c in all_cases:
            print(f"{c.id}\t{c.coverage}\t{c.method}")
        return 0
    if args.oracle_only:
        print("ORACLE PASS: positive + negative controls; generated canonical texts independently parsed + validated")
        return 0
    selected = [c for c in all_cases if args.case is None or c.id == args.case]
    if not selected:
        parser.error(f"no case: {args.case}")
    if args.driver is None:
        parser.error("--driver is required unless --list or --oracle-only")
    driver = args.driver.resolve()
    rows: list[list[str]] = []
    failures = 0
    start = time.monotonic()
    slow: list[tuple[float, str]] = []
    def call(request: dict[str, Any]) -> dict[str, Any]:
        result = subprocess.run([str(driver)], input=jdump(request) + "\n", text=True, encoding="utf-8", capture_output=True, timeout=90, check=False)
        if result.returncode != 0:
            return {"process_error": result.returncode, "stderr": result.stderr}
        try:
            response = json.loads(result.stdout)
        except json.JSONDecodeError as e:
            raise RuntimeError(f"driver JSON protocol: {result.stdout[:300]!r}; stderr {result.stderr[:300]!r}") from e
        if not isinstance(response, dict):
            raise RuntimeError(f"driver response is not an object: {response!r}")
        return response
    transport_tree = node("tbl", [["x", node("arr", [node("other", "datetime"), node("other", "float"), node("int", -5), node("bool", True)])], ["x", node("str", "é😀\0")]])
    transport_manifest = manifest([proof_entry(), diff_entry(adapter=["run", "", "é😀\n"])])
    transport_hex = bytes(range(256)).hex()
    for request, expected in [({"op": "echo_hex", "hex": transport_hex}, {"hex": transport_hex}),
                              ({"op": "echo_tree", "tree": transport_tree}, {"tree": transport_tree}),
                              ({"op": "echo_manifest", "manifest": transport_manifest}, {"ok": wire(transport_manifest)})]:
        observed = call(request)
        if observed != expected:
            raise RuntimeError(f"harness transport control failed: {short(observed)} != {short(expected)}")
    print("TRANSPORT PASS: all 256 byte values; tagged trees/duplicate keys; typed declarations", flush=True)
    for c in selected:
        before = time.monotonic()
        try:
            actual = call(c.request)
            reason = check_case(c, actual, call)
        except subprocess.TimeoutExpired:
            actual = {"timeout": 90}
            reason = "process timeout"
        elapsed = time.monotonic() - before
        slow.append((elapsed, c.id))
        verdict = "PASS" if reason is None else "FAIL"
        failures += reason is not None
        command = f"tools/vflab-run bash tests/manifest/run.sh --case {c.id}"
        rows.append([c.id, c.coverage, short(c.expected), verdict, command, short(actual), reason or "", f"{elapsed:.6f}", c.method, c.note or "-"])
        if args.case or (verdict == "FAIL" and failures <= 8):
            print(f"{verdict} {c.id}: {reason or 'oracle agrees'}; actual={short(actual)}", flush=True)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    with args.report.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, delimiter="\t", lineterminator="\n")
        writer.writerow(["id", "coverage", "expected", args.label, "command", "output", "reason", "seconds", "method", "notes"])
        writer.writerows(rows)
    print(f"RESULT {len(rows)} cases; {len(rows) - failures} PASS; {failures} FAIL; wall {time.monotonic() - start:.3f}s; report {args.report}")
    print("SLOWEST " + "; ".join(f"{name}={seconds:.3f}s" for seconds, name in sorted(slow, reverse=True)[:5]))
    if not args.case:
        green = args.report.with_name(f"GREEN.T.{args.label}.txt")
        green.write_text("".join(row[0] + "\n" for row in rows if row[3] == "PASS"), encoding="utf-8")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
