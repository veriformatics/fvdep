"""Independent RFC 4648 §§3.2–3.5/4/5 and SemVer 2.0.0 §§2/9–11 oracles.

No base64, packaging, semver, or product implementation imports. Whole-type
Version comparison follows docs/library.md, including invalid Ident values.
"""
from __future__ import annotations

import random
import re
from functools import cmp_to_key

SAFE_INTEGER = (1 << 53) - 1
STANDARD = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
URL = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"


def encode(data: bytes, *, url: bool = False) -> str:
    alphabet = URL if url else STANDARD
    out = []
    for offset in range(0, len(data), 3):
        block = data[offset:offset + 3]
        bits = int.from_bytes(block, "big") << (8 * (3 - len(block)))
        digits = [alphabet[(bits >> shift) & 63] for shift in (18, 12, 6, 0)]
        out.extend(digits[:len(block) + 1] + ["="] * (3 - len(block)))
    return "".join(out)


def decode(text: str, *, url: bool = False) -> bytes | None:
    alphabet = URL if url else STANDARD
    if len(text) % 4:
        return None
    out = bytearray()
    for offset in range(0, len(text), 4):
        chunk = text[offset:offset + 4]
        padding = len(chunk) - len(chunk.rstrip("="))
        if padding > 2 or (padding and offset + 4 != len(text)):
            return None
        data = chunk[:4 - padding]
        if any(c not in alphabet for c in data) or "=" in data:
            return None
        value = 0
        for char in data:
            value = value * 64 + alphabet.index(char)
        unused = 2 * padding
        if value & ((1 << unused) - 1):
            return None
        value >>= unused
        out.extend(value.to_bytes(3 - padding, "big"))
    return bytes(out)


def wire_nat(value: int):
    return value if -SAFE_INTEGER <= value <= SAFE_INTEGER else str(value)


def un_nat(value) -> int:
    return int(value)


def parse(text: str) -> dict | None:
    matched = re.fullmatch(
        r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)"
        r"(?:-([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?"
        r"(?:\+([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?", text, flags=re.ASCII,
    )
    if matched is None:
        return None
    major, minor, patch, pre, build = matched.groups()
    identifiers = []
    for token in pre.split(".") if pre is not None else []:
        if all("0" <= c <= "9" for c in token):
            if len(token) > 1 and token[0] == "0":
                return None
            identifiers.append({"num": wire_nat(int(token))})
        else:
            identifiers.append({"alnum": token})
    return {"build": build.split(".") if build is not None else [], "major": wire_nat(int(major)),
            "minor": wire_nat(int(minor)), "patch": wire_nat(int(patch)), "pre": identifiers}


def valid_version(text: str) -> dict:
    value = parse(text)
    assert value is not None, f"invalid reference fixture: {text!r}"
    return value


def sign(a, b) -> int:
    return (a > b) - (a < b)


def compare(a: dict, b: dict) -> str:
    for field in ("major", "minor", "patch"):
        order = sign(un_nat(a[field]), un_nat(b[field]))
        if order:
            return "gt" if order > 0 else "lt"
    ap, bp = a["pre"], b["pre"]
    if not ap or not bp:
        order = sign(not ap, not bp)
        return ("lt", "eq", "gt")[order + 1]
    for ai, bi in zip(ap, bp, strict=False):
        if "num" in ai and "num" in bi:
            order = sign(un_nat(ai["num"]), un_nat(bi["num"]))
        elif "num" in ai:
            order = -1
        elif "num" in bi:
            order = 1
        else:
            order = sign(ai["alnum"], bi["alnum"])
        if order:
            return "gt" if order > 0 else "lt"
    return ("lt", "eq", "gt")[sign(len(ap), len(bp)) + 1]


def bytes_domain(rng: random.Random, count: int = 96) -> list[bytes]:
    values = [b"", b"f", b"fo", b"foo", b"foob", b"fooba", b"foobar", b"\0", b"\xff",
              bytes(range(256)), b"\0\xff\0\x80", b"\0" * 257]
    for _ in range(count):
        size = rng.choice([0, 1, 2, 3, 4, 5, 7, 16, 31, 32, 64, rng.randrange(512)])
        values.append(bytes(rng.randrange(256) for _ in range(size)))
    return values


def version_domain(rng: random.Random, count: int = 72) -> list[dict]:
    values = [valid_version(x) for x in (
        "0.0.0", "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta",
        "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0", "1.0.0+build.001",
        "9007199254740992.0.0-9007199254740993",
    )]
    for _ in range(count):
        def nat():
            return wire_nat(rng.choice([0, 1, 2, SAFE_INTEGER, SAFE_INTEGER + 1, rng.randrange(10**30)]))
        values.append({"build": [rng.choice(["", "a", "001", "💡"]) for _ in range(rng.randrange(3))],
                       "major": nat(), "minor": nat(), "patch": nat(),
                       "pre": [({"num": nat()} if rng.randrange(2) else
                                {"alnum": rng.choice(["", "0", "00", "z", "A", "-", "α", "\0", "💡"])})
                               for _ in range(rng.randrange(4))]})
    return values


def shrink_bytes(value: bytes):
    if value:
        yield b""
        yield value[:len(value) // 2]
        yield value[len(value) // 2:]
        yield value[:1]
        yield bytes(len(value))
        for index, byte in enumerate(value):
            yield value[:index] + value[index + 1:]
            if byte:
                yield value[:index] + bytes([byte // 2]) + value[index + 1:]


def shrink_text(value: str):
    if value:
        yield ""
        yield value[:len(value) // 2]
        yield value[len(value) // 2:]
        yield value[:1]
        for index in range(len(value)):
            yield value[:index] + value[index + 1:]


def shrink_version(value: dict):
    for field in ("major", "minor", "patch"):
        if un_nat(value[field]):
            yield value | {field: 0}
            yield value | {field: wire_nat(un_nat(value[field]) // 2)}
    if value["build"]:
        yield value | {"build": []}
    if value["pre"]:
        yield value | {"pre": []}
        yield value | {"pre": value["pre"][:len(value["pre"]) // 2]}
        for index, identifier in enumerate(value["pre"]):
            yield value | {"pre": value["pre"][:index] + value["pre"][index + 1:]}
            smaller = {"num": 0} if "num" in identifier else {"alnum": ""}
            if smaller != identifier:
                pre = list(value["pre"])
                pre[index] = smaller
                yield value | {"pre": pre}


def shrink_pair(pair):
    a, b = pair
    for smaller in shrink_version(a):
        yield (smaller, b)
    for smaller in shrink_version(b):
        yield (a, smaller)


def self_check() -> None:
    vectors = [(b"", ""), (b"f", "Zg=="), (b"fo", "Zm8="), (b"foo", "Zm9v"),
               (b"foob", "Zm9vYg=="), (b"fooba", "Zm9vYmE="), (b"foobar", "Zm9vYmFy")]
    for raw, text in vectors:
        assert encode(raw) == text and decode(text) == raw
    for text in ("Zg", "Zh==", "Zm9=", "=AAA", "AA=A", "Zg==\n", "A===", "===="):
        assert decode(text) is None, text
    order = [valid_version(s) for s in ("1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta",
                               "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0")]
    assert sorted(reversed(order), key=cmp_to_key(lambda a, b: {"lt": -1, "eq": 0, "gt": 1}[compare(a, b)])) == order
    for text in ("v1.0.0", "1.0", "01.0.0", "1.0.0-01", "1.0.0-", "1.0.0+", "1.0.0\n"):
        assert parse(text) is None, text
