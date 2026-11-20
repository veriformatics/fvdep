"""Protocol byte layouts and independent RFC, SemVer and fixture response oracles."""
from __future__ import annotations

import base64
import binascii
import json
import re
from typing import Any

from tests.oracle.harness import NEXT, TRIAL, Op, Result, jtext, need, text_lines

MAX_INT = 2**53 - 1
ERR = {"err": "none"}  # U4 B1/B3, not the adapter's arbitrary err text.


def ok(value: Any) -> dict[str, Any]:
    return {"ok": value}


def number(n: int) -> int | str:
    return n if abs(n) <= MAX_INT else str(n)


def request(op: Op | str, *args: Any) -> bytes:
    return jtext({"args": list(args), "op": op.fn if isinstance(op, Op) else op}) + b"\n"


def expect(result: Result, *expected: dict[str, Any] | None) -> None:
    """None = any one-key invalid reply, with its actual free text canonically encoded."""
    result.code(0)
    need(not result.out or result.out.endswith(b"\n"), "protocol output missing its final LF")
    lines = result.out[:-1].split(b"\n") if result.out else []
    need(len(lines) == len(expected), f"got {len(lines)} replies, expected {len(expected)}; "
         f"stdout={result.out[:300]!r}")
    for idx, (line, ref) in enumerate(zip(lines, expected, strict=True), 1):
        if ref is None:
            found = json.loads(line)
            need(isinstance(found, dict) and set(found) == {"invalid"} and isinstance(found["invalid"], str),
                 f"reply {idx}: expected invalid with reason, got {line[:200]!r}")
            ref = found
        want = jtext(ref)
        need(line == want, f"reply {idx}: got {line[:200]!r} ({len(line)} bytes), "
             f"expected {want[:200]!r} ({len(want)} bytes)")
    need(not any(re.match(r"(?:PROVEN|MATCHED|DELIVERED|NOT DELIVERED)\b", line)
                 for line in text_lines(result.err)), "oracle emitted a proof/delivery verdict")


def trial(version: Op, a: int, b: int, c: int) -> dict[str, Any]:
    if b == c:
        return ERR
    if version == TRIAL:
        coefficients = (1, 2, -3)
    elif version == NEXT:
        coefficients = (5, -7, 11)
    else:
        raise ValueError(f"not a weighted fixture operation: {version.target}")
    return ok(number(sum(v * k for v, k in zip((a, b, c), coefficients, strict=True))))


def encode(data: bytes, url: bool) -> str:
    return (base64.urlsafe_b64encode if url else base64.b64encode)(data).decode("ascii")


def decode(data: str, url: bool) -> dict[str, Any]:
    # Python's decoder allows alternate alphabet symbols and unused nonzero bits in cases
    # where RFC 4648 strict/inverse semantics do not. Exact re-encoding decides canonicality.
    try:
        raw = base64.b64decode(data.encode("ascii"), altchars=b"-_" if url else None, validate=True)
    except (UnicodeEncodeError, binascii.Error):
        return ERR
    return ok(raw.hex()) if encode(raw, url) == data else ERR


def ver(major: int = 0, minor: int = 0, patch: int = 0, *, pre: list[dict[str, Any]] | None = None,
        build: list[str] | None = None) -> dict[str, Any]:
    return {"major": number(major), "minor": number(minor), "patch": number(patch),
            "pre": pre or [], "build": build or []}


SEMVER = re.compile(
    r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)"
    r"(?:-([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?"
    r"(?:\+([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?"
)


def semver_parse(s: str) -> dict[str, Any]:
    m = SEMVER.fullmatch(s)
    if m is None:
        return ERR
    pre = []
    for x in m[4].split(".") if m[4] is not None else []:
        if all("0" <= c <= "9" for c in x):
            if x.startswith("0") and len(x) > 1:
                return ERR
            pre.append({"num": number(int(x))})
        else:
            pre.append({"alnum": x})
    return ok(ver(int(m[1]), int(m[2]), int(m[3]), pre=pre, build=m[5].split(".") if m[5] else []))


def semver_compare(a: dict[str, Any], b: dict[str, Any]) -> str:
    def rank(v: dict[str, Any]) -> tuple[Any, ...]:
        # Equal prefixes sort before longer tuples; release (empty pre) follows prereleases.
        pre = tuple((0, int(x["num"])) if "num" in x else (1, x["alnum"]) for x in v["pre"])
        return int(v["major"]), int(v["minor"]), int(v["patch"]), not pre, pre

    x, y = rank(a), rank(b)
    return "lt" if x < y else "gt" if y < x else "eq"


def crank(n: int) -> int:
    # Closed form of x -> 67x + 1 mod 97, x_0 = 3; independent of the fixture's loop.
    p = pow(67, n, 97)
    return (3 * p + (p - 1) * pow(66, -1, 97)) % 97
