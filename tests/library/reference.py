"""Independent U4 A4/A5 + B2 oracle. No product code or stdlib base64/semver."""
from __future__ import annotations

import json
import re
from typing import Any

MAX_INT = (1 << 53) - 1
STANDARD = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
URL = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"


def b64encode(data: bytes, url: bool = False) -> str:
    alphabet = URL if url else STANDARD
    bits = [((byte >> shift) & 1) for byte in data for shift in range(7, -1, -1)]
    bits += [0] * ((-len(bits)) % 6)
    chars = []
    for offset in range(0, len(bits), 6):
        value = 0
        for bit in bits[offset:offset + 6]:
            value = value * 2 + bit
        chars.append(alphabet[value])
    chars += ["="] * ((-len(chars)) % 4)
    return "".join(chars)


def b64decode(text: str, url: bool = False) -> bytes | None:
    alphabet = URL if url else STANDARD
    if len(text) % 4:
        return None
    if not text:
        return b""
    pad = len(text) - len(text.rstrip("="))
    if pad > 2:
        return None
    symbols = text[:-pad] if pad else text
    if any(char not in alphabet for char in symbols):
        return None
    bits = []
    for char in symbols:
        value = alphabet.index(char)
        bits.extend((value >> shift) & 1 for shift in range(5, -1, -1))
    unused = (pad * 2) if pad else 0
    if unused and any(bits[-unused:]):
        return None
    if unused:
        bits = bits[:-unused]
    if len(bits) % 8:
        return None
    out = bytearray()
    for offset in range(0, len(bits), 8):
        value = 0
        for bit in bits[offset:offset + 8]:
            value = value * 2 + bit
        out.append(value)
    return bytes(out)


def version(major: int = 1, minor: int = 0, patch: int = 0,
            pre: list[dict[str, Any]] | None = None,
            build: list[str] | None = None) -> dict[str, Any]:
    return {"major": major, "minor": minor, "patch": patch,
            "pre": [] if pre is None else pre, "build": [] if build is None else build}


def numeric(text: str) -> bool:
    return re.fullmatch(r"0|[1-9][0-9]*", text) is not None


def parse(text: str) -> dict[str, Any] | None:
    if not text.isascii():
        return None
    base, plus, build_text = text.partition("+")
    core, dash, pre_text = base.partition("-")
    parts = core.split(".")
    if len(parts) != 3 or not all(numeric(part) for part in parts):
        return None
    pre: list[dict[str, Any]] = []
    if dash:
        for part in pre_text.split("."):
            if re.fullmatch(r"[0-9A-Za-z-]+", part) is None:
                return None
            if part.isdigit():
                if not numeric(part):
                    return None
                pre.append({"num": int(part)})
            else:
                pre.append({"alnum": part})
    build = []
    if plus:
        build = build_text.split(".")
        if any(re.fullmatch(r"[0-9A-Za-z-]+", part) is None for part in build):
            return None
    return version(*(int(part) for part in parts), pre=pre, build=build)


def render(value: dict[str, Any]) -> str:
    text = ".".join(str(value[key]) for key in ("major", "minor", "patch"))
    if value["pre"]:
        text += "-" + ".".join(str(next(iter(ident.values()))) for ident in value["pre"])
    if value["build"]:
        text += "+" + ".".join(value["build"])
    return text


def sign(a: Any, b: Any) -> int:
    return (a > b) - (a < b)


def compare(a: dict[str, Any], b: dict[str, Any]) -> str:
    for key in ("major", "minor", "patch"):
        result = sign(a[key], b[key])
        if result:
            return {-1: "lt", 1: "gt"}[result]
    left, right = a["pre"], b["pre"]
    if bool(left) != bool(right):
        return "lt" if left else "gt"
    for x, y in zip(left, right, strict=False):
        xtag, xval = next(iter(x.items()))
        ytag, yval = next(iter(y.items()))
        if xtag != ytag:
            return "lt" if xtag == "num" else "gt"
        result = sign(xval, yval)
        if result:
            return {-1: "lt", 1: "gt"}[result]
    return {-1: "lt", 0: "eq", 1: "gt"}[sign(len(left), len(right))]


def encode_value(typed: list[Any]) -> Any:
    tag, value = typed
    if tag in ("bytes", "text", "utf16", "ordering"):
        return value
    if tag in ("nat", "int"):
        return value if abs(value) <= MAX_INT else str(value)
    if tag == "version":
        return {"build": value["build"],
                "major": encode_value(["nat", value["major"]]),
                "minor": encode_value(["nat", value["minor"]]),
                "patch": encode_value(["nat", value["patch"]]),
                "pre": [{key: encode_value(["nat", v]) if key == "num" else v}
                        for ident in value["pre"] for key, v in ident.items()]}
    raise ValueError(tag)


def canonical(value: Any) -> bytes:
    # U3 J4 = JSON's shortest spelling, DEL escaped, every other noncontrol scalar raw.
    text = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return text.replace("\x7f", "\\u007f").encode("utf-8")


def request(op: str, args: list[Any]) -> bytes:
    return canonical({"op": op, "args": args})


def wire(value: Any) -> bytes:
    def net(text: str) -> bytes:
        data = text.encode("utf-8")
        return str(len(data)).encode() + b":" + data
    if value is None:
        return b"n"
    if isinstance(value, bool):
        return b"t" if value else b"f"
    if isinstance(value, int):
        return b"i" + str(value).encode() + b";"
    if isinstance(value, str):
        return b"s" + net(value)
    if isinstance(value, list):
        return b"a" + str(len(value)).encode() + b":" + b"".join(wire(x) for x in value)
    if isinstance(value, dict):
        keys = sorted(value, key=lambda key: key.encode("utf-8"))
        return b"o" + str(len(keys)).encode() + b":" + b"".join(
            net(key) + wire(value[key]) for key in keys)
    raise TypeError(type(value))


def unwire(data: bytes) -> Any:
    offset = 0

    def until(stop: bytes) -> bytes:
        nonlocal offset
        end = data.index(stop, offset)
        text = data[offset:end]
        offset = end + 1
        return text

    def net() -> str:
        nonlocal offset
        count = int(until(b":"))
        text = data[offset:offset + count]
        if len(text) != count:
            raise ValueError("short netstring")
        offset += count
        return text.decode("utf-8")

    def read() -> Any:
        nonlocal offset
        tag = data[offset:offset + 1]
        offset += 1
        if tag == b"n":
            return None
        if tag in (b"f", b"t"):
            return tag == b"t"
        if tag == b"i":
            return int(until(b";"))
        if tag == b"s":
            return net()
        if tag == b"a":
            return [read() for _ in range(int(until(b":")))]
        if tag == b"o":
            return {net(): read() for _ in range(int(until(b":")))}
        raise ValueError(f"wire tag {tag!r}")

    value = read()
    if offset != len(data):
        raise ValueError("trailing transport bytes")
    return value
