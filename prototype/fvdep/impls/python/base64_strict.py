#!/usr/bin/env python3
"""Strict base64 adapter: modules base64.encode@1.0.0 + base64.decode@1.0.0 (standard alphabet only)."""
import sys

ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
VAL = {c: i for i, c in enumerate(ALPHA)}


def encode(bs: bytes) -> str:
    out = []
    for i in range(0, len(bs), 3):
        g = bs[i : i + 3]
        n = int.from_bytes(g.ljust(3, b"\0"), "big")
        chars = [ALPHA[(n >> s) & 63] for s in (18, 12, 6, 0)]
        out.append("".join(chars[: len(g) + 1]).ljust(4, "="))
    return "".join(out)


def decode(s: str) -> bytes | None:
    if len(s) % 4:
        return None
    out = bytearray()
    for i in range(0, len(s), 4):
        g = s[i : i + 4]
        last = i + 4 == len(s)
        pad = len(g) - len(g.rstrip("=")) if last else 0
        if pad > 2 or any(c not in VAL for c in g[: 4 - pad]):
            return None
        n = 0
        for c in g[: 4 - pad]:
            n = n * 64 + VAL[c]
        n <<= 6 * pad
        if pad and n & ((1 << (8 * pad)) - 1):  # unused bits must be zero
            return None
        out += n.to_bytes(3, "big")[: 3 - pad]
    return bytes(out)


for line in sys.stdin:
    op, *args = line.rstrip("\n").split("\t")
    try:
        if op == "encode":
            print(f"ok\t{encode(bytes.fromhex(args[0]))}", flush=True)
        elif op == "decode":
            r = decode(args[0])
            print("err" if r is None else f"ok\t{r.hex()}", flush=True)
        else:
            print("unsupported", flush=True)
    except (ValueError, IndexError):
        print("err", flush=True)
