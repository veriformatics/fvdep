#!/usr/bin/env python3
"""Adapter: CPython's stdlib `base64` (`b64encode`, `b64decode(validate=True)`).

Profile `cpython:base64@3.14`: deviates from base64.decode@1.0.0 by accepting
non-canonical input such as `QR==` (unused bits set).
"""
import base64
import binascii
import sys

for line in sys.stdin:
    op, *args = line.rstrip("\n").split("\t")
    try:
        if op == "encode":
            out = base64.b64encode(bytes.fromhex(args[0])).decode()
        elif op == "decode":
            out = base64.b64decode(args[0], validate=True).hex()
        else:
            print("unsupported", flush=True)
            continue
        print(f"ok\t{out}", flush=True)
    except (binascii.Error, ValueError, IndexError):
        print("err", flush=True)
