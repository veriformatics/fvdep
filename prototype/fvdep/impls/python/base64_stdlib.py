#!/usr/bin/env python3
"""base64 adapter wrapping Python's stdlib (`b64decode(validate=True)`).

Kept as the example of a real-world gap: the stdlib accepts non-canonical
input such as `QR==` (unused bits set), which the spec rejects.
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
