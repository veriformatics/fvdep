#!/usr/bin/env python3
"""Python binding of the proven Lean base64 (impls/lean, C library `libfvdep_base64.so`) + adapter.

`encode` / `decode` call the Lean code proven equal to base64.encode@1.0.0 / base64.decode@1.0.0.
Build the library first: `lake build` + `ffi/build.sh` in impls/lean.
"""
import ctypes
import os
import sys
from pathlib import Path

_LIB = os.environ.get("FVDEP_BASE64_LIB") or str(
    Path(__file__).resolve().parents[1] / "lean/.lake/build/ffi/libfvdep_base64.so")
_c = ctypes.CDLL(_LIB)
_c.fvdep_b64_encode.restype = ctypes.c_void_p
_c.fvdep_b64_encode.argtypes = [ctypes.c_char_p, ctypes.c_size_t]
_c.fvdep_b64_decode.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8)),
                                ctypes.POINTER(ctypes.c_size_t)]
_c.fvdep_free.argtypes = [ctypes.c_void_p]
if _c.fvdep_init():
    raise RuntimeError("Lean runtime initialization failed")


def encode(data: bytes) -> str:
    p = _c.fvdep_b64_encode(data, len(data))
    try:
        return ctypes.string_at(p).decode()
    finally:
        _c.fvdep_free(p)


def decode(text: str) -> bytes | None:
    out, n = ctypes.POINTER(ctypes.c_uint8)(), ctypes.c_size_t()
    if _c.fvdep_b64_decode(text.encode(), ctypes.byref(out), ctypes.byref(n)):
        return None
    try:
        return bytes(out[: n.value])
    finally:
        _c.fvdep_free(out)


if __name__ == "__main__":
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
