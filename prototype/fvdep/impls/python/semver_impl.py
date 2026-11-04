#!/usr/bin/env python3
"""semver adapter for spec semver@1.0.0 (SemVer 2.0.0 parse + precedence)."""
import re
import sys

NUM = r"0|[1-9][0-9]*"
IDC = r"[0-9A-Za-z-]+"
RX = re.compile(
    rf"({NUM})\.({NUM})\.({NUM})(?:-({IDC}(?:\.{IDC})*))?(?:\+({IDC}(?:\.{IDC})*))?"
)


def parse(s: str):
    m = RX.fullmatch(s)
    if not m:
        return None
    pre = m[4].split(".") if m[4] else []
    if any(p.isdigit() and len(p) > 1 and p[0] == "0" for p in pre):
        return None
    return (int(m[1]), int(m[2]), int(m[3]), pre, m[5])


def render(v) -> str:
    s = f"{v[0]}.{v[1]}.{v[2]}"
    if v[3]:
        s += "-" + ".".join(v[3])
    if v[4]:
        s += "+" + v[4]
    return s


def key_id(p: str):
    return (0, int(p), "") if p.isdigit() else (1, 0, p)


def compare(a, b) -> str:
    ka, kb = a[:3], b[:3]
    if ka != kb:
        return "lt" if ka < kb else "gt"
    pa, pb = a[3], b[3]
    if pa == pb:
        return "eq"
    if not pa or not pb:
        return "gt" if not pa else "lt"
    xa, xb = [key_id(p) for p in pa], [key_id(p) for p in pb]
    return "eq" if xa == xb else ("lt" if xa < xb else "gt")


for line in sys.stdin:
    op, *args = line.rstrip("\n").split("\t")
    if op == "parse" and len(args) == 1:
        v = parse(args[0])
        print("err" if v is None else f"ok\t{render(v)}", flush=True)
    elif op == "compare" and len(args) == 2:
        a, b = parse(args[0]), parse(args[1])
        print("err" if a is None or b is None else f"ok\t{compare(a, b)}", flush=True)
    else:
        print("unsupported", flush=True)
