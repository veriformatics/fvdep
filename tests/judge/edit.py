#!/usr/bin/env python3
"""U7 R (contract docs/contracts/U7-judge.md R): byte edits of one real lean4export 3.1.0 export for
J's regression cases (each output stays a well-formed export: X's reader accepts it).

usage: edit.py header IN OUT            — the header line alone
       edit.py drop IN OUT NAME         — without NAME's declaration record
       edit.py swap-value IN OUT D FROM — D's `value` = FROM's (two definitions)
       edit.py collide IN OUT P C       — P's declaration renamed to C, C's own dropped
"""
import json
import sys


def names(lines: list[str]) -> dict[str, int]:
    """Each name record's dotted text → its index (string components only: the edits name those)."""
    comp: dict[int, list[str] | None] = {0: []}
    for line in lines[1:]:
        rec = json.loads(line)
        if "in" not in rec:
            continue
        kind = next(k for k in rec if k != "in")
        val = rec[kind]
        pre = comp.get(val["pre"])
        comp[rec["in"]] = None if pre is None or kind != "str" else pre + [val["str"]]
    return {".".join(c): i for i, c in comp.items() if c}


def decl_of(rec: dict) -> dict | None:
    """A non-inductive declaration record's fields, else None."""
    if len(rec) != 1:
        return None
    kind, val = next(iter(rec.items()))
    return val if kind in ("axiom", "def", "thm", "opaque", "quot") else None


def main() -> int:
    op, src, dst = sys.argv[1], sys.argv[2], sys.argv[3]
    with open(src, encoding="utf-8") as f:
        lines = f.read().splitlines()
    if op == "header":
        out = lines[:1]
    else:
        idx = names(lines)
        recs = [json.loads(line) for line in lines[1:]]
        target = idx[sys.argv[4]]
        if op == "drop":
            out = lines[:1] + [line for line, r in zip(lines[1:], recs, strict=True)
                               if (d := decl_of(r)) is None or d["name"] != target]
            if len(out) != len(lines) - 1:
                raise SystemExit(f"edit.py: {sys.argv[4]}: not exactly one declaration")
        elif op == "swap-value":
            frm = idx[sys.argv[5]]
            value = next(d["value"] for r in recs if (d := decl_of(r)) and d["name"] == frm)
            out = lines[:1]
            hits = 0
            for line, r in zip(lines[1:], recs, strict=True):
                d = decl_of(r)
                if d is not None and d["name"] == target:
                    d["value"] = value
                    hits += 1
                    line = json.dumps(r, ensure_ascii=False, separators=(",", ":"))
                out.append(line)
            if hits != 1:
                raise SystemExit(f"edit.py: {sys.argv[4]}: not exactly one declaration")
        elif op == "collide":
            new = idx[sys.argv[5]]
            out = lines[:1]
            hits = 0
            for line, r in zip(lines[1:], recs, strict=True):
                d = decl_of(r)
                if d is not None and d["name"] == new:
                    continue
                if d is not None and d["name"] == target:
                    d["name"] = new
                    hits += 1
                    line = json.dumps(r, ensure_ascii=False, separators=(",", ":"))
                out.append(line)
            if hits != 1:
                raise SystemExit(f"edit.py: {sys.argv[4]}: not exactly one declaration")
        else:
            raise SystemExit(f"edit.py: unknown edit {op}")
    with open(dst, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
