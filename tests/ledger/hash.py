#!/usr/bin/env python3
"""L7: rendered hexadecimal hash = the independent toolchain oracle's statement Expr.hash."""

from pathlib import Path
import re
import sys


def main() -> None:
    oracle = Path(sys.argv[1]).read_text()
    document = Path(sys.argv[2]).read_text()
    matches = re.findall(r"ORACLE_HASH_DECIMAL=([0-9]+)", oracle)
    if len(matches) != 1:
        raise SystemExit(f"Expected one independent statement hash, found {len(matches)}.")
    expected = int(matches[0])
    print(f"ORACLE statement hash hexadecimal={expected:x}")
    tokens = re.findall(r"(?i)(?<![0-9a-z])(?:0x)?[0-9a-f]+(?![0-9a-z])", document)
    if not any(int(token, 16) == expected for token in tokens):
        raise SystemExit("The document does not contain the statement's exact hexadecimal hash.")


if __name__ == "__main__":
    main()
