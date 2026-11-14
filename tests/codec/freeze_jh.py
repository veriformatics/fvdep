"""B2-2: byte-level inventory of the unchanged batch-1 cases + relation predicates."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import sys
from pathlib import Path


def inventory() -> list[str]:
    path = Path(__file__).with_name("suite.py")
    spec = importlib.util.spec_from_file_location("fvdep_codec_suite", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    api = vars(module)
    suite = api["Suite"](0xF7DE3001)
    for name in ["add_json_examples", "add_json_properties", "add_boundary_properties", "add_accessor_cases", "add_hash_cases"]:
        api[name](suite)
    rows = ["id\top\tinput_sha256\texpected_sha256"]
    for case in suite.cases:
        rows.append("\t".join([case.id, case.op, hashlib.sha256(case.payload).hexdigest(),
                               hashlib.sha256(case.expected.encode()).hexdigest()]))
    for relation in suite.relations:
        predicate = relation.check.__code__
        expected = predicate.co_code + repr(predicate.co_consts).encode()
        rows.append("\t".join([relation.id, "relation", hashlib.sha256("\0".join(relation.targets).encode()).hexdigest(),
                               hashlib.sha256(expected).hexdigest()]))
    assert len(rows) == 3935
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", action="store_true")
    parser.add_argument("--baseline", type=Path, default=Path(__file__).with_name("FROZEN-JH.tsv"))
    args = parser.parse_args()
    rows = inventory()
    if args.emit:
        for row in rows:
            print("FROZEN\t" + row)
    else:
        baseline = args.baseline.read_text().splitlines()
        assert baseline == rows, "B2-2 breach: batch-1 id/op/input/expected inventory changed"
    print("CONTROL frozen-JH cases=3934 PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
