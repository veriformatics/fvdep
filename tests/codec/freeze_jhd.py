"""B3-2: freeze every pre-S case, including D; source under test never supplies expected values."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import sys
from pathlib import Path


def load(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return vars(module)


def inventory() -> list[str]:
    api = load('fvdep_codec_suite', 'suite.py')
    s = api['Suite'](0xF7DE3001)
    for name in ['add_json_examples', 'add_json_properties', 'add_boundary_properties', 'add_accessor_cases', 'add_hash_cases']:
        api[name](s)
    load('fvdep_codec_doc_oracle', 'doc_oracle.py')
    load('fvdep_codec_doc_cases', 'doc_cases.py')['add_cases'](s)
    rows = ['id\top\tinput_sha256\texpected_sha256']
    for c in s.cases:
        rows.append('\t'.join([c.id, c.op, hashlib.sha256(c.payload).hexdigest(), hashlib.sha256(c.expected.encode()).hexdigest()]))
    for r in s.relations:
        code = r.check.__code__
        rows.append('\t'.join([r.id, 'relation', hashlib.sha256('\0'.join(r.targets).encode()).hexdigest(),
                               hashlib.sha256(code.co_code + repr(code.co_consts).encode()).hexdigest()]))
    assert len(rows) == 7306
    return rows


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument('--emit', action='store_true')
    p.add_argument('--baseline', type=Path, default=Path(__file__).with_name('FROZEN-JHD.tsv'))
    args = p.parse_args()
    rows = inventory()
    if args.emit:
        for row in rows:
            print('FROZEN\t' + row)
    else:
        assert args.baseline.read_text().splitlines() == rows, 'B3-2 breach: J/H/D inventory changed'
    print('CONTROL frozen-JHD cases=7305 PASS')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
