"""Record S-only outcomes; older batch records remain frozen."""
from __future__ import annotations
import argparse
import csv
import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('fvdep_sha_record_common', ROOT / 'tests/codec/record.py')
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
compact = vars(module)['compact']
NOTES = {
'S5-nist-short':'All 65 byte-oriented response vectors; Lean + sanitized raw C; official archive bytes and pinned SHA256SUMS.',
'S5-nist-long':'Every published long-message response vector; Lean + sanitized raw C; independent hashlib corpus control.',
'S5-nist-monte':'100 published seed/checkpoint pairs, each 1000 calls; previous published MD, never SUT output, seeds each case; Lean + C.',
'S5-million':'Published million-a digest through one-shot and chunked update; exact digest pinned independently.',
'S5-diff-lengths':'All named padding/block/page/1MiB lengths; sha256sum and hashlib agree before SUT calls; Lean + C.',
'S5-diff-generated':'64 seeded arbitrary-byte messages; external sha256sum agreement; exact whole digest and 32-byte output.',
'S5-update-splits':'Empty/1-byte/random splits, block crossings, one-byte all-256 corpus, million-a streaming and sanitized raw block feeds.',
'S5-branching':'Live IORef aliases keep root + both branches shared; finish root/branches, reuse root, finish branch again; generated prefixes/tails.',
'S5-chunk-arith':'Same core compiled at one-shot=127/chunk=64/total=513; 126/127/128/129 + repeated blocks + 511/512; physical 4GiB inputs not allocated.',
'S5-total-limit':'Approved compositional hook: min oracle at UInt64 edges, saturated total -> squeeze abort; small one-shot/stream aborts; default/small raw refusal with untouched out.',
'S5-ofreader':'First empty chunk ends reads; exact call count; injected IO error after nonempty prefix must remain that error, never a prefix digest.',
'S5-file':'Empty, 1 byte, 1MiB±1, 1MiB, 3MiB+17 + missing file; fresh test-owned files, exact original-byte digest.',
'S5-input-unchanged':'IORef-held aliases observed after forced sha result and after ofReader/update/finish; raw C checks input copy + out guard bytes.',
'S5-concurrent':'Six Tasks: first two share the same ByteArray, others distinct; one shared persistent state; all task hashes/branches match sequential reference.',
'S5-c-harness':'gcc ASan+UBSan, detect_leaks=1/halt_on_error, vectors/Monte/boundaries/generated/default+small/refusals; return and guards observed.',
'H3-digest':'All five literal tags; independent H2 encoder + hashlib; generated distinct path sets, multibyte/verbatim paths and arbitrary file bytes.',
}


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument('log', type=Path)
    p.add_argument('--column', default='stubF')
    args = p.parse_args()
    lines = args.log.read_text().splitlines()
    summary = [x for x in lines if x.startswith('SUMMARY_S ')]
    assert len(summary) == 1 and not any('Traceback' in x for x in lines)
    outcomes: dict[str, tuple[bool, str]] = {}
    clauses: dict[str, tuple[str, list[str]]] = {}
    for line in lines:
        m = re.match(r'^(PASS|FAIL) ((?:S\.|H3\.)\S+)(?: .*)?$', line)
        if m:
            verdict, id = m.groups(); assert id not in outcomes
            outcomes[id] = (verdict == 'PASS', line)
        m = re.match(r'^SCLAUSE (\S+) (\d+F/\d+P) cases=(\S+)$', line)
        if m:
            id, count, names = m.groups(); clauses[id] = (count, names.split(','))
    assert set(clauses) == set(NOTES) and len(clauses) == 16
    count = re.search(r' cases=(\d+) ', summary[0]); assert count is not None
    assert len(outcomes) == int(count.group(1))
    table = ROOT / 'tests/codec/COVERAGE-S.tsv'
    with table.open(newline='') as f:
        reader = csv.DictReader(f, delimiter='\t')
        assert reader.fieldnames is not None
        headers, rows = list(reader.fieldnames), list(reader)
    assert len(rows) == 16 and {r['id'] for r in rows} == set(NOTES)
    if args.column not in headers: headers.append(args.column)
    for r in rows:
        count_text, names = clauses[r['id']]
        passed = sum(outcomes[id][0] for id in names)
        assert count_text == f'{len(names)-passed}F/{passed}P'
        r['cases'] = compact(names)
        r['method'] = ('example;differential(NIST/hashlib)' if r['id'].startswith('S5-nist-') or r['id'] == 'S5-million' else 'example;property(seed);differential(hashlib/sha256sum/min/frame)')
        r[args.column] = count_text
        r['notes'] = NOTES[r['id']]
    with table.open('w', newline='') as f:
        writer = csv.DictWriter(f, headers, delimiter='\t', lineterminator='\n')
        writer.writeheader(); writer.writerows(rows)
    with (ROOT / f'tests/codec/RESULTS.S.{args.column}.tsv').open('w', newline='') as f:
        writer = csv.writer(f, delimiter='\t', lineterminator='\n'); writer.writerow(['id','command','output'])
        writer.writerows((id, 'tools/vflab-run bash tests/codec/run.sh', text) for id, (_,text) in outcomes.items())
    (ROOT / f'tests/codec/GREEN.S.{args.column}.txt').write_text(''.join(id+'\n' for id,(passed,_) in outcomes.items() if passed))
    print(summary[0]); print('RECORDED S rows=16, placeholders=0')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
