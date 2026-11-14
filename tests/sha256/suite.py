"""S3/S5 + H3 compiled-boundary tests; hashlib/NIST/sha256sum are independent oracles."""
from __future__ import annotations
import csv
import hashlib
import importlib.util
import os
import random
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('fvdep_sha_oracle', ROOT / 'tests/codec/oracle.py')
assert spec is not None and spec.loader is not None
o = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = o
spec.loader.exec_module(o)
api = vars(o)
Vstr, Varr, Vint = api['string'], api['array'], api['integer']
wire, value_out = api['wire'], api['value_out']
frame, files_value = api['frame'], api['files_value']

@dataclass
class Case:
    id: str
    mode: str
    payload: bytes
    expected: str
    clauses: tuple[str, ...]
    executable: str = 'normal'
    argument: str = ''


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def vectors(path: Path) -> list[tuple[bytes, str]]:
    entries: list[tuple[bytes, str]] = []
    fields: dict[str, str] = {}
    for line in path.read_text().splitlines():
        if ' = ' in line:
            key, val = line.split(' = ', 1)
            fields[key] = val
            if key == 'MD':
                bits = int(fields['Len'])
                assert bits % 8 == 0
                b = bytes.fromhex(fields['Msg'])[:bits // 8]
                assert len(b) * 8 == bits and len(val) == 64 and sha(b) == val
                entries.append((b, val))
                fields = {}
    assert entries
    return entries


def monte() -> list[tuple[bytes, str]]:
    fields = {}
    rows: list[tuple[bytes, str]] = []
    seed = b''
    for line in (ROOT / 'tests/sha256/nist/SHA256Monte.rsp').read_text().splitlines():
        if ' = ' not in line:
            continue
        key, value = line.split(' = ', 1)
        fields[key] = value
        if key == 'Seed':
            seed = bytes.fromhex(value)
        elif key == 'MD':
            assert int(fields['COUNT']) == len(rows)
            x = y = z = seed
            for _ in range(1000):
                x, y, z = y, z, hashlib.sha256(x + y + z).digest()
            assert z.hex() == value
            rows.append((seed, value))
            seed = bytes.fromhex(value)
    assert len(rows) == 100
    return rows


def main() -> int:
    seed = int(os.environ.get('FVDEP_TEST_SEED', '0xF7DE3001'), 0)
    rng = random.Random(seed ^ 0x5A256003)
    print(f'SHA_SEED {seed}', flush=True)
    cases: list[Case] = []
    def add(id: str, mode: str, b: bytes, expected: str, *clauses: str, executable: str = 'normal', argument: str = '') -> None:
        cases.append(Case(id, mode, b, expected, tuple(clauses), executable, argument))
    for name, clause in [('ShortMsg', 'S5-nist-short'), ('LongMsg', 'S5-nist-long')]:
        data = vectors(ROOT / f'tests/sha256/nist/SHA256{name}.rsp')
        for i, (b, md) in enumerate(data):
            add(f'S.nist.{name}.{i:03}', 'S.hash', b, md, clause)
            add(f'S.c.nist.{name}.{i:03}', 'raw', b, 'ok:' + md + ':input=1:guard=1', clause, 'S5-c-harness', executable='c-normal')
    for i, (b, md) in enumerate(monte()):
        add(f'S.nist.monte.{i:03}', 'S.monte', b, md, 'S5-nist-monte')
        add(f'S.c.monte.{i:03}', 'monte', b, 'ok:' + md + ':input=1:guard=1', 'S5-nist-monte', 'S5-c-harness', executable='c-normal')
    print('CONTROL NIST all response digests + 100 Monte checkpoints match hashlib PASS', flush=True)
    million = b'a' * 1_000_000
    assert sha(million) == 'cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0'
    add('S.million.hash', 'S.hash', million, sha(million), 'S5-million')
    parts = [million[i:i+8191] for i in range(0, len(million), 8191)]
    add('S.million.stream', 'S.stream', wire(Varr(Vstr(p.hex()) for p in parts)), sha(million), 'S5-million', 'S5-update-splits')
    named = [0, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 4095, 4096, 1 << 20]
    blobs = [(f'boundary.{n}', rng.randbytes(n), 'S5-diff-lengths') for n in named]
    blobs += [(f'generated.{i:03}', rng.randbytes(rng.randrange(8193)), 'S5-diff-generated') for i in range(64)]
    with tempfile.TemporaryDirectory(prefix='.work.', dir=ROOT / 'tests/sha256') as temp:
        work = Path(temp)
        for label, b, clause in blobs:
            path = work / (label + '.data')
            path.write_bytes(b)
            oracle = subprocess.run(['sha256sum', str(path)], capture_output=True, text=True, check=True).stdout.split()[0]
            assert oracle == sha(b)
            add('S.hash.' + label, 'S.hash', b, oracle, clause)
            add('S.c.' + label, 'raw', b, 'ok:' + oracle + ':input=1:guard=1', clause, 'S5-c-harness', executable='c-normal')
            if len(b) <= 8192:
                chunks = [b'']
                pos = 0
                while pos < len(b):
                    take = rng.choice([1, 1, 2, 55, 63, 64, 65, 127])
                    chunks.append(b[pos:pos+take]); pos += take
                    if rng.randrange(4) == 0: chunks.append(b'')
                chunks.append(b'')
                add('S.split.' + label, 'S.stream', wire(Varr(Vstr(c.hex()) for c in chunks)), oracle, 'S5-update-splits')
                add('S.c.stream.' + label, 'stream', b, 'ok:' + oracle + ':input=1:guard=1', 'S5-update-splits', 'S5-c-harness', executable='c-normal', argument=str(rng.choice([64, 128, 256])))
                add('S.immutable.' + label, 'S.immutable', wire(Vstr(b.hex())), value_out(Varr([Vstr(oracle), Vstr(b.hex())])), 'S5-input-unchanged')
        print(f'CONTROL sha256sum inputs={len(blobs)} match hashlib PASS', flush=True)
        all_bytes = bytes(range(256))
        one_byte = [b''] + [bytes([x]) for x in all_bytes] + [b'']
        add('S.split.one-byte-all', 'S.stream', wire(Varr(Vstr(c.hex()) for c in one_byte)), sha(all_bytes), 'S5-update-splits')
        for i in range(40):
            p, a, b = rng.randbytes(rng.choice([0, 1, 55, 63, 64, 65, 128])), rng.randbytes(rng.randrange(160)), rng.randbytes(rng.randrange(160))
            payload = wire(Varr(Vstr(c.hex()) for c in [p, a, b]))
            expected = value_out(Varr(Vstr(sha(c)) for c in [p, p+a, p+b, p+a, p+a]))
            add(f'S.branch.{i:03}', 'S.branch', payload, expected, 'S5-branching')
            parts = [a, a, b, b, rng.randbytes(65), a]
            expected = value_out(Varr(Varr([Vstr(sha(c)), Vstr(sha(p+c))]) for c in parts))
            add(f'S.tasks.{i:03}', 'S.concurrent', wire(Varr([Vstr(p.hex()), Varr(Vstr(c.hex()) for c in parts)])), expected, 'S5-concurrent', 'S5-branching')
        for i in range(40):
            parts = [rng.randbytes(rng.randrange(1, 100)) for _ in range(rng.randrange(1, 8))]
            insert = rng.randrange(len(parts)+1)
            chunks = parts[:insert] + [b''] + parts[insert:]
            expected = value_out(Varr([Vstr(sha(b''.join(parts[:insert]))), Vint(insert+1), Varr(Vstr(c.hex()) for c in chunks)]))
            add(f'S.reader.stop.{i:03}', 'S.reader', wire(Varr([Varr(Vstr(c.hex()) for c in chunks), Vint(-1)])), expected, 'S5-ofreader', 'S5-input-unchanged')
            # No empty chunk before the injected error; no prefix digest is allowed.
            fail = rng.randrange(1, len(parts)+1)
            add(f'S.reader.error.{i:03}', 'S.reader', wire(Varr([Varr(Vstr(c.hex()) for c in parts), Vint(fail)])), 'error:reader-probe', 'S5-ofreader')
        for n in [0, 1, (1<<20)-1, 1<<20, (1<<20)+1, 3*(1<<20)+17]:
            path = work / f'file.{n}'
            b = rng.randbytes(n); path.write_bytes(b)
            add(f'S.file.{n}', 'S.file', wire(Vstr(str(path))), sha(b), 'S5-file')
        add('S.file.missing', 'S.file', wire(Vstr(str(work / 'absent'))), 'error:file', 'S5-file')
        for i, n in enumerate([0, 1, (1<<61)-1, 1<<61, (1<<64)-1, 1<<64, (1<<64)+1, 1<<128] + [rng.getrandbits(rng.randrange(130)) for _ in range(32)]):
            add(f'S.saturate.{i:03}', 'S.saturate', wire(Vstr(str(n))), str(min(n, (1<<64)-1)), 'S5-total-limit')
        for n in [0, 1, 63, 64, 65, 126, 127, 128, 129, 191, 192, 193, 255, 256, 257, 511, 512]:
            b = rng.randbytes(n)
            add(f'S.small.hash.{n}', 'S.hash', b, sha(b), 'S5-chunk-arith', executable='small')
            add(f'S.small.stream.{n}', 'S.stream', wire(Varr([Vstr(b[:1].hex()), Vstr(b[1:64].hex()), Vstr(b[64:].hex())])), sha(b), 'S5-chunk-arith', 'S5-update-splits', executable='small')
            add(f'S.c.small.{n}', 'raw', b, 'ok:' + sha(b) + ':input=1:guard=1', 'S5-chunk-arith', 'S5-c-harness', executable='c-small')
        for n in [513, 514, 1024]:
            b = rng.randbytes(n)
            for mode in ['hash', 'stream']:
                add(f'S.abort.small.{mode}.{n}', mode, b, 'ABORT', 'S5-total-limit', executable='abort-small')
            add(f'S.c.limit.{n}', 'raw', b, 'refused:untouched:input=1:guard=1', 'S5-total-limit', 'S5-c-harness', executable='c-small')
        for n in [1<<61, (1<<64)-1, 1<<64, (1<<64)+1, 1<<128]:
            add(f'S.abort.wrap.{n}', 'wrap', str(n).encode(), 'ABORT', 'S5-total-limit', executable='abort-normal')
        for variant, totals in [('small', [513, 514, 1<<61, (1<<64)-1]), ('normal', [1<<61, (1<<61)+1, (1<<64)-1])]:
            for n in totals:
                add(f'S.c.squeeze.limit.{variant}.{n}', 'refuse', b'', 'refused:untouched', 'S5-total-limit', 'S5-c-harness', executable='c-' + variant, argument=str(n))
        tags = ['fvdep/spec-closure/1', 'fvdep/impl-sources/1', 'fvdep/proof-sources/1', 'fvdep/adapter/1', 'fvdep/entry/1']
        adapter_files = [('', api['argv_bytes'](['python3', 'a.py', 'a.py', ''])), ('a.py', b'print(1)\n')]
        for tag in range(5):
            add(f'H3.digest.empty-path.{tag}', 'H3.digest', wire(Varr([Vint(tag), files_value(adapter_files)])), sha(frame(tags[tag], adapter_files)), 'H3-digest')
        for i in range(80):
            tag = i % 5
            paths = sorted({rng.choice(['', 'a', 'z', 'é', '😀', 'x/y', 'a/../b']) + str(j) for j in range(rng.randrange(7))})
            fs = [(p, rng.randbytes(rng.randrange(100))) for p in paths]
            rng.shuffle(fs)
            add(f'H3.digest.{i:03}', 'H3.digest', wire(Varr([Vint(tag), files_value(fs)])), sha(frame(tags[tag], fs)), 'H3-digest')
        assert len({c.id for c in cases}) == len(cases), 'duplicate SHA case id'
        # Binary requests keep large byte inputs out of argv/stdin and separate abort processes.
        observed: dict[str, str] = {}
        driver_dir = ROOT / 'tests/codec/.lake/build/bin'
        for executable in ['normal', 'small']:
            request, result = work / (executable+'.requests'), work / (executable+'.results')
            selected = [c for c in cases if c.executable == executable]
            with request.open('w') as f:
                for i, c in enumerate(selected):
                    path = work / f'{executable}.{i}.input'; path.write_bytes(c.payload)
                    f.write(f'{c.id}\t{c.mode}\t{path}\n')
            binary = driver_dir / ('codec-driver' if executable == 'normal' else 'codec-driver-small')
            run = subprocess.run([str(binary), str(request), str(result)], capture_output=True, text=True, timeout=240, check=False)
            if run.returncode:
                print(f'SHA_DRIVER {executable} rc={run.returncode} stderr={run.stderr[-600:]!r}')
            if result.exists():
                for line in result.read_text().splitlines():
                    id, _, value = line.partition('\t'); observed[id] = value
        env = {**os.environ, 'ASAN_OPTIONS':'detect_leaks=1:abort_on_error=1', 'UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1', 'LEAN_ABORT_ON_PANIC':'1'}
        for i, c in enumerate(cases):
            if c.executable in ['normal', 'small']: continue
            path = work / f'process.{i}.input'; path.write_bytes(c.payload)
            if c.executable.startswith('abort-'):
                binary = driver_dir / ('codec-driver-small' if c.executable == 'abort-small' else 'codec-driver')
                cmd = ['bash', '-c', 'ulimit -c 0; exec "$@"', 'sha-abort', str(binary), '--sha-abort', c.mode, str(path)]
            else:
                cmd = [str(ROOT / 'tests/sha256/.build' / c.executable.replace('c-', 'core-', 1)), c.mode, c.argument if c.mode == 'refuse' else str(path)]
                if c.argument and c.mode != 'refuse': cmd.append(c.argument)
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30, check=False, env=env)
            if c.executable.startswith('abort-'):
                good = result.returncode != 0 and 'SHA_LIMIT_READY' in result.stderr and 'DIGEST' not in result.stdout and re.search(r'[0-9a-fA-F]{64}', result.stdout) is None
                observed[c.id] = 'ABORT' if good else f'rc={result.returncode} stdout={result.stdout[:160]!r} stderr={result.stderr[:160]!r}'
            else:
                observed[c.id] = result.stdout.strip() if result.returncode == 0 else f'rc={result.returncode} stderr={result.stderr[:500]!r}'
        output: list[tuple[Case, bool, str]] = []
        for c in cases:
            got = observed.get(c.id, '<missing result>')
            passed = got == c.expected
            def short(x: str) -> str:
                return x if len(x) < 180 else x[:100] + f'...len={len(x)} sha256={sha(x.encode())}'
            text = ('PASS '+c.id) if passed else f'FAIL {c.id} expected={short(c.expected)} got={short(got)}'
            print(text, flush=True); output.append((c, passed, text))
        p = sum(passed for _, passed, _ in output)
        for clause in sorted({x for c in cases for x in c.clauses}):
            subset = [(c, passed) for c, passed, _ in output if clause in c.clauses]
            cp = sum(passed for _, passed in subset)
            print(f'SCLAUSE {clause} {len(subset)-cp}F/{cp}P cases={",".join(c.id for c,_ in subset)}')
        record = ROOT / 'tests/sha256/.build/results.tsv'
        with record.open('w', newline='') as f:
            writer = csv.writer(f, delimiter='\t', lineterminator='\n')
            writer.writerow(['id','command','output'])
            writer.writerows((c.id, 'tools/vflab-run bash tests/codec/run.sh', text) for c,_,text in output)
        print(f'SUMMARY_S seed={seed} cases={len(cases)} pass={p} fail={len(cases)-p}', flush=True)
        return 1 if p != len(cases) else 0

if __name__ == '__main__':
    raise SystemExit(main())
