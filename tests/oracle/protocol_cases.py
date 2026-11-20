"""Seeded end-to-end native bridge, batch validation, and observable trace cases."""
from __future__ import annotations

from array import array
import fcntl
import itertools
import os
from pathlib import Path
import random
import re
import select
import subprocess
import termios

from tests.oracle.harness import (
    BIN, BYTES, INT, NAT, ORDER, SEED, TEXT, TRIAL, UNITS, VERSION, WORK, Context, case,
    evals, jtext, need, proxy_entries, put, text_lines, wait_until,
)
from tests.oracle.reference import (
    ERR, MAX_INT, crank, decode, encode, expect, number, ok, request, semver_compare, semver_parse, trial, ver,
)


def rng(op: str) -> random.Random:
    return random.Random(SEED ^ int.from_bytes(op.encode(), "big"))


def signed_values(r: random.Random) -> list[int]:
    return [0, 1, -1, MAX_INT, MAX_INT + 1, MAX_INT + 2, -MAX_INT, -MAX_INT - 1,
            10**91, -(10**91), *(r.randrange(-(10**49), 10**49) for _ in range(32))]


def random_text(r: random.Random, cap: int = 16) -> str:
    alphabet = "Aa0-+./ \"\\\n\r\t\x00\x7f\x85é𝄞🙂\u2028\ufeff\uffff"
    return "".join(r.choices(alphabet, k=r.randrange(cap)))


def version_value(r: random.Random) -> dict:
    nats = [0, 42, MAX_INT, MAX_INT + 1, 10**88, r.getrandbits(r.randrange(110))]
    pre = [r.choice(({"num": number(r.choice(nats))}, {"alnum": random_text(r)})) for _ in range(r.randrange(5))]
    return ver(*r.choices(nats, k=3), pre=pre, build=[random_text(r) for _ in range(r.randrange(5))])


@case("W.weighted-property", "W1–W5, Q2; E4", "seeded weighted Int×Int×Int -> Option Int, order, implicit binder, actual fn name")
def weighted(c: Context) -> None:
    c.lib()
    r = rng(TRIAL.fn)
    pool = signed_values(r)
    cases = [(2, 5, -1), (-1, 2, 5), (1, 7, 7), (8, -7, -7), (MAX_INT, 0, 1)]
    cases += [(r.choice(pool), r.choice(pool), r.choice(pool)) for _ in range(63)]
    batch = b"".join(request(TRIAL, *map(number, args)) for args in cases)
    # A derivation from the module id instead of the registered function fails these negatives.
    wrong = [request("weight_mix", 2, 3, 4), request("weightMix", 2, 3, 4),
             request(TRIAL, 2, 3), request(TRIAL, 2, 3, 4, 5)]
    expect(c.oracle(TRIAL, b"".join(wrong) + batch), *([None] * len(wrong)),
           *(trial(TRIAL, a, b, cc) for a, b, cc in cases))


@case("W.bytearray-property", "W3–W5; §8", "ByteArray both ways: empty/all bytes/seeded reversals, malformed encodings refused")
def bytearray(c: Context) -> None:
    c.lib()
    r = rng(BYTES.fn)
    cases = [b"", bytes(range(256)), b"\x00\xff\x80", *(r.randbytes(r.randrange(160)) for _ in range(72))]
    wrong = ["FC", "f", "0x00", "gg", "é0", [0, 255], False, 1, None]
    expect(c.oracle(BYTES, b"".join(request(BYTES, x) for x in wrong + [b.hex() for b in cases])),
           *([None] * len(wrong)), *(ok(b[::-1].hex()) for b in cases))


@case("W.utf16-property", "W3–W5; §8", "UTF-16 code units retain lone surrogates, all edge values and order")
def units(c: Context) -> None:
    c.lib()
    r = rng(UNITS.fn)
    cases = [[], [0, 0x7F, 0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000, 0xFFFF],
             [0xDC00, 0xD800], [0xD800], [0xDFFF]]
    cases += [[r.randrange(65536) for _ in range(r.randrange(33))] for _ in range(72)]
    bad = ["x", [True], ["1"], [-1], [65536], [0, 65536], [None]]
    expect(c.oracle(UNITS, b"".join(request(UNITS, x) for x in [*cases, *bad])),
           *(ok(x[::-1]) for x in cases), *([None] * len(bad)))


@case("W.text-property", "W1–W5; V1; U3 J1–J4", "UTF-8 scalar and escaping round trips, inclusive 65,536-byte string bound")
def text(c: Context) -> None:
    c.lib()
    r = rng(TEXT.fn)
    max_text = "🙂" * 16_383 + "é" + "xy"
    need(len(max_text.encode()) == 65536, "text boundary fixture is not 65,536 bytes")
    cases = ["", "a\x00\t\x7f\x85\u2028\u2029é\ufeff🙂\uffff\\\"", max_text,
             *(random_text(r, 80) for _ in range(64))]
    invalid = [request(TEXT, max_text + "x"), b'{"args":["\\ud800"],"op":"turnText"}\n',
               b'{"args":["\xff"],"op":"turnText"}\n', b'{"args":["\x00"],"op":"turnText"}\n']
    batch = b"".join(request(TEXT, s) for s in cases)
    expect(c.oracle(TEXT, batch + b"".join(invalid)), *(ok(s[::-1]) for s in cases), *([None] * len(invalid)))


@case("W.nat-int-property", "W1–W5; U4 B2", "Nat and Int encode magnitude boundaries and canonical decimal strings both ways")
def numbers(c: Context) -> None:
    c.lib()
    vals = signed_values(rng(NAT.fn))
    for op, xs, extra_bad in ((NAT, [0, MAX_INT // 2, MAX_INT // 2 + 1, *map(abs, vals)], [-1, str(-MAX_INT - 1)]),
                              (INT, vals, [])):
        bad = ["", "0", "-0", "1", "-1", "01", "0009007199254740992", "+9007199254740992", "-09007199254740992",
               "9007199254740992\n", MAX_INT + 1, -MAX_INT - 1, True, None, *extra_bad]
        raw = b"".join(request(op, x) for x in [*map(number, xs), *bad])
        answers = [ok(number((2 * n + 1) if op == NAT else (3 * n - 2))) for n in xs]
        expect(c.oracle(op, raw), *answers, *([None] * len(bad)))


@case("W.ordering", "W1–W5; §8", "Ordering arg/result accepts exactly lt/eq/gt")
def ordering(c: Context) -> None:
    c.lib()
    order = ("lt", "eq", "gt")
    invalid = ("LT", "eq ", "", "le", "gt\n", 2, None, ["eq"])
    expect(c.oracle(ORDER, b"".join(request(ORDER, x) for x in (*order, *invalid))),
           ok("eq"), ok("gt"), ok("lt"), *([None] * len(invalid)))


@case("W.version-property", "W1–W5; U4 B2", "Version fields and tagged empty/non-ASCII/punctuated identifiers preserved exactly")
def version_values(c: Context) -> None:
    c.lib()
    r = rng(VERSION.fn)
    cases = [ver(), ver(MAX_INT, MAX_INT + 1, 3, pre=[{"alnum": ""}, {"num": 0}, {"alnum": "0"},
            {"alnum": ".//é🙂\x00\u2028"}, {"num": str(10**90)}], build=["", "/. x", "🙂", "000"]),
             *(version_value(r) for _ in range(76))]
    normal = ver(1, 0, 0)
    bad = [normal | {"major": "1"}, normal | {"minor": -1}, normal | {"patch": MAX_INT + 1},
           normal | {"pre": [{"num": 1, "alnum": "a"}]}, normal | {"pre": [{"alnum": 1}]},
           normal | {"build": [0]}, normal | {"extra": "x"}, {k: v for k, v in normal.items() if k != "minor"}]
    answers = [ok(v | {"pre": v["pre"][::-1], "build": v["build"][::-1]}) for v in cases]
    expect(c.oracle(VERSION, b"".join(request(VERSION, x) for x in [*cases, *bad])),
           *answers, *([None] * len(bad)))


def rfc(c: Context, url: bool) -> None:
    c.lib()
    suffix, camel = ("_url", "Url") if url else ("", "")
    r = rng("base64" + suffix)
    xs = [b"", b"f", b"fo", b"foo", b"foob", b"fooba", b"foobar", b"\xfb\xff", bytes(range(256)),
          *(r.randbytes(r.randrange(120)) for _ in range(61))]
    expect(c.oracle(f"base64.encode{suffix}@1.0.0", b"".join(request("encode" + camel, x.hex()) for x in xs)),
           *(ok(encode(x, url)) for x in xs))
    texts = [encode(x, url) for x in xs]
    texts += ["A", "AA", "AA=", "A===", "A=A=", "AAAA=", "AA==AAAA", "AB==", "AAB=", "YQ=", "YQ==\n",
              "YW Jj", "éAAA", "\x00AAA", encode(b"\xfb\xff", not url)]
    expect(c.oracle(f"base64.decode{suffix}@1.0.0", b"".join(request("decode" + camel, s) for s in texts)),
           *(decode(s, url) for s in texts))


@case("W.rfc-standard", "W3–W5; Q2; library Operations", "List UInt8 and text via independent RFC 4648 standard encoder/strict decoder")
def std64(c: Context) -> None:
    rfc(c, False)


@case("W.rfc-url", "W3–W5; Q2; library Operations", "List UInt8 and text via independent RFC 4648 URL encoder/strict decoder")
def url64(c: Context) -> None:
    rfc(c, True)


@case("W.large-reply", "V4; §8; U4 B3", "a 65,536-character Base64 input returns the entire 98,304-character hex string")
def large_reply(c: Context) -> None:
    c.lib()
    data = "A" * 65_536
    expected = ok((b"\x00" * 49_152).hex())
    expect(c.oracle("base64.decode@1.0.0", request("decode", data)), expected)


@case("W.semver-parse", "W3–W5; library Operations", "SemVer strict grammar, large numbers, prerelease/build distinctions")
def parse_versions(c: Context) -> None:
    c.lib()
    cases = ["0.0.0", "2.3.4-0.A-0+00.f-", "1.0.0+001", "1.0.0--", "", "v1.0.0", " 1.0.0", "1.0.0\n",
             "1.0.0-01", "01.0.0", "1.0.0+", "1.0.0-", "1.0.0-..", "1.0.0-β", "1.0.0+z+q", "１.0.0",
             f"{10**82}.0.1-{10**76}.Z+01"]
    r = rng("parse")
    for _ in range(48):
        core = ".".join(str(r.getrandbits(r.randrange(85))) for _ in range(3))
        s = f"{core}-a{r.randrange(100)}.{r.randrange(100)}+b.{r.randrange(100)}"
        cases.extend((s, s.replace("-a", "-00.", 1)))
    expect(c.oracle("semver.parse@1.0.0", b"".join(request("parse", s) for s in cases)),
           *(semver_parse(s) for s in cases))


@case("W.semver-compare", "W3–W5; library Operations", "real ordering is the whole-type reference, ignoring build across generated pairs")
def compare_versions(c: Context) -> None:
    c.lib()
    r = rng("compare")
    axes = [ver(), ver(1), ver(0, 1), ver(0, 0, 1), ver(pre=[{"num": 2}]), ver(pre=[{"num": 10}]),
            ver(pre=[{"alnum": ""}]), ver(pre=[{"alnum": "1"}]), ver(pre=[{"alnum": "1"}, {"num": 1}]),
            ver(pre=[{"alnum": "💡"}]), ver(build=["ignored", "/."])]
    pairs = list(itertools.product(axes, repeat=2))
    for _ in range(40):
        a, b = version_value(r), version_value(r)
        pairs.extend(((a, b), (b, a), (a, a | {"build": [random_text(r), ""]})))
    expect(c.oracle("semver.compare@1.0.0", b"".join(request("compare", a, b) for a, b in pairs)),
           *(ok(semver_compare(a, b)) for a, b in pairs))


@case("V.empty", "V1, V3–V4", "zero-byte input produces zero bytes and no evaluation")
def empty(c: Context) -> None:
    c.lib()
    log = c.proxy("bwrap")
    expect(c.oracle(TRIAL, request(TRIAL, 1, 2, 3)), trial(TRIAL, 1, 2, 3))
    need(evals(log) == 1, "bwrap observer missed the valid control evaluation")
    expect(c.oracle(TRIAL))
    need(evals(log) == 1, "zero requests launched evaluation")


@case("V.mixed-lines", "V1–V5; U4 B3", "blank/invalid interleaving, CRLF, final unterminated line, one eval for all valid rows")
def mixed(c: Context) -> None:
    c.lib()
    log = c.proxy("bwrap")
    first = b'{"op": "foldPulse", "args": [2, -3, 5]}\r\n'
    rejected = request(TRIAL, 0, 1, 1)
    last = request(TRIAL, -2, 3, 4).removesuffix(b"\n")
    duplicate = b'{"op":"foldPulse","\\u006fp":"foldPulse","args":[-2,3,4]}\n'
    data = b"\n" + first + b"not-json\n" + rejected + duplicate + last
    expect(c.oracle(TRIAL, data), None, trial(TRIAL, 2, -3, 5), None, ERR, None, trial(TRIAL, -2, 3, 4))
    need(evals(log) == 1, "a mixed batch did not use exactly one evaluation step")


@case("V.all-invalid", "V2–V3; I2", "all-invalid batch replies in order without running an evaluation step")
def all_invalid(c: Context) -> None:
    c.lib()
    log = c.proxy("bwrap")
    expect(c.oracle(TRIAL, request(TRIAL, 1, 2, 3)), trial(TRIAL, 1, 2, 3))
    need(evals(log) == 1, "evaluation-proxy positive control did not fire")
    bad_rows = [b"\n", b"garbage\n", request("other", 1, 2, 3), request(TRIAL, 2), request(TRIAL, 1, "2", 3)]
    expect(c.oracle(TRIAL, b"".join(bad_rows)), *([None] * len(bad_rows)))
    need(evals(log) == 1, "invalid public requests crossed into the driver")


@case("V.request-budget", "V1; I5; Q3", "exact request byte cap accepts CRLF batch, one more byte refuses with zero stdout")
def request_budget(c: Context) -> None:
    c.lib()
    data = request(TRIAL, 2, 3, 4).replace(b"\n", b"\r\n")
    n = len(data)
    expect(c.oracle(TRIAL, data, limits={"requestBytes": n}), trial(TRIAL, 2, 3, 4))
    c.oracle(TRIAL, data + b"\n", limits={"requestBytes": n}).failure(
        re.escape(f"infra io: oracle, input: the batch exceeds {n} bytes"))


@case("V.staging-budget", "V2; W1; I5; Q3", "exact W1 staged-byte cap accepts, one fewer rejects after a valid first request")
def staging_budget(c: Context) -> None:
    c.lib()
    pairs = ((-1, 2, 3), (4, 0, -5))
    data = request(TRIAL, *pairs[0]) + b"invalid\n" + request(TRIAL, *pairs[1])
    layout = b"i:-1 i:2 i:3\ni:4 i:0 i:-5\n"
    n = len(layout)
    expect(c.oracle(TRIAL, data, limits={"stagingBytes": n}), trial(TRIAL, *pairs[0]), None, trial(TRIAL, *pairs[1]))
    c.oracle(TRIAL, data, limits={"stagingBytes": n - 1}).failure(
        re.escape("infra io: oracle, input:"), r"(?i)stag|requests\.txt|byte")


@case("V.output-budget", "V4; U4 B3; I5; Q3", "exact canonical reply-byte cap accepts; a late overflow returns no prefix")
def output_budget(c: Context) -> None:
    c.lib()
    rows = ((-7, 5, 21), (6, 0, 0), (MAX_INT, -MAX_INT, MAX_INT))
    data = b"".join(request(TRIAL, *map(number, xs)) for xs in rows)
    answers = [trial(TRIAL, *xs) for xs in rows]
    n = sum(len(jtext(x)) + 1 for x in answers)
    expect(c.oracle(TRIAL, data, limits={"batchBytes": n}), *answers)
    c.oracle(TRIAL, data, limits={"batchBytes": n - 1}).failure(
        re.escape(f"infra io: oracle, output: the encoded batch exceeds {n - 1} bytes"))


@case("V.invalid-budget", "V2, V4; I5", "invalid reply charged before a later valid request reaches the evaluation step")
def invalid_budget(c: Context) -> None:
    c.lib()
    log = c.proxy("bwrap")
    ready = request(TRIAL, 2, 3, 4)
    expect(c.oracle(TRIAL, ready), trial(TRIAL, 2, 3, 4))
    need(evals(log) == 1, "evaluation-proxy positive control did not fire")
    n = len(b'{"invalid":""}\n') - 1  # Lower bound independent of the free invalid reason.
    c.oracle(TRIAL, b"\n" + ready, limits={"batchBytes": n}).failure(
        re.escape("infra io: oracle,"), re.escape(f"the encoded batch exceeds {n} bytes"))
    need(evals(log) == 1, "evaluation started after the batch budget had already failed")


DRIVER_ERROR = r"infra io: oracle, evaluate: the driver's reply [0-9]+ is malformed"


@case("V.reply-substitute", "V3–V5; Q3", "use typed substituted driver lines at valid ranks, not driver stdout or public order")
def substitute(c: Context) -> None:
    c.lib()
    data = request(TRIAL, 1, 2, 3) + b"\n" + request(TRIAL, 0, 4, 5) + request(TRIAL, 3, 1, 2)
    expect(c.oracle(TRIAL, data, replies=b"ok i:71\nerr\nok i:-52\n"), ok(71), None, ERR, ok(-52))


@case("V.reply-missing-extra", "V3–V5; Q3", "missing line, missing LF, extra result, and extra blank line refuse before stdout")
def reply_count(c: Context) -> None:
    c.lib()
    data = request(TRIAL, 1, 2, 3)
    for body in (b"", b"ok i:1", b"ok i:1\nok i:2\n", b"ok i:1\n\n"):
        c.oracle(TRIAL, data, replies=body).failure(DRIVER_ERROR)


@case("V.reply-spelling", "W2, W4; V4; Q3", "reject noncanonical result syntaxes, decimal variants and raw invalid bytes")
def reply_spelling(c: Context) -> None:
    c.lib()
    data = request(TRIAL, 1, 2, 3)
    for body in (b"OK i:1\n", b"ok i:+1\n", b"ok i:-0\n", b"ok i:01\n", b"ok i:1 \n", b"err extra\n",
                 b"ok i:\xff\n", b"ok i:1\r\n"):
        c.oracle(TRIAL, data, replies=body).failure(DRIVER_ERROR)


@case("V.reply-type-and-rank", "W2, W4; V4–V5; Q3", "typed reply checks and malformed line index counts valid requests only")
def reply_rank(c: Context) -> None:
    c.lib()
    valid = request(TRIAL, 1, 2, 3)
    r0 = c.oracle(TRIAL, valid, replies=b"ok n:42\n").failure(DRIVER_ERROR)
    r1 = c.oracle(TRIAL, b"\n" + valid + b"bad\n" + valid, replies=b"ok i:12\nok n:42\n").failure(DRIVER_ERROR)
    rank_pattern = rb"the driver's reply ([0-9]+) is malformed"
    m0, m1 = re.search(rank_pattern, r0.err), re.search(rank_pattern, r1.err)
    assert m0 is not None and m1 is not None
    first, second = int(m0[1]), int(m1[1])
    need(first in (0, 1) and second == first + 1,
         f"malformed line diagnostic uses input position rather than its driver rank: {first}, {second}")
    c.oracle(INT, request(INT, 1), replies=b"err\n").failure(DRIVER_ERROR)


@case("V.evaluate-deadline", "V3; U5 R4/P5; Q3", "real bounded-time evaluation ends on the deadline, with typed exit 2 and no replies")
def evaluate_deadline(c: Context) -> None:
    c.lib()
    log = c.proxy("bwrap")
    expect(c.oracle(WORK, request(WORK, 17)), ok(crank(17)))
    need(evals(log) == 1, "warm-up did not run the evaluator")
    data = request(WORK, 0) + request(WORK, 10**10)
    c.oracle(WORK, data, limits={"oracleSeconds": 1}).failure(
        re.escape("infra io: oracle, evaluate:"), r"(?i)deadline|timed?[- ]?out|timeout")
    need(evals(log) == 2, "deadline applied outside the evaluation step")


@case("O.help", "O1; §1", "both command help spellings ignore poison manifest/source, cache and stdin", fixture=False)
def help_only(c: Context) -> None:
    c.proxy("git")
    os.mkfifo(c.work / "fvdep.toml")
    for spell in (("oracle", "--help"), ("help", "oracle")):
        result = c.unread_input([str(BIN), *spell]).code(0)
        lines = text_lines(result.out)
        need(any(re.search(r"\boracle\b", s) for s in lines), "help did not show oracle usage")
        need(not c.cache.exists() and not proxy_entries(c.home / "git.jsonl"), "help effected cache or fetch")


@case("O.usage", "O1, O3; §1–2", "specific help exists; wrong arity/option refuses before any source effect", fixture=False)
def usage(c: Context) -> None:
    help_result = c.local_stdout("oracle", "--help").code(0)
    need(b"oracle" in help_result.out, "oracle help missing")
    log = c.proxy("git")
    for args in ((), (TRIAL.target, "extra"), (TRIAL.target, "--unrecognized-oracle-flag")):
        c.local_stdout("oracle", *args).failure(r"(?i)usage", absent=("Fetch failed:",))
    need(not c.cache.exists() and not proxy_entries(log), "usage started a fetch or created the cache")


@case("O.resolution-unread", "O1, O3; E1", "unknown target exits with an open stdin writer and leaves prequeued bytes unread")
def resolution_unread(c: Context) -> None:
    c.lib()
    target = "trial.unknown@1.0.0"
    log = c.proxy("bwrap")
    result = c.unread_input(c.oracle_argv(target), request(TRIAL, 1, 2, 3))
    result.failure(re.escape(f"unknown target {target}"))
    c.noted(c.need_fixture().second)
    need(not proxy_entries(log), "unknown target invoked the build or sandbox preflight")


@case("O.batch-eof", "O1, O3; V1–V4; §8", "prequeued valid request yields no evaluation/output while its producer remains open")
def batch_eof(c: Context) -> None:
    c.lib()
    trace = c.proxy("bwrap")
    a, b = (1, 2, 3), (-9, 1, -2)
    expect(c.oracle(TRIAL, request(TRIAL, *a)), trial(TRIAL, *a))
    before = evals(trace)
    need(before == 1, "evaluation observer did not fire on positive control")
    read, write = os.pipe()
    try:
        os.write(write, request(TRIAL, *a))
        argv = c.oracle_argv(TRIAL)
        with subprocess.Popen(argv, cwd=c.work, env=c.env, stdin=read, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE) as proc:
            assert proc.stdout is not None
            try:
                def consumed() -> bool:
                    pending = array("i", [0])
                    fcntl.ioctl(read, termios.FIONREAD, pending, True)
                    return proc.poll() is not None or pending[0] == 0

                wait_until(consumed, 90, "the first request to be consumed")
                early = select.select([proc.stdout], [], [], 1.0)[0]
                need(not early and evals(trace) == before, "oracle began replying/evaluating before stdin EOF")
                os.write(write, request(TRIAL, *b).removesuffix(b"\n"))
                os.close(write)
                write = -1
                out, err = proc.communicate(timeout=90)
            except (AssertionError, OSError, subprocess.SubprocessError):
                proc.kill()
                out, err = proc.communicate()
                assert proc.returncode is not None
                c.observed(argv, c.work, c.env, proc.returncode, out, err)
                raise
            assert proc.returncode is not None
            expect(c.observed(argv, c.work, c.env, proc.returncode, out, err), trial(TRIAL, *a), trial(TRIAL, *b))
        need(evals(trace) == before + 1, "closed stream did not evaluate exactly once")
    finally:
        if write >= 0:
            os.close(write)
        os.close(read)


@case("O.output-failure", "I5; O1; §2", "stdout I/O errors and broken pipe exit 2 instead of success/signal")
def output_failure(c: Context) -> None:
    c.lib()
    data = request(TRIAL, 1, 2, 3)
    expect(c.oracle(TRIAL, data), trial(TRIAL, 1, 2, 3))
    argv = c.oracle_argv(TRIAL)
    file = put(c.home, "read-only-output", b"output was not replaced")
    with file.open("rb") as read_only:
        c.invoke(argv, data=data, stdout_fd=read_only.fileno()).failure(r"Could not write the output: .+\.")
    need(file.read_bytes() == b"output was not replaced", "failed write mutated the read-only descriptor's file")
    read, write = os.pipe()
    os.close(read)
    try:
        c.invoke(argv, data=data, stdout_fd=write).failure(absent=("Could not write the output:",))
    finally:
        os.close(write)


@case("O.steps", "I1–I2; E3–E4; V3; O3", "two ordered export roots and one evaluation in real sandbox, using one library view")
def steps(c: Context) -> None:
    c.lib()
    log = c.proxy("bwrap")
    expect(c.oracle(TRIAL, request(TRIAL, 3, 4, 5)), trial(TRIAL, 3, 4, 5))
    trace = []
    views = []
    for row in proxy_entries(log):
        args = row["argv"]
        if "--run" in args and any(Path(a).name == "Driver.lean" for a in args):
            trace.append("eval")
        elif export := next((i for i, a in enumerate(args) if Path(a).name == "leanexport"), 0):
            trace.append(args[export + 1:])
        else:
            continue
        views.append(next((args[i + 1] for i in range(len(args) - 2)
                           if args[i] == "--ro-bind" and args[i + 2] == "/fvdep/lib"), None))
    need(trace == [[TRIAL.entry, "--", TRIAL.entry + ".entry"],
                   [TRIAL.spec, "--", TRIAL.spec + "." + TRIAL.fn], "eval"], f"unexpected export/eval trace: {trace!r}")
    need(None not in views and len(set(views)) == 1, f"exports/eval did not share one read-only library view: {views!r}")
