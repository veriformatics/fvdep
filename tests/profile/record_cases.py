"""P5 request/record oracle, bounded-child faults, and the D2 compile barrier."""
from __future__ import annotations

from pathlib import Path
import random
import re
import shlex
import signal
from typing import Any, Callable

from tests.profile.boundary_cases import EOF, SORRY, SOURCE_BATCH_BYTES, SOURCE_FILE_BYTES, early_snapshot
from tests.profile.harness import (
    HEX, INIT, LIBRARY_HEADERS, PHASE_IMPL, PROFILE, SEED, SIMPLE, SPEC_MODULE,
    Context, Grammars, Result, Sources, case, check, jtext, lines, module_path, need, profile_lines,
    put, refusal, request_bytes, sha, source_digest, sources, step_argv,
)
from tests.profile.syntax_cases import COMMAND, TERM

IO = "infra io: profile, "
BAD_RECORD = IO + "the result record "
IMPL = sources({"Impl": PHASE_IMPL})
PAIR = sources({"Z": "def z := 2\n", "A.B": SIMPLE})
ACCEPTED = {"kind": "accepted"}
DEEP = "def deep := (((7)))\n"
SHALLOW_NODES, DEEP_DEPTH = 30, 9  # D4: header and all command occurrences, including empty nodes.
PAREN_COUNT = 50000
SLOW = "def slow := " + "(" * PAREN_COUNT + "0" + ")" * PAREN_COUNT + "\n"
FILE_SIGNAL = int(signal.SIGXFSZ)


def request(c: Context, batch: Sources, *, headers: Grammars | None = None,
            limits: dict[str, int] | None = None, fingerprint: str | None = None) -> str:
    return sha(request_bytes(batch, fingerprint or c.toolchain.fingerprint, library=headers, limits=limits))


def record(batch: Sources, key: str, grammar: Grammars, outcome: dict[str, Any] | None = None) -> dict[str, Any]:
    return {"schema": 1, "profile": PROFILE, "recipe": "consumer/1", "request": key,
            "modules": [{"module": m, "sha256": sha(b), "grammar": list(grammar[m])}
                        for m, b in sorted(batch.items())],
            "outcome": ACCEPTED if outcome is None else outcome}


def rejected(rule: str, detail: list[str], module: str = "A.B", *, line: int = 1,
             column: int = 0) -> dict[str, Any]:
    return {"kind": "refused", "cause": {"rule": rule, "detail": detail},
            "module": module, "line": line, "column": column}


def input_record(c: Context, value: bytes | dict[str, Any], name: str = "results.json") -> Path:
    return put(c.directory, name, value if isinstance(value, bytes) else jtext(value))


def output(c: Context, r: Result, batch: Sources, want: str, *, grammar: Grammars | None = None,
           headers: Grammars | None = None, limits: dict[str, int] | None = None,
           proof: Sources | None = None) -> list[str]:
    prefix = () if proof is None else (
        "impl_sources " + source_digest("impl", batch), "proof_sources " + source_digest("proof", proof),
    )
    return profile_lines(r, batch, want, request=request(c, batch, headers=headers, limits=limits),
                         grammars={} if grammar is None else grammar, prefix=prefix)


def inject(c: Context, raw: bytes | dict[str, Any], batch: Sources, want: str, *,
           grammar: Grammars | None = None, headers: Grammars | None = None,
           limits: dict[str, int] | None = None) -> None:
    library = c.library() if headers is not None else None
    check(c, batch, want, grammar={} if grammar is None else grammar, library=library, headers=headers,
          limits=limits, results=input_record(c, raw))


@case("record.accepted", "R/P5b/D1", "0; canonical matching record, grammar in module order, no parse launch")
def valid_record(c: Context) -> None:
    # P5b validates grammar shape, not the report's relation to headers or the module's own imports.
    grammar = {"A.B": ("Std.Time", "Init", "Std.Time"), "Z": ()}
    inject(c, record(PAIR, request(c, PAIR), grammar), PAIR, "accepted", grammar=grammar)


@case("record.refused", "P5b/T/D1/interface §1", "1; refusal uses the typed cause, codepoints and Cc line escaping")
def reflected_refusal(c: Context) -> None:
    grammar = dict.fromkeys(PAIR, INIT)
    detail = "a\x00\t\n\r\x1b\x7f\x85é"
    v = record(PAIR, request(c, PAIR), grammar, rejected("parse", [detail], "Z", line=4, column=17))
    inject(c, v, PAIR, refusal(4, 17, "parse " + detail, "Z"), grammar=grammar)


@case("record.detail-limit", "P5b/T", "1; detail of exactly 1024 UTF-8 bytes fits, not clipped at intake")
def record_detail_limit(c: Context) -> None:
    grammar = dict.fromkeys(PAIR, INIT)
    detail = "é" * 512
    v = record(PAIR, request(c, PAIR), grammar, rejected("parse", [detail]))
    inject(c, v, PAIR, refusal(1, 0, "parse " + detail, "A.B"), grammar=grammar)


@case("record.over", "P5b/P6/D1", "2; a valid over outcome → batch cap, no grammar lines or launch")
def record_over(c: Context) -> None:
    v = record(PAIR, request(c, PAIR), dict.fromkeys(PAIR, INIT), {"kind": "over", "limit": "batchNodes"})
    inject(c, v, PAIR, IO + "the batch passed batchNodes 16777216")


RecordEdit = Callable[[dict[str, Any]], bytes | None]


def change(v: dict[str, Any], **fields: Any) -> None:
    v.update(fields)


def absent(v: dict[str, Any], field: str) -> None:
    del v[field]


def row_edit(v: dict[str, Any], **fields: Any) -> None:
    v["modules"][0].update(fields)


MALFORMED: dict[str, RecordEdit] = {
    "json": lambda _: b'{"schema":',
    "scalar": lambda _: b"null",
    "trailing-lf": lambda v: jtext(v) + b"\n",
    "leading-space": lambda v: b" " + jtext(v),
    "escaped-key": lambda v: jtext(v).replace(b'"schema"', b'"' + bytes([92]) + b'u0073chema"'),
    "duplicate": lambda v: jtext(v)[:-1] + b',"schema":1}',
    "root-missing": lambda v: absent(v, "profile"),
    "root-extra": lambda v: change(v, extra="other"),
    "root-mistyped": lambda v: change(v, profile=3),
    "schema": lambda v: change(v, schema=2),
    "request-syntax": lambda v: change(v, request="a" * 63),
    "digest-uppercase": lambda v: row_edit(v, sha256="A" * 64),
    "grammar-type": lambda v: row_edit(v, grammar="Init"),
    "grammar-name": lambda v: row_edit(v, grammar=["A..B"]),
    "module-extra": lambda v: row_edit(v, extra=True),
    "outcome-kind": lambda v: change(v, outcome={"kind": "other"}),
    "outcome-extra": lambda v: change(v, outcome={"kind": "accepted", "extra": False}),
    "limit": lambda v: change(v, outcome={"kind": "over", "limit": "depth"}),
    "rule": lambda v: change(v, outcome=rejected("other", ["x"])),
    "arity": lambda v: change(v, outcome=rejected("kind", ["a", "b"])),
    "detail-type": lambda v: change(v, outcome={"kind": "refused", "module": "A.B", "line": 1, "column": 0,
                                                "cause": {"rule": "kind", "detail": [1]}}),
    "detail-bytes": lambda v: change(v, outcome=rejected("parse", ["é" * 512 + "a"])),
    "line-zero": lambda v: change(v, outcome=rejected("kind", ["x"], line=0)),
    "col-negative": lambda v: change(v, outcome=rejected("kind", ["x"], column=-1)),
    "line-unsafe-int": lambda v: change(v, outcome=rejected("kind", ["x"], line=2**53)),
    "cap-invalid-decimal": lambda v: change(v, outcome=rejected("cap", ["nodes", "01"])),
    "header-invalid-modifier": lambda v: change(v, outcome=rejected("header", ["modifier", "other"])),
    "scope-invalid-slot": lambda v: change(v, outcome=rejected("scope", ["close", "Array"])),
}


def malformed_sample(id_: str, edit: RecordEdit) -> None:
    @case("record.malformed." + id_, "R/P5b/U3 J", "2; result record is malformed")
    def run(c: Context) -> None:
        valid = record(PAIR, request(c, PAIR), dict.fromkeys(PAIR, INIT))
        body = edit(valid)
        inject(c, valid if body is None else body, PAIR, BAD_RECORD + "is malformed")


for sample, mutation in MALFORMED.items():
    malformed_sample(sample, mutation)


def misbinding(v: dict[str, Any], batch: Sources, change_: str, alternate: str = "a" * 64) -> str:
    match change_:
        case "profile":
            v["profile"] = "fvdep/profile/2"
            return "names profile fvdep/profile/2"
        case "request":
            expected = v["request"]
            v["request"] = alternate
            return f"names request {alternate}, expected {expected}"
        case "recipe":
            v["recipe"] = "library/1"
            return "names recipe library/1"
        case "missing":
            v["modules"].pop()
            return f"lists {len(batch) - 1} modules, expected {len(batch)}"
        case "extra":
            v["modules"].append({"module": "ZZ", "sha256": "b" * 64, "grammar": []})
            return f"lists {len(batch) + 1} modules, expected {len(batch)}"
        case "names":
            first, second = v["modules"]
            v["modules"] = [second, first]
            return f"lists {second['module']} at 1, expected {first['module']}"
        case "digest":
            first = v["modules"][0]
            name, expected = first["module"], first["sha256"]
            first["sha256"] = alternate
            return f"has digest {alternate} for {name}, expected {expected}"
        case "outside":
            v["outcome"] = rejected("kind", [TERM + "sorry"], "Outside")
            return "refuses Outside, outside the batch"
        case _:
            raise AssertionError(f"unknown misbinding {change_}")


BINDINGS = ("profile", "request", "recipe", "missing", "extra", "names", "digest", "outside")


def binding_sample(change_: str) -> None:
    @case("record.binding." + change_, "R/P5b/D1", "2; first binding reason names " + change_)
    def run(c: Context) -> None:
        v = record(PAIR, request(c, PAIR), dict.fromkeys(PAIR, INIT))
        why = misbinding(v, PAIR, change_)
        inject(c, v, PAIR, BAD_RECORD + why)


for field in BINDINGS:
    binding_sample(field)


def request_change(variant: str) -> None:
    @case("record.request-input." + variant, "R/P5a/P5b/B2", "2; request digest binds " + variant)
    def run(c: Context) -> None:
        fields = LIBRARY_HEADERS
        expected = request(c, PAIR, headers=fields)
        match variant:
            case "library-header":
                modified = request(c, PAIR, headers=fields | {SPEC_MODULE: ("Std.Time",)})
            case "library-header-order":
                fields = fields | {SPEC_MODULE: ("Std.Time", "Std.Data.HashMap")}
                expected = request(c, PAIR, headers=fields)
                modified = request(c, PAIR, headers=fields | {SPEC_MODULE: tuple(reversed(fields[SPEC_MODULE]))})
            case "depth":
                modified = request(c, PAIR, headers=fields, limits={"depth": 4095})
            case "toolchain":
                modified = request(c, PAIR, headers=fields, fingerprint="f" * 64)
            case "source-bytes":
                modified = request(c, PAIR | {"A.B": b"def a := 2\n"}, headers=fields)
            case _:
                raise AssertionError(f"unknown request variant {variant}")
        library = c.library(body="".join(f"import {m}\n" for m in fields[SPEC_MODULE])
                            + "def Fvdep.Trial.sample : Nat := 1\n")
        v = record(PAIR, modified, dict.fromkeys(PAIR, INIT))
        r = c.profile(c.trial(PAIR), list(PAIR), library=library, results=input_record(c, v), observe=True)
        rest = profile_lines(r, PAIR, BAD_RECORD + f"names request {modified}, expected {expected}",
                             request=expected, grammars={})
        need(not rest, f"text after D1 outcome: {rest!r}")
        r.no_build(launches=0)


for request_variant in ("library-header", "library-header-order", "depth", "toolchain", "source-bytes"):
    request_change(request_variant)


def generated_mutation(i: int) -> None:
    @case(f"record.generated.{i:02}", "P5b property", "2; generated malformed or mis-bound record: first failure only")
    def run(c: Context) -> None:
        rng = random.Random(SEED + 913 * i)
        batch = sources({"Pre.A": f"def a := {rng.randrange(10000)}\n", "Pre.Z": f"def z := {rng.randrange(10000)}\n"})
        v = record(batch, request(c, batch), {"Pre.A": ("Init",), "Pre.Z": ()})
        altered = f"{rng.getrandbits(256):064x}"
        change_ = ("profile", "request", "recipe", "missing", "names", "digest", "outside")[i % 7]
        if i >= 7:
            misbinding(v, batch, "outside", altered)
        why = misbinding(v, batch, change_, altered)
        if i >= 14:
            v[f"unknown{rng.randrange(10000)}"] = rng.randrange(10000)
            why = "is malformed"
        inject(c, v, batch, BAD_RECORD + why)


for index in range(21):
    generated_mutation(index)


@case("snapshot.at-file-and-batch-cap", "D1/P6/U5 S1/P5b", "0; 16 × 1 MiB sources accepted at both inclusive caps")
def source_caps_inclusive(c: Context) -> None:
    batch = {f"Module{i:02}": b" " * SOURCE_FILE_BYTES for i in range(SOURCE_BATCH_BYTES // SOURCE_FILE_BYTES)}
    grammar = dict.fromkeys(batch, INIT)
    inject(c, record(batch, request(c, batch), grammar), batch, "accepted", grammar=grammar)


def cap_case(id_: str, text: str, limits: dict[str, int], want: str, grammar: Grammars) -> None:
    @case("cap." + id_, "R/P6/C1", f"{0 if want == 'accepted' else 2 if want.startswith('infra ') else 1}; {want}")
    def run(c: Context) -> None:
        check(c, sources({"Impl": text}), want, limits=limits, grammar=grammar)


cap_case("depth-at", DEEP, {"depth": DEEP_DEPTH}, "accepted", {"Impl": INIT})
cap_case("depth-over", DEEP, {"depth": DEEP_DEPTH - 1}, refusal(1, 15, "cap depth 8"), {"Impl": INIT})
cap_case("nodes-at", SIMPLE, {"nodes": SHALLOW_NODES}, "accepted", {"Impl": INIT})
cap_case("nodes-over", SIMPLE, {"nodes": SHALLOW_NODES - 1}, refusal(1, 0, "cap nodes 29"), {"Impl": INIT})
cap_case("batch-at", SIMPLE, {"batchNodes": SHALLOW_NODES}, "accepted", {"Impl": INIT})
cap_case("batch-over", SIMPLE, {"batchNodes": SHALLOW_NODES - 1}, IO + "the batch passed batchNodes 29", {})
cap_case("batch-first", SIMPLE, {"batchNodes": 29, "nodes": 29}, IO + "the batch passed batchNodes 29", {})
# D4 anchor: the first depth-9 occurrence of DEEP is ordinal 38 (header included), at 1:15.
cap_case("depth-before-nodes", DEEP, {"depth": 8, "nodes": 37}, refusal(1, 15, "cap depth 8"), {"Impl": INIT})
cap_case("batch-before-depth", DEEP, {"depth": 8, "nodes": 37, "batchNodes": 37},
         IO + "the batch passed batchNodes 37", {})
cap_case("cap-before-walk", "def a := (sorry)\n", {"depth": 5}, refusal(1, 9, "cap depth 5"), {"Impl": INIT})
cap_case("file-bytes", SIMPLE, {"fileBytes": 64}, IO + f"the parse step died by signal {FILE_SIGNAL}", {})
cap_case("deadline", SLOW, {"seconds": 1}, IO + "the parse step timed out after 1 s", {})


@case("cap.nodes-reset", "P6/C1", "0; nodes resets per module; exactly 60 batch occurrences fit")
def nodes_reset(c: Context) -> None:
    batch = sources({"A": SIMPLE, "B": SIMPLE})
    check(c, batch, grammar=dict.fromkeys(batch, INIT), limits={"nodes": 30, "batchNodes": 60})


@case("cap.batch-across-modules", "P6/C1", "2; batchNodes counts both modules, not their separate maxima")
def batch_across(c: Context) -> None:
    batch = sources({"A": SIMPLE, "B": SIMPLE})
    check(c, batch, IO + "the batch passed batchNodes 59", grammar={}, limits={"nodes": 30, "batchNodes": 59})


OUT = "/fvdep/work/out"


def script_result(data: bytes) -> str:
    return "exec /usr/bin/printf %s " + shlex.quote(data.decode()) + f" >{OUT}/results.json"


def u5_frame_size(data: bytes) -> int:
    status = jtext({"code": 0, "kind": "exited", "tmpFull": False, "workFull": False})
    return 8 + len("fvdep/step/1") + 8 + (16 + len(status)) + (16 + len("results.json") + len(data))


def child_scenario(c: Context, batch: Sources, id_: str, *, headers: Grammars | None = None) -> tuple[str, str, dict[str, int]]:
    data = jtext(record(batch, request(c, batch, headers=headers), dict.fromkeys(batch, INIT)))
    if id_ == "no-record":
        return "exit 0", IO + "the parse step wrote no result record", {}
    if id_ == "extra-file":
        return (f"touch {OUT}/z-extra {OUT}/a-extra\n" + script_result(data),
                IO + "the parse step wrote a-extra beside the result record", {})
    if id_ == "exit":
        return (script_result(data).removeprefix("exec ") + f"\ntouch {OUT}/a-extra\nexit 3",
                IO + "the parse step exited with code 3", {})
    if id_ == "signal":
        return 'kill -9 "$$"', IO + "the parse step died by signal 9", {}
    if id_ == "timeout":
        return "exec sleep 4", IO + "the parse step timed out after 1 s", {"seconds": 1}
    if id_ in {"frame-at", "frame-over"}:
        size = u5_frame_size(data) - int(id_ == "frame-over")
        want = "accepted" if id_ == "frame-at" else IO + f"the parse step's frame passed frameBytes {size}"
        return script_result(data), want, {"frameBytes": size}
    if id_ in {"file-at", "file-over"}:
        size = len(data) - int(id_ == "file-over")
        want = "accepted" if id_ == "file-at" else IO + f"the parse step died by signal {FILE_SIGNAL}"
        return script_result(data), want, {"fileBytes": size}
    raise AssertionError(f"unknown child scenario {id_}")


STEP_FAULTS = ("no-record", "extra-file", "exit", "signal", "timeout", "frame-over", "file-over")


def child_case(id_: str) -> None:
    @case("step." + id_, "R/P5c/P6/D1", f"{'0' if id_.endswith('-at') else '2'}; child {id_} disposition")
    def run(c: Context) -> None:
        script, want, limits = child_scenario(c, IMPL, id_)
        r = c.profile(c.trial(IMPL), list(IMPL), limits=limits, child=c.child(script), observe=True)
        grammar = dict.fromkeys(IMPL, INIT) if want == "accepted" else {}
        rest = output(c, r, IMPL, want, limits=limits, grammar=grammar)
        need(not rest, f"text after D1 outcome: {rest!r}")
        r.no_build(launches=1, child=True)


for scenario in (*STEP_FAULTS, "frame-at", "file-at"):
    child_case(scenario)


def check_phase_tail(r: Result, tail: list[str], *, parse: bool) -> None:
    labels = tuple((f"phase{n}", m) for n, m in ((1, "Impl"), (2, "Proof")))
    first = re.fullmatch(f"phase1 built ({HEX})", tail[0]) if len(tail) > 1 else None
    need(first is not None, f"missing phase1 built: {tail[:2]!r}")
    assert first is not None
    second = re.fullmatch(f"phase2 built ({HEX}) on {first[1]}", tail[1])
    need(second is not None, f"missing phase2 handoff: {tail[:2]!r}")
    assert second is not None
    expected = [pat for (phase, m), e in zip(labels, (first[1], second[1]), strict=True) for pat in (
        *(rf"artifact {phase} {m}\.{ext} [1-9][0-9]* {HEX}" for ext in ("c", "ilean", "olean")),
        rf"export {phase} exports/e{phase[-1]}\.ndjson [1-9][0-9]* {e}",
    )]
    need(len(tail[2:]) == len(expected) and all(re.fullmatch(w, a) for w, a in zip(expected, tail[2:], strict=True)),
         f"wrong phase artifact/export suffix: {tail[2:]!r}")
    argv = [step_argv(a) for a in r.launches]
    need(argv, "missing bwrap launches")
    if parse:
        need(any(a.rsplit("/", 1)[-1] == "fvdep-parse" for a in argv[0]), f"first launch not parse: {argv[0]!r}")
        argv = argv[1:]
    need(all(not any(a.rsplit("/", 1)[-1] == "fvdep-parse" for a in args) for args in argv), "extra parse launch")
    words = {a.rsplit("/", 1)[-1] for args in argv for a in args}
    need({"lean", "leanexport"} <= words, "accepted barrier did not reach compile and export")
    need(len(r.build_trace) == 1 and re.fullmatch(rf"{HEX} {re.escape(SPEC_MODULE)}", r.build_trace[0]),
         f"expected one cold library compile of {SPEC_MODULE}; got {r.build_trace!r}")


@case("phase.accepted", "R/D2/D3/B1/U5 D1/K7", "0; parse first, one cold library fill, phase1 + phase2 build and export")
def phase_accepted(c: Context) -> None:
    proj, proof = c.project(IMPL)
    r = c.phase(proj, c.library())
    tail = output(c, r, IMPL, "accepted", grammar=dict.fromkeys(IMPL, INIT), headers=LIBRARY_HEADERS, proof=proof)
    check_phase_tail(r, tail, parse=True)


@case("phase.frozen-source", "B2/D2/D3/U5 S2", "0; both phases use the frozen implementation despite a later live-file edit")
def phase_frozen_source(c: Context) -> None:
    proj, proof = c.project(IMPL)
    live = proj / module_path("Impl")
    changed = b"def ProfileTrial.impl : Nat := 2\n"
    r = c.phase(proj, c.library(), edit=(live, changed))
    tail = output(c, r, IMPL, "accepted", grammar=dict.fromkeys(IMPL, INIT), headers=LIBRARY_HEADERS, proof=proof)
    need(live.read_bytes() == changed, "live-source edit did not fire at the parse launch")
    check_phase_tail(r, tail, parse=True)


@case("phase.no-profile-reuse", "P5b/B2/D1", "0 twice; identical inputs each launch a new parser, never compile")
def repeated_profile(c: Context) -> None:
    src = c.trial(IMPL)
    for _ in range(2):
        r = c.profile(src, list(IMPL), observe=True)
        rest = output(c, r, IMPL, "accepted", grammar=dict.fromkeys(IMPL, INIT))
        need(not rest, f"text after D1 outcome: {rest!r}")
        r.no_build(launches=1)


def phase_failure(id_: str, text: str, want: str, grammar: Grammars, limits: dict[str, int] | None = None) -> None:
    @case("phase.refuse." + id_, "R/D2/D3/B1", f"{2 if want.startswith('infra ') else 1}; {want}; no compile")
    def run(c: Context) -> None:
        module = "Impl._x" if id_ == "header-name" else "Impl"
        batch = sources({module: text})
        proj, proof = c.project(batch)
        r = c.phase(proj, c.library(), limits=limits)
        tail = output(c, r, batch, want, grammar=grammar, headers=LIBRARY_HEADERS, limits=limits, proof=proof)
        need(not tail, f"phase effects after barrier failure: {tail!r}")
        r.no_build(launches=1)


for id_, text, line, col, cause in (
    ("parse", "def a := (1\n", 2, 0, EOF),
    ("scope", "open Array\n", 1, 5, "scope open Array"),
    ("ownership", "def Std.foo := 1\n", 1, 4, "ownership Std.foo"),
    ("kind", "def a := sorry\n", 1, 9, SORRY),
    ("shape", "structure S where\n  a : Nat\n  deriving Repr (x := 1)\n", 3, 11,
     "shape " + COMMAND + "derivingClass"),
    ("atom", "noncomputable section\nend\n", 1, 0, "atom " + COMMAND + "sectionHeader noncomputable"),
    ("reserved", "def f (_x : Nat) := 1\n", 1, 7, "reserved _x"),
    ("name", "structure S where\n  a : Nat\n  deriving Repr, ToJson\n", 3, 17, "name deriving ToJson"),
):
    phase_failure(id_, text, refusal(line, col, cause), {"Impl": INIT})

phase_failure("import", "import Lean\n" + PHASE_IMPL, refusal(1, 0, "header import Lean"), {})
phase_failure("header-parse", "public import Std\n", refusal(1, 0, "parse cannot use `public import` without `module`"), {})
phase_failure("header-name", PHASE_IMPL, refusal(1, 0, "header name Impl._x", "Impl._x"), {})
phase_failure("depth", DEEP, refusal(1, 15, "cap depth 8"), {"Impl": INIT}, {"depth": 8})
phase_failure("nodes", SIMPLE, refusal(1, 0, "cap nodes 29"), {"Impl": INIT}, {"nodes": 29})
phase_failure("batch", SIMPLE, IO + "the batch passed batchNodes 29", {}, {"batchNodes": 29})
phase_failure("deadline", SLOW, IO + "the parse step timed out after 1 s", {}, {"seconds": 1})
phase_failure("file-bytes", PHASE_IMPL, IO + f"the parse step died by signal {FILE_SIGNAL}", {}, {"fileBytes": 64})


def phase_record(id_: str) -> None:
    @case("phase.record." + id_, "R/P5b/D2/D3", "2; exact record refusal without a sandbox launch or compile")
    def run(c: Context) -> None:
        batch = PAIR
        proj, proof = c.project(batch)
        v = record(batch, request(c, batch, headers=LIBRARY_HEADERS), dict.fromkeys(batch, INIT))
        if id_ == "malformed":
            v["schema"] = "1"
            why = "is malformed"
        else:
            why = misbinding(v, batch, id_)
        r = c.phase(proj, c.library(), results=input_record(c, v))
        rest = output(c, r, batch, BAD_RECORD + why, headers=LIBRARY_HEADERS, proof=proof)
        need(not rest, f"phase effects after failed intake: {rest!r}")
        r.no_build(launches=0)


for field in ("malformed", *BINDINGS):
    phase_record(field)


def phase_child(id_: str) -> None:
    @case("phase.step." + id_, "R/P5c/D2/D3", "2; exact child fault, one parse launch, no compile")
    def run(c: Context) -> None:
        proj, proof = c.project(IMPL)
        script, want, limits = child_scenario(c, IMPL, id_, headers=LIBRARY_HEADERS)
        r = c.phase(proj, c.library(), limits=limits, child=c.child(script))
        rest = output(c, r, IMPL, want, headers=LIBRARY_HEADERS, limits=limits, proof=proof)
        need(not rest, f"phase effects after child fault: {rest!r}")
        r.no_build(launches=1, child=True)


for scenario in STEP_FAULTS:
    phase_child(scenario)


@case("phase.step.setup", "P5c/D2/D3/interface §1", "2; bwrap setup failure, control-free line, no compile")
def setup_failure(c: Context) -> None:
    proj, proof = c.project(IMPL)
    r = c.phase(proj, c.library(), fault="setup")
    rest = output(c, r, IMPL, "infra sandbox_setup: profile, fixture setup error \x1b",
                  headers=LIBRARY_HEADERS, proof=proof)
    need(not rest, f"phase effects after failed setup: {rest!r}")
    r.no_build(launches=1)


@case("phase.step.old-bwrap", "P5c/D2/D3/U5 T1", "2; tool_missing names bwrap; version query only")
def old_bwrap(c: Context) -> None:
    proj, _ = c.project(IMPL)
    r = c.phase(proj, c.library(), fault="old-version")
    r.code(2)
    need(any("tool_missing" in line and "bwrap" in line for line in r.output + lines(r.err)),
         f"expected tool_missing naming bwrap: {r.output!r} {r.err!r}")
    r.no_build(launches=0)


@case("phase.snapshot.link", "R/D2/D3/U5 S1", "2; S1 symbolic-link refusal before source digests or launch")
def phase_link(c: Context) -> None:
    proj, _ = c.project(IMPL)
    link = proj / module_path("Impl")
    link.unlink()
    link.symlink_to(put(c.directory, "copy.lean", PHASE_IMPL))
    early_snapshot(c.phase(proj, c.library()), "Impl.lean")


@case("phase.manifest.reserved", "R/D2/D3/U3 T3", "2; schema names impl_modules; no launch")
def manifest_reserved(c: Context) -> None:
    proj, _ = c.project(IMPL, modules=["Fvdep.Impl"])
    r = c.phase(proj, c.library())
    r.code(2)
    need(any("schema" in line and "impl_modules" in line for line in r.output + lines(r.err)),
         f"expected schema refusal naming impl_modules: {r.output!r} {r.err!r}")
    r.no_build(launches=0)
