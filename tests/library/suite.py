"""Blind U4 A/B acceptance suite. Stdlib-only; source clauses in COVERAGE.tsv."""
from __future__ import annotations

import argparse
import dataclasses
import importlib.util
import json
import os
from pathlib import Path
import random
import subprocess
import time
from typing import Any, Callable

# -I intentionally omits the script directory from sys.path.
_spec = importlib.util.spec_from_file_location("library_reference", Path(__file__).with_name(
    "reference.py"))
assert _spec is not None and _spec.loader is not None
ref: Any = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

DEFAULT_SEED = 0xF4DE_0401
MAX = (1 << 53) - 1
A64 = "U4 A4/A5; RFC4648 §§3.2–3.5,4,5,10"
ASEM = "U4 A4/A5; SemVer2 §§2,9,10,11; library whole-type compare"
BVAL = "U4 B1/B2; interface §8"
BREQ = "U4 B3; U3 J1–J3; interface §8"
BREPLY = "U4 B3/B4 ReplyLayout; U3 J4"
BSIG = "U4 B1/B4 SigExact"
BCLI = "U4 B5; interface §8"


class CheckFailure(Exception):
    pass


def brief(value: Any) -> str:
    text = repr(value)
    return text if len(text) < 280 else text[:230] + f"… ({len(text)} chars)"


def equal(got: Any, want: Any, context: str = "") -> None:
    if got != want:
        raise CheckFailure(f"{context} got={brief(got)} want={brief(want)}")


class Driver:
    def __init__(self, binary: Path):
        self.binary = str(binary.resolve())
        self.cache: dict[bytes, Any] = {}

    def call(self, command: Any) -> Any:
        key = ref.wire(command)
        if key in self.cache:
            return self.cache[key]
        proc = subprocess.run([self.binary], input=key.hex().encode() + b"\n",
                              capture_output=True, timeout=120, check=False)
        if proc.returncode != 0:
            raise CheckFailure(f"driver exit {proc.returncode}: {brief(proc.stderr)}")
        rows = proc.stdout.splitlines()
        if len(rows) != 1:
            raise CheckFailure(f"driver replies={len(rows)} expected=1")
        try:
            value = ref.unwire(bytes.fromhex(rows[0].decode()))
        except (ValueError, IndexError) as exc:
            raise CheckFailure(f"driver transport: {exc}") from exc
        self.cache[key] = value
        return value

    def batch(self, commands: list[Any]) -> list[Any]:
        values: list[Any] = []
        for offset in range(0, len(commands), 128):
            value = self.call(["batch", commands[offset:offset + 128]])
            if not isinstance(value, list):
                raise CheckFailure("driver batch not a list")
            values.extend(value)
        equal(len(values), len(commands), "batch length")
        return values


@dataclasses.dataclass
class Case:
    name: str
    clause: str
    domain: str
    check: Callable[[], None]


class Suite:
    def __init__(self, driver: Driver, oracle: Path, seed: int):
        self.driver = driver
        self.oracle = str(oracle.resolve())
        self.seed = seed
        self.cases: list[Case] = []
        self.exhaustive: dict[int, list[Any]] = {}

    def add(self, name: str, clause: str, domain: str, check: Callable[[], None]) -> None:
        self.cases.append(Case(name, clause, domain, check))

    def exact(self, name: str, clause: str, command: Any, want: Any,
              domain: str = "named example") -> None:
        self.add(name, clause, domain,
                 lambda: equal(self.driver.call(command), want, brief(command)))

    def many(self, name: str, clause: str, commands: list[Any], wants: list[Any],
             domain: str) -> None:
        def check() -> None:
            got = self.driver.batch(commands)
            for i, (actual, expected) in enumerate(zip(got, wants, strict=True)):
                equal(actual, expected, f"sample={i} {brief(commands[i])}")
        self.add(name, clause, domain, check)

    def oracle_run(self, target: str, data: bytes) -> subprocess.CompletedProcess[bytes]:
        return subprocess.run([self.oracle, "oracle", target], input=data, capture_output=True,
                              timeout=120, check=False)

    def cli_exact(self, name: str, target: str, data: bytes, want: bytes,
                  domain: str = "exact stdout bytes + exit 0") -> None:
        def check() -> None:
            proc = self.oracle_run(target, data)
            equal(proc.returncode, 0, "oracle exit")
            equal(proc.stdout, want, "oracle stdout")
        self.add(name, BCLI, domain, check)

    def build_base64(self) -> None:
        vectors = [(b"", ""), (b"f", "Zg=="), (b"fo", "Zm8="), (b"foo", "Zm9v"),
                   (b"foob", "Zm9vYg=="), (b"fooba", "Zm9vYmE="),
                   (b"foobar", "Zm9vYmFy")]
        for i, (data, text) in enumerate(vectors):
            for suffix, enc, dec in (("std", "encode", "decode"),
                                     ("url", "encodeUrl", "decodeUrl")):
                self.exact(f"A.b64.vector.{i}.{suffix}.encode", A64,
                           ["spec", enc, data.hex()], text, "RFC4648 §10 vector")
                self.exact(f"A.b64.vector.{i}.{suffix}.decode", A64,
                           ["spec", dec, text], [data.hex()], "RFC4648 §10 vector")
        for size in (1, 2):
            def exhaustive(column: int, size: int = size) -> None:
                if size not in self.exhaustive:
                    values = []
                    count = 256 ** size
                    for offset in range(0, count, 512):
                        inputs = [n.to_bytes(size, "big").hex()
                                  for n in range(offset, min(offset + 512, count))]
                        result = self.driver.call(["base64", inputs])
                        equal(len(result), len(inputs), "exhaustive batch")
                        values.extend(result)
                    self.exhaustive[size] = values
                for n, row in enumerate(self.exhaustive[size]):
                    data = n.to_bytes(size, "big")
                    want = (ref.b64encode(data), ref.b64encode(data, True),
                            [data.hex()], [data.hex()])[column]
                    equal(row[column], want, f"input={data.hex()}")
            for column, label in enumerate(("encode", "encodeUrl", "roundtrip", "roundtripUrl")):
                self.add(f"A.b64.exhaustive.{size}.{label}", A64,
                         f"all {256 ** size} {size}-byte inputs",
                         lambda column=column, exhaustive=exhaustive: exhaustive(column))
        rng = random.Random(self.seed)
        samples = [bytes(rng.randrange(256) for _ in range(n))
                   for n in list(range(130)) + [255, 256, 257, 1023, 1024, 1025]]
        for op, url in (("encode", False), ("encodeUrl", True)):
            self.many(f"A.b64.generated.{op}", A64,
                      [["spec", op, data.hex()] for data in samples],
                      [ref.b64encode(data, url) for data in samples],
                      f"seeded {len(samples)} inputs; lengths 0..129 + block boundaries")
        refusals = {
            "length1": "A", "length2": "AA", "length3": "AAA", "length5": "AAAAA",
            "padding1": "=AAA", "padding2": "A=AA", "padding3": "AA=A",
            "padding4": "====", "padding3only": "A===", "padding5": "AA===",
            "padding-tail-missing": "AA=", "padding-after-full": "AAAA=",
            "padding-interior": "AA==AAAA", "padding-interior3": "AAA=AAAA",
            "padding-double-group": "AA==AA==", "padding-then-char": "AA==A",
            "space": "AA A", "tab": "AA\tA", "lf": "AAA\n", "crlf": "AA\r\n",
            "space-around": " AAAA ", "nul": "AA\0A", "del": "AA\x7fA",
            "nonascii-latin": "AAéA", "nonascii-bmp": "AA中A",
            "nonascii-nonbmp": "AA😀A", "nonascii-fullwidth": "ＡＡＡＡ",
            "bits-one-byte": "AB==", "bits-two-byte": "AAB=",
        }
        for op, url in (("decode", False), ("decodeUrl", True)):
            for label, text in refusals.items():
                self.exact(f"A.b64.refuse.{op}.{label}", A64, ["spec", op, text], [])
            foreign = "-_" if not url else "+/"
            for i, char in enumerate(foreign):
                self.exact(f"A.b64.refuse.{op}.foreign{i}", A64,
                           ["spec", op, char + "AAA"], [])
            alphabet = ref.URL if url else ref.STANDARD
            filling = ["A" + alphabet[index] + "==" for index in range(64) if index % 16]
            filling += ["AA" + alphabet[index] + "=" for index in range(64) if index % 4]
            self.many(f"A.b64.filling-bits.{op}", A64,
                      [["spec", op, text] for text in filling], [[] for _ in filling],
                      f"all {len(filling)} nonzero low 4/2-bit tails")
            padding = []
            for length in (4, 8):
                for mask in range(1 << length):
                    padding.append("".join("=" if mask & (1 << i) else "A"
                                           for i in range(length)))
            self.many(f"A.b64.padding-masks.{op}", A64,
                      [["spec", op, text] for text in padding],
                      [[] if (decoded := ref.b64decode(text, url)) is None
                       else [decoded.hex()] for text in padding],
                      "all 272 '=' position masks at 4/8 characters")
            ascii_cases = ["AAAA"[:position] + chr(char) + "AAAA"[position + 1:]
                           for char in range(128) for position in range(4)]
            self.many(f"A.b64.ascii-domain.{op}", A64,
                      [["spec", op, text] for text in ascii_cases],
                      [[] if (decoded := ref.b64decode(text, url)) is None
                       else [decoded.hex()] for text in ascii_cases],
                      "every ASCII character in each of four positions (512 inputs)")
            texts = [ref.b64encode(data, url) for data in samples]
            self.many(f"A.b64.generated.inverse.{op}", A64,
                      [["spec", op, text] for text in texts],
                      [[data.hex()] for data in samples], "seeded independent encoder inverse")
            mutated = []
            for text in texts[1:]:
                position = rng.randrange(len(text))
                replacement = rng.choice(alphabet + "=!?\n_")
                mutated.append(text[:position] + replacement + text[position + 1:])
            self.many(f"A.b64.generated.canonical.{op}", A64,
                      [["spec", op, text] for text in mutated],
                      [[] if (decoded := ref.b64decode(text, url)) is None
                       else [decoded.hex()] for text in mutated],
                      "seeded canonical/refusal differential; independent bit decoder")

    def build_semver(self) -> None:
        accepted = ["0.0.0", "1.2.3", "1.0.0-0", "1.0.0-1", "1.0.0-alpha",
                    "1.0.0-alpha.1", "1.0.0-0A", "1.0.0-a-", "1.0.0--",
                    "1.0.0---", "1.0.0-123a", "1.0.0-a.0.9.z",
                    "1.0.0+0", "1.0.0+001", "1.0.0+-", "1.0.0+foo-bar",
                    "1.0.0-alpha+001.x-", "1.0.0-a-b+c-d.e", "1.0.0-01a",
                    "9" * 256 + ".0.0", "0." + "8" * 256 + ".0",
                    "0.0." + "7" * 256, "0.0.0-" + "6" * 256,
                    "0.0.0+" + "0" * 256, "1.0.0-Z.a.A.9.10"]
        refused = ["", "1", "1.2", "1.2.3.4", ".1.2", "1..2", "1.2.",
                   "01.2.3", "1.02.3", "1.2.03", "00.0.0", "+1.2.3", "-1.2.3",
                   "v1.2.3", "V1.2.3", " 1.2.3", "1.2.3 ", "1.2.3\n", "1.2.3\t",
                   "1.2.3-", "1.2.3+", "1.2.3-.a", "1.2.3-a.", "1.2.3-a..b",
                   "1.2.3+.a", "1.2.3+a.", "1.2.3+a..b", "1.2.3-01", "1.2.3-00",
                   "1.2.3-a.01", "1.2.3+foo+bar", "1.2.3-a+b+c", "1.2.3-a_b",
                   "1.2.3+a_b", "1.2.3-α", "1.2.3+é", "１.2.3", "1.٢.3",
                   "1.2.3-٠", "1.2.3-a b", "1.2.3-a/b", "1.2.3\0", "1.2.3-😀"]
        for i, text in enumerate(accepted):
            parsed = ref.parse(text)
            assert parsed is not None, text
            self.exact(f"A.semver.parse.accept.{i:02}", ASEM,
                       ["spec", "parse", text], [parsed], f"grammar witness {text[:55]!r}")
            self.exact(f"A.semver.render.{i:02}", ASEM,
                       ["spec", "render", parsed], text, "canonical rendering witness")
        for i, text in enumerate(refused):
            assert ref.parse(text) is None, text
            self.exact(f"A.semver.parse.refuse.{i:02}", ASEM,
                       ["spec", "parse", text], [], f"grammar refusal {text!r}")
        chain = ["1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta",
                 "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"]
        commands, wants = [], []
        for i, a in enumerate(chain):
            for j, b in enumerate(chain):
                commands.append(["spec", "compare", ref.parse(a), ref.parse(b)])
                wants.append("lt" if i < j else "gt" if i > j else "eq")
        self.many("A.semver.precedence-chain", ASEM, commands, wants,
                  "all 64 ordered pairs in SemVer §11 chain")
        witnesses = [
            (ref.version(pre=[{"num": 9}]), ref.version(pre=[{"num": 10}])),
            (ref.version(pre=[{"num": 10**180}]), ref.version(pre=[{"alnum": ""}])),
            (ref.version(pre=[{"alnum": ""}]), ref.version(pre=[{"alnum": "0"}])),
            (ref.version(pre=[{"alnum": "9"}]), ref.version(pre=[{"alnum": "10"}])),
            (ref.version(pre=[{"alnum": "a"}]),
             ref.version(pre=[{"alnum": "a"}, {"num": 0}])),
            (ref.version(pre=[{"alnum": "Z"}]), ref.version(pre=[{"alnum": "a"}])),
            (ref.version(pre=[{"alnum": "é"}]), ref.version(pre=[{"alnum": "😀"}])),
            (ref.version(pre=[{"alnum": "\0"}]), ref.version(pre=[{"alnum": ""}])),
            (ref.version(build=["x"]), ref.version(build=["y", ""])),
            (ref.version(2, 0, 0, [{"num": 0}]), ref.version(1, 999, 999)),
            (ref.version(1, 2, 0, [{"num": 0}]), ref.version(1, 1, 999)),
            (ref.version(1, 0, 2, [{"num": 0}]), ref.version(1, 0, 1)),
        ]
        for i, (a, b) in enumerate(witnesses):
            self.exact(f"A.semver.whole-type.{i:02}", ASEM,
                       ["spec", "compare", a, b], ref.compare(a, b), "whole-type witness")
        rng = random.Random(self.seed ^ 0x5E4)
        valid = [self.generated_version(rng, True) for _ in range(256)]
        self.many("A.semver.generated.render", ASEM,
                  [["spec", "render", value] for value in valid],
                  [ref.render(value) for value in valid], "256 grammar-valid generated values")
        self.many("A.semver.generated.render-roundtrip", ASEM,
                  [["spec", "parse", ref.render(value)] for value in valid],
                  [[value] for value in valid], "256 Valid values; parse(render(v)) = v")
        triples = [[self.generated_version(rng, False) for _ in range(3)] for _ in range(256)]
        # Correlated triples exercise the non-core tie paths, not just differing majors.
        for i in range(32):
            variants: list[list[dict[str, Any]]] = [[{"num": i}], [{"alnum": ""}], []]
            triples.append([ref.version(pre=pre, build=[str(i)]) for pre in variants])
            tied = self.generated_version(rng, False)
            triples.append([tied, {**tied, "build": ["different", ""]}, tied])
        orders: list[tuple[list[dict[str, Any]], list[str]]] = []
        def get_orders() -> list[tuple[list[dict[str, Any]], list[str]]]:
            if not orders:
                calls = [["spec", "compare", values[i], values[j]]
                         for values in triples for i, j in
                         ((0, 1), (1, 0), (1, 2), (0, 2), (0, 0))]
                results = self.driver.batch(calls)
                orders.extend((values, results[k * 5:(k + 1) * 5])
                              for k, values in enumerate(triples))
            return orders
        def law(label: str) -> None:
            for values, results in get_orders():
                a, b, c = values
                ab, ba, bc, ac, aa = results
                if label == "swap":
                    equal(ab, {"lt": "gt", "eq": "eq", "gt": "lt"}.get(ba), brief(values))
                elif label == "trans":
                    if ab != "gt" and bc != "gt":
                        equal(ac != "gt", True, brief([a, b, c]))
                elif label == "eqIff":
                    equal(ab == "eq", {**a, "build": []} == {**b, "build": []}, brief(values))
                    equal(aa, "eq", "reflexivity")
                else:
                    equal(ab, ref.compare(a, b), brief(values))
                    equal(bc, ref.compare(b, c), brief(values))
                    equal(ac, ref.compare(a, c), brief(values))
        for label in ("swap", "trans", "eqIff", "precedence"):
            self.add(f"A.semver.property.{label}", ASEM,
                     f"{len(triples)} seeded whole-type triples incl. invalid alnum/build",
                     lambda label=label: law(label))
        builds = [self.generated_version(rng, False) for _ in range(64)]
        self.many("A.semver.property.build-ignored", ASEM,
                  [["spec", "compare", value, {**value, "build": ["", "😀", "0"]}]
                   for value in builds], ["eq"] * len(builds), "64 arbitrary whole-type versions")

    @staticmethod
    def generated_version(rng: random.Random, valid: bool) -> dict[str, Any]:
        numbers = [0, 1, 2, 9, 10, MAX, MAX + 1, 10**128]
        pre: list[dict[str, Any]] = []
        for _ in range(rng.randrange(5)):
            if rng.randrange(2):
                pre.append({"num": rng.choice(numbers)})
            else:
                options = ["a", "Z", "alpha", "1a", "-", "a-b"] if valid else [
                    "", "0", "10", "01", "a", "é", "😀", "\0", "a.b", "-", "𝄞"]
                pre.append({"alnum": rng.choice(options)})
        build_options = ["0", "001", "x", "A-0"] if valid else ["", "😀", "a.b", "\0", "001"]
        build = [rng.choice(build_options) for _ in range(rng.randrange(4))]
        return ref.version(*(rng.choice(numbers) for _ in range(3)), pre=pre, build=build)

    def value(self, label: str, typed: list[Any]) -> None:
        encoded = ref.encode_value(typed)
        self.exact(f"B.value.encode.{label}", BVAL, ["encodeVal", typed], encoded)
        self.exact(f"B.value.decode.{label}", BVAL,
                   ["decodeVal", typed[0], encoded], [typed])

    def refusal(self, label: str, ty: str, value: Any) -> None:
        self.exact(f"B.value.refuse.{ty}.{label}", BVAL, ["decodeVal", ty, value], [])

    def build_values(self) -> None:
        for i, data in enumerate((b"", b"\0", b"\xff", b"\x01\xab\xef", bytes(range(256)))):
            self.value(f"bytes.{i}", ["bytes", data.hex()])
        for label, text in (("empty", ""), ("ascii", "abcXYZ09"),
                            ("controls", "".join(chr(i) for i in range(33)) + "\x7f"),
                            ("unicode", "é中😀  ﻿﷐￿\U0010ffff"),
                            ("cap-ascii", "x" * 65536), ("cap-utf8", "é" * 32768),
                            ("cap-nonbmp", "😀" * 16384)):
            self.value(f"text.{label}", ["text", text])
        for i, codes in enumerate(([], [0], [65535], [0, 65535, 55296, 56320, 65])):
            self.value(f"utf16.{i}", ["utf16", codes])
        for i, number in enumerate((0, 1, MAX - 1, MAX, MAX + 1, 2**64, 10**256)):
            self.value(f"nat.{i}", ["nat", number])
        ints = (0, 1, -1, MAX, -MAX, MAX + 1, -MAX - 1, 2**64, -(2**64), 10**256, -(10**256))
        for i, number in enumerate(ints):
            self.value(f"int.{i}", ["int", number])
        for order in ("lt", "eq", "gt"):
            self.value(f"ordering.{order}", ["ordering", order])
        versions = [ref.version(0), ref.version(MAX, MAX + 1, 10**128,
                    [{"num": 0}, {"num": MAX + 1}, {"alnum": ""}, {"alnum": "001"}],
                    ["", "😀", "a.b", "\0"]), ref.version(pre=[{"alnum": "\U0010ffff"}])]
        for i, value in enumerate(versions):
            self.value(f"version.{i}", ["version", value])
        for i, value in enumerate(("A0", "abCD", "f", "fff", "gg", "00 ", " 00", "0x00",
                                   "éé", "\0\0", "+0", "-0")):
            self.refusal(str(i), "bytes", value)
        for ty in ("nat", "int"):
            strings = ["0", "1", str(MAX), "00", "01", "+9007199254740992",
                       "09007199254740992", "9007199254740992 ", " 9007199254740992",
                       "9e20", "9007199254740992.0", "９００７１９９２５４７４０９９２", "", "-0"]
            if ty == "nat":
                strings += ["-1", "-9007199254740992", "-09007199254740992"]
            else:
                strings += ["-1", str(-MAX), "-09007199254740992", "--9007199254740992"]
            for i, value in enumerate(strings):
                self.refusal(f"decimal.{i}", ty, value)
            for i, value in enumerate((MAX + 1, -MAX - 1)):
                self.refusal(f"integer-range.{i}", ty, value)
        self.refusal("negative", "nat", -1)
        for i, value in enumerate(([-1], [65536], [0, 65536], ["0"], [True], [None], [[0]])):
            self.refusal(f"codeunit.{i}", "utf16", value)
        for i, value in enumerate(("LT", "less", "", "0", "Eq")):
            self.refusal(str(i), "ordering", value)
        wrong_kinds = {
            "bytes": [None, True, 0, [], {}], "text": [None, False, 0, [], {}],
            "utf16": [None, True, 0, "", {}], "nat": [None, True, [], {}],
            "int": [None, False, [], {}], "ordering": [None, True, 0, [], {}],
            "version": [None, False, 0, "", []],
        }
        for ty, values in wrong_kinds.items():
            for i, value in enumerate(values):
                self.refusal(f"kind.{i}", ty, value)
        base = ref.encode_value(["version", ref.version()])
        for key in sorted(base):
            self.refusal(f"missing.{key}", "version", {k: v for k, v in base.items() if k != key})
        self.refusal("extra", "version", {**base, "extra": 0})
        for key in ("major", "minor", "patch"):
            for i, bad in enumerate((-1, "0", "+9007199254740992", None, [])):
                self.refusal(f"{key}.{i}", "version", {**base, key: bad})
        bad_pre = [None, {}, "", [0], ["a"], [{}], [{"num": 0, "alnum": "0"}],
                   [{"num": 0, "extra": 0}], [{"unknown": "a"}], [{"num": -1}],
                   [{"num": "0"}], [{"alnum": 0}], [{"alnum": None}]]
        for i, value in enumerate(bad_pre):
            self.refusal(f"pre.{i}", "version", {**base, "pre": value})
        for i, value in enumerate((None, {}, "", [0], [False], [None], [[]])):
            self.refusal(f"build.{i}", "version", {**base, "build": value})
        rng = random.Random(self.seed ^ 0xB2)
        generated: list[list[Any]] = []
        for i in range(160):
            ty = i % 7
            if ty == 0:
                value = ["bytes", bytes(rng.randrange(256) for _ in range(i % 33)).hex()]
            elif ty == 1:
                value = ["text", "".join(rng.choice("aé中😀\0\n\x7f") for _ in range(i % 33))]
            elif ty == 2:
                value = ["utf16", [rng.randrange(65536) for _ in range(i % 33)]]
            elif ty == 3:
                value = ["nat", rng.randrange(1 << rng.randrange(1, 256))]
            elif ty == 4:
                value = ["int", rng.randrange(-(1 << 128), 1 << 128)]
            elif ty == 5:
                value = ["ordering", rng.choice(["lt", "eq", "gt"])]
            else:
                value = ["version", self.generated_version(rng, False)]
            generated.append(value)
        self.many("B.value.property.encode-layout", BVAL,
                  [["encodeVal", value] for value in generated],
                  [ref.encode_value(value) for value in generated],
                  "160 seeded typed values across all seven Ty constructors")
        self.many("B.value.property.decode-encode", BVAL,
                  [["decodeVal", value[0], ref.encode_value(value)] for value in generated],
                  [[value] for value in generated], "160 independent layout round trips")

    def request_check(self, label: str, sig: list[Any], data: bytes,
                      want: list[Any] | None) -> None:
        def check() -> None:
            got = self.driver.call(["request", sig, data.hex()])
            if want is None:
                if not (isinstance(got, list) and len(got) == 2 and got[0] == "invalid"
                        and isinstance(got[1], str)):
                    raise CheckFailure(f"expected invalid String, got={brief(got)}")
            else:
                equal(got, ["ok", want], brief(data))
        self.add(f"B.request.{label}", BREQ, f"line bytes={len(data)}", check)

    def build_requests(self) -> None:
        sig = ["echo", ["text"], ["plain", "text"]]
        positive = {
            "empty-text": ref.request("echo", [""]),
            "unicode": ref.request("echo", ["😀\0é\x7f"]),
            "order-whitespace": b' \t { "op" : "echo", "args" : ["x"] } \r ',
            "escape-pair": b'{"op":"echo","args":["\\ud83d\\ude00"]}',
            "escaped-keys": b'{"o\\u0070":"echo","ar\\u0067s":["x"]}',
            "slash": b'{"op":"echo","args":["a\\/b"]}',
            "cap-ascii": ref.request("echo", ["x" * 65536]),
            "cap-multibyte": ref.request("echo", ["é" * 32768]),
        }
        for label, data in positive.items():
            text = json.loads(data)["args"][0]
            self.request_check(label, sig, data, [["text", text]])
        bad = {
            "empty-line": b"", "whitespace": b" \t\r", "malformed": b"{",
            "null": b"null", "array": b"[]", "string": b'"hello"',
            "missing-op": b'{"args":["x"]}', "missing-args": b'{"op":"echo"}',
            "extra": b'{"op":"echo","args":["x"],"x":0}',
            "op-kind": b'{"op":0,"args":["x"]}',
            "args-kind": b'{"op":"echo","args":"x"}',
            "wrong-op": ref.request("Echo", ["x"]),
            "zero-arity": ref.request("echo", []), "two-arity": ref.request("echo", ["x", "y"]),
            "wrong-arg": ref.request("echo", [0]),
            "duplicate-op": b'{"op":"echo","op":"echo","args":["x"]}',
            "duplicate-escaped": b'{"op":"echo","o\\u0070":"echo","args":["x"]}',
            "lone-high": b'{"op":"echo","args":["\\ud800"]}',
            "lone-low": b'{"op":"echo","args":["\\udfff"]}',
            "high-then-text": b'{"op":"echo","args":["\\ud800x"]}',
            "encoded-surrogate": b'{"op":"echo","args":["\xed\xa0\x80"]}',
            "utf8-overlong": b'{"op":"echo","args":["\xc0\xaf"]}',
            "utf8-stray": b'{"op":"echo","args":["\x80"]}',
            "utf8-high": b'{"op":"echo","args":["\xf4\x90\x80\x80"]}',
            "bom": b'\xef\xbb\xbf{"op":"echo","args":["x"]}',
            "raw-control": b'{"op":"echo","args":["\x00"]}',
            "cap-plus-one": ref.request("echo", ["x" * 65537]),
            "cap-multibyte-plus": ref.request("echo", ["é" * 32768 + "a"]),
            "depth33": b'{"op":"echo","args":' + b"[" * 32 + b"0" + b"]" * 32 + b"}",
            "depth-priority": b"x" + b"[" * 33,
            "trailing": ref.request("echo", ["x"]) + b"x",
            "trailing-json": ref.request("echo", ["x"]) + b"null",
            "trailing-comma": b'{"op":"echo","args":["x",]}',
        }
        for label, data in bad.items():
            self.request_check(label, sig, data, None)
        typed_cases: list[tuple[str, Any, list[Any]]] = [
            ("bytes", "00ff", ["00FF", "f", "gg", []]),
            ("utf16", [0, 65535, 55296], [[-1], [65536], [True], "abc"]),
            ("nat", str(MAX + 1), [-1, str(MAX), "01", MAX + 1]),
            ("int", str(-MAX - 1), [str(-MAX), "-0", "+9007199254740992", -MAX - 1]),
            ("ordering", "lt", ["LT", 0, True]),
            ("version", ref.encode_value(["version", ref.version(pre=[{"alnum": ""}])]),
             [{}, {"build": [], "major": 1, "minor": 0, "patch": 0, "pre": [{"num": 0,
                "alnum": "0"}]}]),
        ]
        for ty, good, bads in typed_cases:
            typed_good = [ty, (bytes.fromhex(good).hex() if ty == "bytes" else
                               int(good) if ty in ("nat", "int") else
                               ref.version(pre=[{"alnum": ""}]) if ty == "version" else good)]
            typed_sig = ["f", [ty], ["plain", ty]]
            self.request_check(f"typed.{ty}.accept", typed_sig, ref.request("f", [good]),
                               [typed_good])
            for i, value in enumerate(bads):
                self.request_check(f"typed.{ty}.refuse.{i}", typed_sig,
                                   ref.request("f", [value]), None)
        numeric_sig = ["f", ["int"], ["plain", "int"]]
        for i, lexeme in enumerate((b"-0", b"1.0", b"1e0", b"+1", b"01", b"9007199254740992")):
            self.request_check(f"json-number.{i}", numeric_sig,
                               b'{"op":"f","args":[' + lexeme + b"]}", None)
        pair = ["pair", ["nat", "text"], ["plain", "nat"]]
        self.request_check("two-args.accept", pair, ref.request("pair", [0, "x"]),
                           [["nat", 0], ["text", "x"]])
        self.request_check("two-args.wrong-order", pair, ref.request("pair", ["x", 0]), None)

    def build_reply_lines(self) -> None:
        replies = [["bytes", "00ff"], ["text", ""], ["text", "\0\b\t\n\f\r\x1f\x7f\"\\/é😀"],
                   ["utf16", [0, 65535]], ["nat", MAX], ["nat", MAX + 1],
                   ["int", -MAX - 1], ["ordering", "eq"], ["version", ref.version(
                       pre=[{"num": 0}, {"alnum": "0"}], build=[""])],
                   ["bytes", "ff" * 49152], ["text", "x" * 65537]]
        for i, typed in enumerate(replies):
            self.exact(f"B.reply.ok.{i:02}", BREPLY, ["reply", "ok", typed],
                       (ref.canonical({"ok": ref.encode_value(typed)}) + b"\n").hex(),
                       f"canonical bytes + LF; {typed[0]} value")
        self.exact("B.reply.none", BREPLY, ["reply", "none"], b'{"err":"none"}\n'.hex())
        for i, reason in enumerate(("", "bad request", "\0\n\x7f😀", "x" * 65537)):
            self.exact(f"B.reply.invalid.{i}", BREPLY, ["reply", "invalid", reason],
                       (ref.canonical({"invalid": reason}) + b"\n").hex(),
                       "free-text invalid reason; canonical total printer")
        fragments = [b"", b"\n", b"\n\n", b"a", b"a\n", b"a\nb", b"a\nb\n",
                     b"\r\n", b"a\r\nb\r\n", b"\r", b"a\n\nb", b"\xff\n\0",
                     b"\nlast", b"\nlast\n"]
        for i, data in enumerate(fragments):
            parts = data.split(b"\n")
            if parts[-1] == b"":
                parts.pop()
            self.exact(f"B.lines.{i:02}", "U4 B3 lines", ["lines", data.hex()],
                       [part.hex() for part in parts], "byte LF framing; EOF adds no request")
        rng = random.Random(self.seed ^ 0xB3)
        inputs = [bytes(rng.choice([0, 10, 13, 65, 127, 255]) for _ in range(i))
                  for i in range(128)]
        wants = []
        for data in inputs:
            parts = data.split(b"\n")
            if parts[-1] == b"":
                parts.pop()
            wants.append([part.hex() for part in parts])
        self.many("B.lines.property.framing", "U4 B3 lines", [["lines", x.hex()] for x in inputs],
                  wants, "128 arbitrary byte streams; includes empty LF lines + final fragment")

    def build_signatures(self) -> None:
        types = {"bytes-list": ["list", "UInt8"], "bytes-array": "ByteArray",
                 "text": ["list", "Char"], "utf16": ["list", "UInt16"], "nat": "Nat",
                 "int": "Int", "ordering": "Ordering", "version": "Version"}
        names = {key: "bytes" if key.startswith("bytes-") else key for key in types}
        launch = [(["arrow", types["bytes-list"], types["text"]], [["bytes"], ["plain", "text"]]),
                  (["arrow", types["text"], ["option", types["bytes-list"]]],
                   [["text"], ["option", "bytes"]]),
                  (["arrow", types["text"], ["option", "Version"]],
                   [["text"], ["option", "version"]]),
                  (["arrow", "Version", ["arrow", "Version", "Ordering"]],
                   [["version", "version"], ["plain", "ordering"]])]
        for i, (expr, want) in enumerate(launch + launch[:2]):
            self.exact(f"B.sig.launch.{i}", BSIG, ["sig", expr], want,
                       "six launch signature shapes (encode/decode repeated for URL)")
        for key, expr in types.items():
            for mode in ("plain", "option"):
                result = expr if mode == "plain" else ["option", expr]
                self.exact(f"B.sig.table.{key}.{mode}", BSIG,
                           ["sig", ["arrow", expr, result]], [[names[key]], [mode, names[key]]])
        mixed = ["arrow", "Nat", ["arrow", ["list", "Char"], ["arrow", "ByteArray", "Int"]]]
        self.exact("B.sig.multiple", BSIG, ["sig", mixed],
                   [["nat", "text", "bytes"], ["plain", "int"]])
        invalid = ["Nat", "Version", "String", "Prop", "Type", "dependent",
                   ["arrow", "String", "Nat"], ["arrow", "Nat", "String"],
                   ["arrow", "Bool", "Nat"], ["arrow", "Nat", "Bool"],
                   ["arrow", ["list", "Nat"], "Nat"],
                   ["arrow", "Nat", ["list", "Int"]],
                   ["arrow", ["option", "Nat"], "Nat"],
                   ["arrow", "Nat", ["option", ["option", "Nat"]]],
                   ["arrow", ["arrow", "Nat", "Nat"], "Nat"],
                   ["arrow", "Nat", ["option", ["list", "UInt16"]]],
                   ["arrow", "Unit", "Ordering"]]
        # Option (List UInt16) is encodable: keep it a positive, not a false refusal.
        valid_option = invalid.pop(-2)
        self.exact("B.sig.option-utf16", BSIG, ["sig", valid_option],
                   [["nat"], ["option", "utf16"]])
        # MAIN (reviewer-5 S7 regressions): metadata is transparent at every position sigOf reads.
        regression = "regression: metadata transparent (reviewer-5 S7)"
        self.exact("B.sig.mdata.codomain-arrow", BSIG,
                   ["sig", ["arrow", "Nat", ["mdata", ["arrow", "Nat", "Nat"]]]],
                   [["nat", "nat"], ["plain", "nat"]], regression)
        self.exact("B.sig.mdata.list-arg", BSIG,
                   ["sig", ["arrow", ["list", ["mdata", "UInt8"]], "Nat"]],
                   [["bytes"], ["plain", "nat"]], regression)
        for i, expr in enumerate(invalid):
            self.exact(f"B.sig.refuse.{i:02}", BSIG, ["sig", expr], None)

    def build_cli(self) -> None:
        valid = [
            ("base64.encode", "encode", ["00ff"], {"ok": ref.b64encode(b"\0\xff")}),
            ("base64.encode_url", "encodeUrl", ["fbff"], {"ok": ref.b64encode(b"\xfb\xff", True)}),
            ("base64.decode", "decode", ["AP8="], {"ok": "00ff"}),
            ("base64.decode_url", "decodeUrl", ["-_8="], {"ok": "fbff"}),
            ("semver.parse", "parse", ["1.2.3-alpha+001"],
             {"ok": ref.encode_value(["version", ref.parse("1.2.3-alpha+001")])}),
            ("semver.compare", "compare", [ref.version(pre=[{"num": 10}]),
                                           ref.version(pre=[{"alnum": ""}])], {"ok": "lt"}),
        ]
        for target, op, args, reply in valid:
            self.cli_exact(f"B.cli.target.{target}", target + "@1.0.0",
                           ref.request(op, args) + b"\n", ref.canonical(reply) + b"\n")
        target = "base64.decode@1.0.0"
        good = ref.request("decode", ["Zg=="])
        self.cli_exact("B.cli.empty-eof", target, b"", b"")
        self.cli_exact("B.cli.crlf", target, good + b"\r\n", b'{"ok":"66"}\n')
        self.cli_exact("B.cli.final-fragment", target, good, b'{"ok":"66"}\n')
        self.cli_exact("B.cli.final-lf", target, good + b"\n", b'{"ok":"66"}\n')
        self.cli_exact("B.cli.none-result", target, ref.request("decode", ["AB=="]) + b"\n",
                       b'{"err":"none"}\n')
        self.cli_exact("B.cli.empty-result", target, ref.request("decode", [""]) + b"\n",
                       b'{"ok":""}\n')
        data = b"\n" + good + b"\n{\n" + good + b"\r\n" + ref.request("oops", [""]) + b"\n" + good
        def recovery() -> None:
            proc = self.oracle_run(target, data)
            equal(proc.returncode, 0, "recovery exit")
            lines = proc.stdout.splitlines(keepends=True)
            equal(len(lines), 6, "one reply per input line incl. final fragment")
            for i in (0, 2, 4):
                decoded = json.loads(lines[i])
                equal(set(decoded), {"invalid"}, f"reply {i}")
                equal(isinstance(decoded["invalid"], str), True, f"reply {i} String")
                equal(lines[i], ref.canonical(decoded) + b"\n", "invalid canonical+LF")
            for i in (1, 3, 5):
                equal(lines[i], b'{"ok":"66"}\n', f"reply {i}")
        self.add("B.cli.recovery", BCLI, "six lines; empty/malformed/wrong-op interleaved with valid",
                 recovery)
        for i, args in enumerate(([], ["base64.encode@1.0.0", "extra"], ["--unknown"],
                                   ["base64.encode"], ["base64.encode@1"], ["@1.0.0"])):
            def usage(args: list[str] = args) -> None:
                proc = subprocess.run([self.oracle, "oracle", *args], input=b"", capture_output=True,
                                      timeout=10, check=False)
                equal(proc.returncode, 2, "usage exit")
                equal(proc.stdout, b"", "usage stdout")
                if not proc.stderr:
                    raise CheckFailure("usage/unknown target needs stderr diagnostic")
            self.add(f"B.cli.usage.{i}", BCLI, f"argv={args!r}; exit 2 + stderr", usage)
        def unread() -> None:
            read_fd, write_fd = os.pipe()
            marker = b"THIS INPUT MUST STAY UNREAD\n"
            os.write(write_fd, marker)
            os.close(write_fd)
            proc = subprocess.Popen([self.oracle, "oracle", "missing.operation@9.8.7"],
                                    stdin=read_fd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                stdout, stderr = proc.communicate(timeout=10)
                equal(proc.returncode, 2, "unknown target exit")
                equal(stdout, b"", "unknown target stdout")
                if b"missing.operation@9.8.7" not in stderr:
                    raise CheckFailure(f"diagnostic does not name target: {brief(stderr)}")
                os.set_blocking(read_fd, False)
                try:
                    left = os.read(read_fd, len(marker))
                except BlockingIOError:
                    left = b""
                equal(left, marker, "stdin bytes preserved")
            finally:
                if proc.poll() is None:
                    proc.kill()
                    proc.communicate()
                os.close(read_fd)
        self.add("B.cli.unknown-stdin-unread", BCLI,
                 "unknown target with finite pipe; exact marker remains unread", unread)
        expanded = "A" * 65536
        self.cli_exact("B.cli.maximal-expansion", target,
                       ref.request("decode", [expanded]) + b"\n",
                       ref.canonical({"ok": "00" * 49152}) + b"\n",
                       "65536-char request → 98304-char hex payload; full stdout compared")
        self.cli_exact("B.cli.maximal-expansion-url", "base64.decode_url@1.0.0",
                       ref.request("decodeUrl", [expanded]),
                       ref.canonical({"ok": "00" * 49152}) + b"\n",
                       "URL; final fragment; reply larger than request cap")

    def build(self) -> None:
        self.build_base64()
        self.build_semver()
        self.build_values()
        self.build_requests()
        self.build_reply_lines()
        self.build_signatures()
        self.build_cli()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--oracle", type=Path, required=True)
    parser.add_argument("--coverage", type=Path)
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    seed = int(os.environ.get("FVDEP_TEST_SEED", str(DEFAULT_SEED)), 0)
    suite = Suite(Driver(args.driver), args.oracle, seed)
    suite.build()
    names = [case.name for case in suite.cases]
    if len(names) != len(set(names)):
        raise RuntimeError("duplicate case ids")
    coverage = "case\tclause\tdomain\n" + "".join(
        f"{case.name}\t{case.clause}\t{case.domain.replace(chr(9), ' ')}\n" for case in suite.cases)
    if args.coverage:
        args.coverage.write_text(coverage)
    if args.list:
        print(coverage, end="")
        return 0
    only = os.environ.get("FVDEP_LIBRARY_CASE", "")
    cases = [case for case in suite.cases if only in case.name]
    if not cases:
        raise RuntimeError(f"no cases matching {only!r}")
    print(f"SEED {seed} (0x{seed:x}); cases={len(cases)}; scope={only or 'all'}", flush=True)
    results = []
    for case in cases:
        start = time.monotonic()
        try:
            case.check()
            verdict, detail = "PASS", ""
        except (CheckFailure, subprocess.TimeoutExpired, ValueError, KeyError, TypeError) as exc:
            verdict, detail = "FAIL", str(exc).replace("\n", " ").replace("\t", " ")
        seconds = time.monotonic() - start
        results.append((case.name, verdict, seconds, detail))
        print(f"{verdict} {case.name}\t{seconds:.6f}\t{detail}", flush=True)
    for name, verdict, seconds, _ in sorted(results, key=lambda row: row[2], reverse=True)[:10]:
        print(f"SLOW {name} {seconds:.6f}s {verdict}")
    failures = sum(verdict == "FAIL" for _, verdict, _, _ in results)
    print(f"TOTAL {len(results)} PASS {len(results) - failures} FAIL {failures}")
    return min(failures, 255)


if __name__ == "__main__":
    raise SystemExit(main())
