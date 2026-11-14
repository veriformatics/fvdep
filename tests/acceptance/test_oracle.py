"""Oracle differential properties; finite seeded samples, not a proof claim."""
import copy
import itertools
import json
import random

from harness import SEED, case
from reference import SAFE_INTEGER, bytes_domain, compare, decode, encode, parse, self_check, shrink_bytes, shrink_pair, shrink_text, version_domain


def reference_property(ctx, target, op, values, args, expected, shrinks):
    def request(value):
        return {"op": op, "args": args(value)}

    def matches(value, reply):
        want = expected(value)
        return set(reply) == {"err"} if want is None else reply == {"ok": want}

    replies = ctx.oracle(target, [request(value) for value in values])
    for value, reply in zip(values, replies, strict=True):
        if matches(value, reply):
            continue
        current, current_reply = value, reply
        seen = {json.dumps(request(current), sort_keys=True)}
        rounds = 0
        for _ in range(64):
            candidates = []
            for candidate in itertools.islice(shrinks(current), 128):
                key = json.dumps(request(candidate), sort_keys=True)
                if key not in seen:
                    seen.add(key)
                    candidates.append(candidate)
            if not candidates:
                break
            results = ctx.oracle(target, [request(candidate) for candidate in candidates])
            failing = [(candidate, result) for candidate, result in zip(candidates, results, strict=True)
                       if not matches(candidate, result)]
            if not failing:
                break
            current, current_reply = failing[0]
            rounds += 1
        raise AssertionError(f"{target}: shrunk input {request(current)!r}; reply={current_reply!r}; "
                             f"expected={expected(current)!r}; seed={SEED}; shrink_rounds={rounds} "
                             "(limit 64 rounds, 128 candidates/round)")


for id, op, url in [("base64.encode", "encode", False), ("base64.encode_url", "encodeUrl", True)]:
    @case(f"oracle.{id}.reference", "U4", "library Operations; RFC 4648 §§4–5", f"{id} agrees with an independent bit-level encoder over seeded byte strings", "property")
    def encoder(ctx, id=id, op=op, url=url):
        self_check()
        values = bytes_domain(random.Random(SEED))
        reference_property(ctx, f"{id}@1.0.0", op, values, lambda raw: [raw.hex()],
                           lambda raw: encode(raw, url=url), shrink_bytes)


for id, op, url in [("base64.decode", "decode", False), ("base64.decode_url", "decodeUrl", True)]:
    @case(f"oracle.{id}.reference", "U4", "library Operations; RFC 4648 §§3.2–3.5/4/5", f"{id} accepts exactly strict canonical encodings over seeded valid and malformed strings", "property")
    def decoder(ctx, id=id, op=op, url=url):
        rng = random.Random(SEED)
        valid = [encode(raw, url=url) for raw in bytes_domain(rng)]
        invalid = ["A", "AA", "AAA", "A===", "====", "=AAA", "AA=A", "AA==AAAA", "AAAA=",
                   "Zh==", "Zm9=", "Zg==\n", " Zg==", "Zg==\r\n", "Zg== ", "Zg==\0", "éAAA", "💡AAA"]
        invalid.extend(["-w==", "_w=="] if not url else ["+w==", "/w=="])
        alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=_- \n\0é"
        invalid.extend("".join(rng.choice(alphabet) for _ in range(rng.randrange(25))) for _ in range(144))
        values = valid + invalid
        def expected(text):
            raw = decode(text, url=url)
            return None if raw is None else raw.hex()
        reference_property(ctx, f"{id}@1.0.0", op, values, lambda text: [text], expected, shrink_text)


@case("oracle.base64.round-trip", "U4", "library Operations; RFC 4648 §3.5", "Decode after encode returns every sampled input for both alphabets", "property")
def base64_round_trip(ctx):
    values = bytes_domain(random.Random(SEED ^ 1), count=64)
    for encode_id, encode_op, decode_id, decode_op in [
        ("base64.encode", "encode", "base64.decode", "decode"),
        ("base64.encode_url", "encodeUrl", "base64.decode_url", "decodeUrl"),
    ]:
        encoded = ctx.oracle(f"{encode_id}@1.0.0", [{"op": encode_op, "args": [raw.hex()]} for raw in values])
        decoded = ctx.oracle(f"{decode_id}@1.0.0", [{"op": decode_op, "args": [reply["ok"]]} for reply in encoded])
        assert decoded == [{"ok": raw.hex()} for raw in values]


@case("oracle.semver.parse.reference", "U4", "library Shared type; SemVer 2.0.0 §§2/9/10", "SemVer parse matches the independent grammar including large numeric components", "property")
def semver_parse(ctx):
    rng = random.Random(SEED ^ 2)
    values = ["0.0.0", "1.2.3", "1.0.0-0", "1.0.0-00a", "1.0.0--", "1.0.0+001.00",
              "9007199254740992.99999999999999999999999999999.0-9007199254740992",
              "", "1", "1.0", "1.0.0.0", "v1.0.0", " 1.0.0", "1.0.0\n", "01.0.0", "1.01.0",
              "1.0.01", "1.0.0-01", "1.0.0-", "1.0.0+", "1.0.0-a..b", "1.0.0+a..b", "1.0.0-α", "1.0.0+é"]
    for _ in range(100):
        nums = [rng.choice([0, 1, SAFE_INTEGER, SAFE_INTEGER + 1, rng.randrange(10**25)]) for _ in range(3)]
        text = ".".join(str(x) for x in nums)
        if rng.randrange(2):
            text += "-" + ".".join(rng.choice(["0", "00", "alpha", "a-1", "-", "001a", "9"]) for _ in range(rng.randrange(1, 4)))
        if rng.randrange(2):
            text += "+" + rng.choice(["build", "001", "a.b", "-"])
        values.append(text)
        values.append(text + rng.choice([" ", "\n", "_", "/", "💡"]))
    reference_property(ctx, "semver.parse@1.0.0", "parse", values, lambda text: [text], parse, shrink_text)


@case("oracle.semver.compare.reference", "U4", "library Shared type; SemVer 2.0.0 §11", "Compare follows the whole-type reference including arbitrary tagged identifiers", "property")
def semver_compare(ctx):
    rng = random.Random(SEED ^ 3)
    values = version_domain(rng)
    pairs = list(zip(values, values[1:], strict=False)) + [(rng.choice(values), rng.choice(values)) for _ in range(100)]
    # Keep numeric cores equal so prerelease rules cannot hide behind core ordering.
    for _ in range(60):
        a, b = copy.deepcopy(rng.choice(values)), copy.deepcopy(rng.choice(values))
        for field in ("major", "minor", "patch"):
            b[field] = a[field]
        pairs.append((a, b))
    reference_property(ctx, "semver.compare@1.0.0", "compare", pairs, list,
                       lambda pair: compare(*pair), shrink_pair)


@case("oracle.semver.compare.preorder", "U4", "library Shared type obligations", "Compare is antisymmetric in ordering, transitive, and ignores build metadata", "property")
def semver_preorder(ctx):
    rng = random.Random(SEED ^ 4)
    values = version_domain(rng, count=30)
    pairs = []
    triples = []
    for _ in range(50):
        a, b, c = (copy.deepcopy(rng.choice(values)) for _ in range(3))
        if rng.randrange(2):
            for field in ("major", "minor", "patch"):
                b[field] = c[field] = a[field]
        triples.append((a, b, c))
        build_changed = a | {"build": ["", "arbitrary", "💡"]}
        pairs.extend([(a, b), (b, a), (b, c), (a, c), (a, build_changed)])
    replies = ctx.oracle("semver.compare@1.0.0", [{"op": "compare", "args": list(pair)} for pair in pairs])
    for i, (a, b, _) in enumerate(triples):
        ab, ba, bc, ac, build = (reply.get("ok") for reply in replies[5 * i:5 * i + 5])
        assert ab in {"lt", "eq", "gt"} and bc in {"lt", "eq", "gt"} and ac in {"lt", "eq", "gt"}
        assert ba == {"lt": "gt", "eq": "eq", "gt": "lt"}[ab]
        if ab in {"lt", "eq"} and bc in {"lt", "eq"}:
            assert ac in {"lt", "eq"}
        assert (ab == "eq") == ((a | {"build": []}) == (b | {"build": []}))
        assert build == "eq"


@case("oracle.protocol.recovery", "U4", "interface §8", "Malformed requests produce invalid and the oracle continues to a valid request")
def protocol_recovery(ctx):
    bad = ["not-json", "{", "null", "[]", "{}", '{"op":"encode","op":"encode","args":[""]}',
           {"op": "unknown", "args": [""]}, {"op": "encode", "args": []},
           {"op": "encode", "args": ["", ""]}, {"op": "encode", "args": [0]},
           {"op": "encode", "args": ["0"]}, {"op": "encode", "args": ["FF"]},
           {"op": "encode", "args": ["xz"]}]
    requests = []
    for value in bad:
        requests.extend([value, {"op": "encode", "args": [""]}])
    replies = ctx.oracle("base64.encode@1.0.0", requests)
    for index in range(0, len(replies), 2):
        assert set(replies[index]) == {"invalid"}, (bad[index // 2], replies[index])
        assert replies[index + 1] == {"ok": ""}


@case("oracle.protocol.scalar-values", "U4", "interface §8; Decisions Data formats", "An escaped lone surrogate is invalid; a nonalphabet Unicode scalar is a decode rejection")
def scalar_values(ctx):
    requests = ['{"op":"decode","args":["\\ud800"]}', '{"op":"decode","args":["\\udfff"]}',
                {"op": "decode", "args": ["💡AAA"]}, {"op": "decode", "args": [""]}]
    replies = ctx.oracle("base64.decode@1.0.0", requests)
    assert [set(reply) for reply in replies] == [{"invalid"}, {"invalid"}, {"err"}, {"ok"}]
    assert replies[-1] == {"ok": ""}


@case("oracle.protocol.integer-boundaries", "U4", "interface §8", "Large Nat uses a canonical decimal string; in-range strings and noncanonical values are invalid")
def integer_boundaries(ctx):
    zero = {"major": 0, "minor": 0, "patch": 0, "pre": [], "build": []}
    cases = [(SAFE_INTEGER, True), (str(SAFE_INTEGER + 1), True), (str(10**80), True),
             (str(SAFE_INTEGER), False), ("0", False), ("00", False), ("+9007199254740992", False),
             ("09007199254740992", False), (-1, False), (1.5, False), (True, False),
             (SAFE_INTEGER + 1, False), ("-9007199254740992", False)]
    replies = ctx.oracle("semver.compare@1.0.0", [{"op": "compare", "args": [zero | {"major": value}, zero]} for value, _ in cases])
    for (value, valid), reply in zip(cases, replies, strict=True):
        assert reply == {"ok": "gt"} if valid else set(reply) == {"invalid"}, (value, reply)


@case("oracle.protocol.ident-tags", "U4", "interface §8; library Shared type", "num and alnum identifiers never share an encoding")
def ident_tags(ctx):
    core = {"major": 0, "minor": 0, "patch": 0, "pre": [], "build": []}
    a, b = core | {"pre": [{"num": 0}]}, core | {"pre": [{"alnum": "0"}]}
    requests = [{"op": "compare", "args": [a, b]}, {"op": "compare", "args": [b, a]},
                {"op": "compare", "args": [core | {"pre": [{"num": 0, "alnum": "0"}]}, a]}]
    replies = ctx.oracle("semver.compare@1.0.0", requests)
    assert replies[:2] == [{"ok": "lt"}, {"ok": "gt"}]
    assert set(replies[2]) == {"invalid"}


@case("oracle.protocol.string-limit", "U4", "interface §8; Decisions Data formats", "The differential codec accepts the 64-KiB string boundary and refuses the next byte")
def string_limit(ctx):
    # Empty parse results keep replies small; the bound concerns UTF-8 bytes.
    replies = ctx.oracle("semver.parse@1.0.0", [{"op": "parse", "args": ["a" * (64 * 1024)]},
                                               {"op": "parse", "args": ["a" * (64 * 1024 + 1)]},
                                               {"op": "parse", "args": ["é" * (32 * 1024 + 1)]},
                                               {"op": "parse", "args": ["0.0.0"]}])
    assert [set(reply) for reply in replies] == [{"err"}, {"invalid"}, {"invalid"}, {"ok"}]


@case("oracle.unknown-target", "U4", "interface §§2–3", "An absent oracle target exits 2 rather than serving another operation")
def unknown_target(ctx):
    ctx.library()
    ctx.call("oracle", "missing.operation@1.0.0", data='{"op":"encode","args":[""]}\n').code(2).contains("missing.operation")
