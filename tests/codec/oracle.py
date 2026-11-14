"""Independent J2–J4 + H2 reference; production modules remain unread."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

MAX_INT = (1 << 53) - 1
MAX_STRING = 65_536
MAX_DEPTH = 32


@dataclass(frozen=True)
class V:
    tag: str
    scalar: None | bool | int | str = None
    items: tuple[V, ...] = ()
    members: tuple[tuple[str, V], ...] = ()


def null() -> V:
    return V("null")


def boolean(b: bool) -> V:
    return V("bool", b)


def integer(n: int) -> V:
    return V("int", n)


def string(s: str) -> V:
    return V("str", s)


def array(xs: Iterable[V]) -> V:
    return V("arr", items=tuple(xs))


def obj(ms: Iterable[tuple[str, V]]) -> V:
    return V("obj", members=tuple(ms))


def as_string(v: V) -> str:
    assert v.tag == "str" and isinstance(v.scalar, str)
    return v.scalar


def as_int(v: V) -> int:
    assert v.tag == "int" and type(v.scalar) is int
    return v.scalar


def net(s: str) -> bytes:
    b = s.encode("utf-8")
    return str(len(b)).encode("ascii") + b":" + b


def wire(v: V) -> bytes:
    match v.tag:
        case "null":
            return b"n"
        case "bool":
            return b"t" if v.scalar else b"f"
        case "int":
            return b"i" + str(as_int(v)).encode("ascii") + b";"
        case "str":
            return b"s" + net(as_string(v))
        case "arr":
            return b"a" + str(len(v.items)).encode("ascii") + b":" + b"".join(map(wire, v.items))
        case "obj":
            return b"o" + str(len(v.members)).encode("ascii") + b":" + b"".join(
                net(k) + wire(x) for k, x in v.members
            )
    raise AssertionError(v.tag)


def value_out(v: V) -> str:
    return "ok:" + wire(v).hex()


def depth(v: V) -> int:
    if v.tag == "arr":
        return 1 + max((depth(x) for x in v.items), default=0)
    if v.tag == "obj":
        return 1 + max((depth(x) for _, x in v.members), default=0)
    return 0


def bounded_strings(v: V) -> bool:
    if v.tag == "str":
        return len(as_string(v).encode("utf-8")) <= MAX_STRING
    if v.tag == "arr":
        return all(map(bounded_strings, v.items))
    if v.tag == "obj":
        return all(len(k.encode("utf-8")) <= MAX_STRING and bounded_strings(x) for k, x in v.members)
    return True


def valid(v: V) -> bool:
    if depth(v) > MAX_DEPTH or not bounded_strings(v):
        return False
    match v.tag:
        case "int":
            return abs(as_int(v)) <= MAX_INT
        case "arr":
            return all(map(valid, v.items))
        case "obj":
            keys = [k.encode("utf-8") for k, _ in v.members]
            return all(a < b for a, b in zip(keys, keys[1:], strict=False)) and all(valid(x) for _, x in v.members)
    return True


def canonicalize(v: V) -> V:
    if v.tag == "arr":
        return array(map(canonicalize, v.items))
    if v.tag == "obj":
        return obj(sorted(((k, canonicalize(x)) for k, x in v.members), key=lambda p: p[0].encode()))
    return v


def quote(s: str) -> bytes:
    short = {'"': '\\"', "\\": "\\\\", "\b": "\\b", "\f": "\\f", "\n": "\\n", "\r": "\\r", "\t": "\\t"}
    out = bytearray(b'"')
    for c in s:
        if c in short:
            out.extend(short[c].encode("ascii"))
        elif ord(c) < 32 or ord(c) == 127:
            out.extend(f"\\u{ord(c):04x}".encode("ascii"))
        else:
            out.extend(c.encode("utf-8"))
    out.append(34)
    return bytes(out)


def canonical(v: V) -> bytes:
    match v.tag:
        case "null":
            return b"null"
        case "bool":
            return b"true" if v.scalar else b"false"
        case "int":
            return str(as_int(v)).encode("ascii")
        case "str":
            return quote(as_string(v))
        case "arr":
            return b"[" + b",".join(map(canonical, v.items)) + b"]"
        case "obj":
            return b"{" + b",".join(quote(k) + b":" + canonical(x) for k, x in v.members) + b"}"
    raise AssertionError(v.tag)


def excessive_lexical_depth(b: bytes) -> bool:
    """Byte scanner: quotes/escapes alone delimit strings; grammar is a later stage."""
    level = 0
    in_string = False
    escaped = False
    for c in b:
        if in_string:
            if escaped:
                escaped = False
            elif c == 92:
                escaped = True
            elif c == 34:
                in_string = False
        elif c == 34:
            in_string = True
        elif c in (91, 123):
            level += 1
            if level > MAX_DEPTH:
                return True
        elif c in (93, 125):
            level = max(0, level - 1)
    return False


class Malformed(ValueError):
    pass


class Parser:
    def __init__(self, b: bytes) -> None:
        self.b = b
        self.i = 0

    def peek(self) -> int:
        return self.b[self.i] if self.i < len(self.b) else -1

    def ws(self) -> None:
        while self.peek() in (32, 9, 10, 13):
            self.i += 1

    def take(self, c: int) -> None:
        if self.peek() != c:
            raise Malformed
        self.i += 1

    def hex4(self) -> int:
        raw = self.b[self.i : self.i + 4]
        if len(raw) != 4 or any(c not in b"0123456789abcdefABCDEF" for c in raw):
            raise Malformed
        self.i += 4
        return int(raw, 16)

    def text(self) -> str:
        self.take(34)
        out: list[str] = []
        short = {34: '"', 92: "\\", 47: "/", 98: "\b", 102: "\f", 110: "\n", 114: "\r", 116: "\t"}
        while True:
            c = self.peek()
            if c == 34:
                self.i += 1
                return "".join(out)
            if c < 32:
                raise Malformed
            if c == 92:
                self.i += 1
                esc = self.peek()
                self.i += 1
                if esc in short:
                    out.append(short[esc])
                elif esc == 117:
                    cp = self.hex4()
                    if 0xD800 <= cp <= 0xDBFF:
                        if self.b[self.i : self.i + 2] != b"\\u":
                            raise Malformed
                        self.i += 2
                        low = self.hex4()
                        if not 0xDC00 <= low <= 0xDFFF:
                            raise Malformed
                        cp = 0x10000 + ((cp - 0xD800) << 10) + low - 0xDC00
                    elif 0xDC00 <= cp <= 0xDFFF:
                        raise Malformed
                    out.append(chr(cp))
                else:
                    raise Malformed
            elif c < 128:
                self.i += 1
                out.append(chr(c))
            else:
                if 0xC2 <= c <= 0xDF:
                    n = 2
                elif 0xE0 <= c <= 0xEF:
                    n = 3
                elif 0xF0 <= c <= 0xF4:
                    n = 4
                else:
                    raise Malformed
                raw = self.b[self.i : self.i + n]
                try:
                    char = raw.decode("utf-8", "strict")
                except UnicodeDecodeError as e:
                    raise Malformed from e
                if len(char) != 1:
                    raise Malformed
                self.i += n
                out.append(char)

    def number(self) -> V:
        negative = self.peek() == 45
        if negative:
            self.i += 1
        if self.peek() == 48:
            if negative:
                raise Malformed
            self.i += 1
            return integer(0)
        if not 49 <= self.peek() <= 57:
            raise Malformed
        n = 0
        while 48 <= self.peek() <= 57:
            n = n * 10 + self.peek() - 48
            self.i += 1
            if n > MAX_INT:
                raise Malformed
        return integer(-n if negative else n)

    def value(self) -> V:
        self.ws()
        c = self.peek()
        if c == 34:
            return string(self.text())
        for spelling, value in ((b"null", null()), (b"false", boolean(False)), (b"true", boolean(True))):
            if self.b[self.i : self.i + len(spelling)] == spelling:
                self.i += len(spelling)
                return value
        if c == 45 or 48 <= c <= 57:
            return self.number()
        if c == 91:
            self.i += 1
            self.ws()
            xs: list[V] = []
            if self.peek() == 93:
                self.i += 1
                return array(xs)
            while True:
                xs.append(self.value())
                self.ws()
                if self.peek() == 93:
                    self.i += 1
                    return array(xs)
                self.take(44)
        if c == 123:
            self.i += 1
            self.ws()
            ms: list[tuple[str, V]] = []
            if self.peek() == 125:
                self.i += 1
                return obj(ms)
            while True:
                self.ws()
                key = self.text()
                self.ws()
                self.take(58)
                ms.append((key, self.value()))
                self.ws()
                if self.peek() == 125:
                    self.i += 1
                    return obj(ms)
                self.take(44)
        raise Malformed


type Segment = str | int
type Site = tuple[tuple[Segment, ...], str]


def duplicate_site(v: V, path: tuple[Segment, ...] = ()) -> Site | None:
    if v.tag == "obj":
        keys = [k for k, _ in v.members]
        repeated = {k for k in keys if keys.count(k) > 1}
        if repeated:
            return path, min(repeated, key=lambda k: k.encode("utf-8"))
        for k, x in v.members:
            site = duplicate_site(x, (*path, k))
            if site is not None:
                return site
    if v.tag == "arr":
        for i, x in enumerate(v.items):
            site = duplicate_site(x, (*path, i))
            if site is not None:
                return site
    return None


def site_out(site: Site) -> str:
    path, key = site
    segments = array(
        array([string("index"), integer(p)]) if isinstance(p, int)
        else array([string("key"), string(p)]) for p in path
    )
    return "error:duplicate:" + wire(array([segments, string(key)])).hex()


@dataclass(frozen=True)
class Outcome:
    kind: str
    value: V | None = None
    site: Site | None = None

    def output(self) -> str:
        if self.kind == "ok":
            assert self.value is not None
            return value_out(self.value)
        if self.kind == "duplicate":
            assert self.site is not None
            return site_out(self.site)
        return "error:" + self.kind


def decode(b: bytes) -> Outcome:
    if excessive_lexical_depth(b):
        return Outcome("tooLarge")
    parser = Parser(b)
    try:
        value = parser.value()
        parser.ws()
        if parser.i != len(b):
            raise Malformed
    except Malformed:
        return Outcome("malformed")
    if not bounded_strings(value):
        return Outcome("tooLarge")
    site = duplicate_site(value)
    if site is not None:
        return Outcome("duplicate", site=site)
    value = canonicalize(value)
    assert valid(value), "reference outcome must satisfy J1"
    return Outcome("ok", value=value)


def u64(n: int) -> bytes:
    return n.to_bytes(8, "big")


def frame(tag: str, files: list[tuple[str, bytes]]) -> bytes:
    tag_bytes = tag.encode("utf-8")
    out = bytearray(u64(len(tag_bytes)) + tag_bytes + u64(len(files)))
    for path, content in sorted(files, key=lambda p: p[0].encode("utf-8")):
        path_bytes = path.encode("utf-8")
        out.extend(u64(len(path_bytes)) + path_bytes + u64(len(content)) + content)
    return bytes(out)


def unframe(b: bytes) -> tuple[str, list[tuple[str, bytes]]] | None:
    cursor = 0

    def count() -> int:
        nonlocal cursor
        if len(b) - cursor < 8:
            raise Malformed
        n = int.from_bytes(b[cursor : cursor + 8], "big")
        cursor += 8
        return n

    def blob() -> bytes:
        nonlocal cursor
        n = count()
        if n > len(b) - cursor:
            raise Malformed
        value = b[cursor : cursor + n]
        cursor += n
        return value

    try:
        tag = blob().decode("utf-8", "strict")
        size = count()
        if size > (len(b) - cursor) // 16:
            return None
        files: list[tuple[str, bytes]] = []
        previous: bytes | None = None
        for _ in range(size):
            path_bytes = blob()
            path = path_bytes.decode("utf-8", "strict")
            content = blob()
            if previous is not None and path_bytes <= previous:
                return None
            previous = path_bytes
            files.append((path, content))
        return (tag, files) if cursor == len(b) else None
    except (Malformed, UnicodeDecodeError):
        return None


def argv_bytes(argv: list[str]) -> bytes:
    return u64(len(argv)) + b"".join(u64(len(s.encode("utf-8"))) + s.encode("utf-8") for s in argv)


def adapter_entries(argv: list[str], named: list[tuple[str, bytes]]) -> list[tuple[str, bytes]]:
    seen = {""}
    out = [("", argv_bytes(argv))]
    for path, content in named:
        if path not in seen:
            seen.add(path)
            out.append((path, content))
    return out


def files_value(files: list[tuple[str, bytes]]) -> V:
    return array(array([string(p), string(b.hex())]) for p, b in files)


def frame_args(tag: str, files: list[tuple[str, bytes]]) -> bytes:
    return wire(array([string(tag), files_value(files)]))


def unframe_out(value: tuple[str, list[tuple[str, bytes]]] | None) -> str:
    if value is None:
        return "none"
    tag, files = value
    return value_out(array([string(tag), files_value(files)]))
