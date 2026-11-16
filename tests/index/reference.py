"""Independent C6 + D5 document walk; only contract-owned schema predicates."""
from __future__ import annotations

from dataclasses import dataclass, field
import json
import re
from typing import Any, Callable


def canonical(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).replace(
        "\x7f", "\\u007f").encode()


def display(value: str) -> str:
    out = []
    for char in value:
        n = ord(char)
        if n in (9, 10, 13):
            out.append({9: "\\t", 10: "\\n", 13: "\\r"}[n])
        elif n < 32 or 127 <= n <= 159:
            out.append("\\u00" + format(n, "02X"))
        else:
            out.append(char)
    return "".join(out)


def line(value: str) -> bytes:
    return (display(value) + "\n").encode()


def pointer(path: list[str | int]) -> str:
    return "".join("/" + str(item).replace("~", "~0").replace("/", "~1") for item in path)


def kind(value: Any) -> str:
    if value is None:
        return "null"
    if type(value) is bool:
        return "bool"
    if type(value) is int:
        return "int"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "array"
    if isinstance(value, dict):
        return "object"
    raise TypeError(type(value))


def error(path: list[str | int], code: str, value: Any = None) -> str:
    prefix = pointer(path)
    text = (prefix + " " if prefix else "") + code
    if code != "missing_field":
        rendered = canonical(value)
        text += " " + (rendered.decode() if len(rendered) <= 64 else kind(value))
    return text


def text(value: str, cap: int = 1024) -> bool:
    return 1 <= len(value.encode()) <= cap and all(ord(c) >= 32 and not 127 <= ord(c) <= 159 for c in value)


def module_id(value: str) -> bool:
    return re.fullmatch(r"[a-z][a-z0-9]*\.[a-z][a-z0-9]*(?:_[a-z][a-z0-9]*)*", value) is not None


def version(value: str) -> bool:
    return re.fullmatch(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", value) is not None


def version_key(value: str) -> tuple[tuple[int, str], ...]:
    return tuple((len(part), part) for part in value.split("."))


@dataclass
class Node:
    type: str
    fields: dict[str, Node] = field(default_factory=dict)
    child: Node | None = None
    predicate: Callable[[Any], bool] = lambda _: True
    nullable: bool = False
    discriminator: str | None = None
    special: str = ""


def walk(node: Node, value: Any, path: list[str | int]) -> str | None:
    if node.nullable and value is None:
        return None
    if kind(value) != node.type:
        return error(path, "wrong_type", value)
    if node.special == "compat":
        assert node.child is not None
        return error(path, "bad_value", value) if walk(node.child, value, path) else None
    if node.type == "object":
        disc = node.discriminator
        if disc is not None:
            if disc not in value:
                return error([*path, disc], "missing_field")
            issue = walk(node.fields[disc], value[disc], [*path, disc])
            if issue:
                return issue
        keys = sorted(value, key=lambda key: key.encode())
        for key in keys:
            if key not in node.fields:
                return error([*path, key], "unknown_field", value[key])
        for key in sorted(node.fields, key=lambda key: key.encode()):
            if key not in value:
                return error([*path, key], "missing_field")
        for key in keys:
            issue = walk(node.fields[key], value[key], [*path, key])
            if issue:
                return issue
    if node.type == "array":
        assert node.child is not None
        for i, item in enumerate(value):
            issue = walk(node.child, item, [*path, i])
            if issue:
                return issue
    if node.special in ("axioms", "operations"):
        keys = ([item.encode() for item in value] if node.special == "axioms" else
                [(item["id"].encode(), version_key(item["version"])) for item in value])
        for i in range(1, len(keys)):
            if keys[i] <= keys[i - 1]:
                return error([*path, i], "bad_value", value[i])
    if node.special == "obligations":
        seen = set()
        for i, item in enumerate(value):
            if item["name"] in seen:
                return error([*path, i, "name"], "bad_value", item["name"])
            seen.add(item["name"])
    if not node.predicate(value):
        if node.special == "status":
            return error([*path, "axioms"], "bad_value", value["axioms"])
        return error(path, "bad_value", value)
    return None


NAME = Node("string", predicate=text)
ID = Node("string", predicate=module_id)
VERSION = Node("string", predicate=version)
DIGEST = Node("string", predicate=lambda x: re.fullmatch(r"[0-9a-f]{64}", x) is not None)
COMMIT = Node("string", predicate=lambda x: re.fullmatch(r"[0-9a-f]{40}", x) is not None)
AXIOMS = Node("array", child=NAME, special="axioms")
STATUS = Node("string", predicate=lambda s: s in {"proven", "open", "trusts"})


def consistent(value: dict[str, Any]) -> bool:
    status, axioms = value["status"], value["axioms"]
    return ((status == "proven" and not axioms) or
            (status == "open" and (not axioms or "sorryAx" in axioms)) or
            (status == "trusts" and bool(axioms) and "sorryAx" not in axioms))


OBLIGATION = Node("object", fields={"axioms": AXIOMS, "name": NAME, "status": STATUS},
                  predicate=consistent, discriminator="status", special="status")
COMPAT_INNER = Node("object", fields={"axioms": AXIOMS, "status": STATUS, "version": VERSION},
                    predicate=consistent, discriminator="status", special="status")
COMPAT = Node("object", child=COMPAT_INNER, nullable=True, special="compat")
OPERATION = Node("object", fields={
    "compat": COMPAT, "digest": DIGEST, "id": ID,
    "obligations": Node("array", child=OBLIGATION, special="obligations"),
    "version": VERSION})
NOTICE = Node("object", fields={
    "id": ID, "version": VERSION, "reason": Node("string", predicate=lambda s: text(s, 65536)),
    "replacement": Node("string", predicate=version, nullable=True)})
REMOVED = Node("object", fields={
    "digest": DIGEST, "id": ID, "kind": Node("string", predicate=lambda x: x == "operation"),
    "last_commit": COMMIT, "toolchain": NAME, "version": VERSION})
INDEX = Node("object", discriminator="schema", fields={
    "schema": Node("int", predicate=lambda x: x == 1), "toolchain": NAME,
    "notices": Node("array", child=NOTICE), "removed": Node("array", child=REMOVED),
    "operations": Node("array", child=OPERATION, special="operations")})


def index_error(value: Any) -> str | None:
    issue = walk(INDEX, value, [])
    if issue:
        return issue
    listed = {(x["id"], x["version"]) for x in value["operations"]}
    removed = {(x["id"], x["version"]) for x in value["removed"]}
    known = listed | removed
    notices = value["notices"]
    for i, item in enumerate(notices):
        key = (item["id"], item["version"])
        replacement = item["replacement"]
        if key not in known or (replacement is not None and (item["id"], replacement) not in known):
            return error(["notices", i], "bad_value", item)
    seen = set()
    for i, item in enumerate(value["removed"]):
        key = (item["id"], item["version"])
        if key in listed or key in seen or not any((n["id"], n["version"]) == key for n in notices):
            return error(["removed", i], "bad_value", item)
        seen.add(key)
    return None
