"""C6/C7/C9 decoder + history cases; expected layouts/relations independent of the tool."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import random
from typing import Any, Callable


def register(ctx: Any) -> None:
    register_decode(ctx)
    register_history(ctx)


def register_decode(ctx: Any) -> None:
    fx, ref = ctx.fx, ctx.ref
    old = fx.operation()
    newer = fx.operation(version="1.1.0", compat={"axioms": [], "status": "proven", "version": "1.0.0"})
    gone = fx.removed_record(id="other.encode")
    base = fx.index(operations=[old, newer], removed=[gone],
                    notices=[fx.notice(replacement="1.1.0"), fx.notice(id="other.encode")])
    assert ref.index_error(base) is None
    def case(label: str, value: Any, expected: str | None = None) -> None:
        issue = ref.index_error(value) if expected is None else expected
        if issue is None:
            want, code = fx.canonical(value) + b"\n", 0
        else:
            want, code = ref.line("refused: " + issue), 1
        clause = "C6/C9 decode; U3 D5; D1/D2"
        if label.startswith(("presentation.", "c1-control.")):
            clause += "; D3 Cc + last-stage escaping"
        ctx.decode_case("C11." + label, fx.canonical(value), want, code, clause)
    case("roundtrip.full", base)
    case("roundtrip.empty", fx.index())
    ctx.decode_case("C11.roundtrip.noncanonical", json.dumps(base, indent=2, ensure_ascii=True).encode(),
                    fx.canonical(base) + b"\n", 0)
    for i, value in enumerate((None, True, 0, "", [])):
        case(f"root-kind.{i}", value)
    for label, value in (("missing", {k: v for k, v in base.items() if k != "schema"}),
                          ("zero", {**base, "schema": 0}), ("two", {**base, "schema": 2}),
                          ("string", {**base, "schema": "1"}), ("bool", {**base, "schema": True}),
                          ("null", {**base, "schema": None})):
        case("schema." + label, value)
    paths: list[tuple[list[str | int], dict[str, Any]]] = [([], base),
        (["operations", 0], old), (["operations", 0, "obligations", 0], old["obligations"][0]),
        (["operations", 1, "compat"], newer["compat"]), (["notices", 0], base["notices"][0]),
        (["removed", 0], gone)]
    def changed(path: list[str | int], transform: Callable[[Any], None]) -> Any:
        value = copy.deepcopy(base)
        node = value
        for segment in path:
            node = node[segment]
        transform(node)
        return value
    for path, node in paths:
        prefix = "root" if not path else "-".join(str(x) for x in path)
        for field in node:
            case(f"missing.{prefix}.{field}", changed(path, lambda obj, field=field: obj.pop(field)))
        case("unknown." + prefix, changed(path, lambda obj: obj.update({"a~/b": 0})))
        for field, good in node.items():
            bad_values: list[Any]
            if isinstance(good, str):
                bad_values = [None, False, 0, [], {}]
            elif isinstance(good, list):
                bad_values = [None, False, 0, "", {}]
            elif isinstance(good, dict):
                bad_values = [False, 0, "", []]  # compat is nullable
            elif type(good) is int:
                bad_values = [None, True, "1", [], {}]
            else:
                bad_values = [False, 0, [], {}]  # nullable replacement
            for i, bad in enumerate(bad_values):
                case(f"kind.{prefix}.{field}.{i}", changed(path,
                     lambda obj, field=field, bad=bad: obj.update({field: bad})))
    invalid_texts = {
        "id": ["", "Base64.encode", "base64._encode", "base64.encode_1", "base64..encode", "base64.encode-foo"],
        "version": ["", "1", "1.0", "01.0.0", "1.0.0-alpha", "v1.0.0", "1.0.0 "],
        "digest": ["", "0" * 63, "0" * 65, "A" * 64, "g" * 64],
    }
    for field, values in invalid_texts.items():
        for i, value in enumerate(values):
            case(f"bad.{field}.{i}", changed(["operations", 0],
                 lambda node, field=field, value=value: node.update({field: value})))
    # One operation keeps membership/order independent of the long canonical field.
    capped_version = fx.index(operations=[fx.operation(version="9" * 65532 + ".0.0")])
    case("version.cap", capped_version)
    capped_id = fx.index(operations=[fx.operation(id="a" * 65533 + ".op")])
    case("id.cap-valid", capped_id)
    for label, value in (("id", fx.index(operations=[fx.operation(id="a" * 65534 + ".op")])),
                          ("version", fx.index(operations=[fx.operation(version="9" * 65533 + ".0.0")]))):
        ctx.decode_case("C11.text." + label + "-over-cap", fx.canonical(value),
                        b"refused: too_large\n", 1, "C6/J1 65536-byte string boundary")
    large_key = "x" * 65536
    case("key.cap", {"schema": 1, large_key: 0})
    ctx.decode_case("C11.text.key-over-cap", fx.canonical({"schema": 1, large_key + "x": 0}),
                    b"refused: too_large\n", 1, "C9/J1 key byte cap before schema")
    for field in ("name",):
        for label, value in (("empty", ""), ("nul", "x\0y"), ("del", "x\x7f"),
                              ("over", "x" * 1025), ("utf8-over", "é" * 513)):
            case(f"bad.obligation.{field}.{label}", changed(["operations", 0, "obligations", 0],
                 lambda node, value=value: node.update({"name": value})))
        for label, value in (("cap", "x" * 1024), ("utf8-cap", "é" * 512)):
            case(f"accept.obligation.{field}.{label}", changed(["operations", 0, "obligations", 0],
                 lambda node, value=value: node.update({"name": value})))
    for label, value in (("empty", ""), ("control", "x\n"), ("over", "x" * 1025)):
        case("toolchain." + label, {**base, "toolchain": value})
    case("toolchain.cap", {**base, "toolchain": "x" * 1024})
    for label, value in (("empty", ""), ("control", "bad\ttext"), ("del", "bad\x7f")):
        case("reason." + label, changed(["notices", 0], lambda node, value=value: node.update({"reason": value})))
    case("reason.cap", changed(["notices", 0], lambda node: node.update({"reason": "é" * 32768})))
    for label, value in (("upper", "A" * 40), ("short", "0" * 39), ("long", "0" * 41)):
        case("removed.commit." + label, changed(["removed", 0],
             lambda node, value=value: node.update({"last_commit": value})))
    case("removed.kind", changed(["removed", 0], lambda node: node.update({"kind": "profile"})))
    for path, _ in ((["operations", 0, "obligations", 0], None), (["operations", 1, "compat"], None)):
        label = "obligation" if "obligations" in path else "compat"
        for status in ("proven", "open", "trusts", "unknown"):
            for i, axioms in enumerate(([], ["sorryAx"], ["Custom.a"], ["Custom.a", "sorryAx"],
                                       ["z", "a"], ["a", "a"], [""], [None], ["x\0"])):
                case(f"status.{label}.{status}.{i}", changed(path,
                     lambda node, status=status, axioms=axioms: node.update({"status": status, "axioms": axioms})))
    case("operations.reversed", {**base, "operations": list(reversed(base["operations"]))})
    case("operations.duplicate", {**base, "operations": [old, old]})
    case("obligations.duplicate", changed(["operations", 0], lambda node: node.update({
        "obligations": [node["obligations"][0], node["obligations"][0]]})))
    for label, value in (
        ("notice-membership", {**base, "notices": [fx.notice(id="missing.encode")]}),
        ("replacement", {**base, "notices": [fx.notice(replacement="9.0.0")]}),
        ("removed-listed", {**base, "removed": [fx.removed_record()], "notices": [fx.notice()]}),
        ("removed-duplicate", {**base, "removed": [gone, gone]}),
        ("removed-no-notice", {**base, "notices": [fx.notice(replacement="1.1.0")]}),
    ):
        case("relation." + label, value)
    # The staged walk must not let a later relation/array rule mask an earlier field failure.
    case("order.discriminator", {"schema": 2, "unknown": 0})
    case("order.unknown-before-missing", {"schema": 1, "a~/b": 0})
    case("order.missing-before-value", {"schema": 1, "notices": 0, "operations": [], "removed": []})
    case("order.member-bytes", {**base, "notices": 0, "operations": 0})
    case("order.element-before-order", {**base, "operations": [newer, {**old, "digest": "bad"}]})
    case("order.walk-before-relation", {**base, "notices": [fx.notice(id="missing.encode")], "toolchain": ""})
    raw_errors = {
        "empty": (b"", "malformed"), "syntax": (b"{", "malformed"),
        "fraction": (b'{"schema":1.0}', "malformed"), "exponent": (b'{"schema":1e0}', "malformed"),
        "negative-zero": (b'{"schema":-0}', "malformed"), "big-int": (b'{"schema":9007199254740992}', "malformed"),
        "bom": (b'\xef\xbb\xbf{}', "malformed"), "trailing": (fx.canonical(base) + b"x", "malformed"),
        "surrogate": (b'{"schema":1,"x":"\\ud800"}', "malformed"),
        "utf8": (b'{"schema":1,"x":"\xed\xa0\x80"}', "malformed"),
        "depth": (b"[" * 33, "too_large"), "depth-priority": (b"x" + b"[" * 33, "too_large"),
        "string-cap": (b'{"schema":1,"x":"' + b"x" * 65537 + b'"}', "too_large"),
        "duplicate": (b'{"schema":1,"schema":1}', "duplicate_key /schema"),
        "duplicate-escaped": (b'{"schema":1,"schem\\u0061":1}', "duplicate_key /schema"),
        "duplicate-nested": (b'{"x":[{"a/b":1,"a/b":2}]}', "duplicate_key /x/0/a~1b"),
    }
    for label, (data, issue) in raw_errors.items():
        ctx.decode_case("C11.text." + label, data, ref.line("refused: " + issue), 1,
                        "C9 decode; U3 J1–J3 priority")
    for codepoint in [*range(32), *range(127, 160)]:
        char = chr(codepoint)
        case(f"presentation.key.{codepoint:02x}", {"schema": 1, "x" + char + "~/y": 0})
        case(f"presentation.value.{codepoint:02x}", {**base, "toolchain": "x" + char})
    for size in (59, 60, 61):
        case(f"presentation.value-choice.{size + 4}", {**base, "toolchain": "a" * size + "\x85"})
    case("presentation.literal-backslash-n", {"schema": 1, "x\\n~/y": 0})
    case("presentation.non-cc-separators", {"schema": 1, "x  ~/y": 0})
    for label, char in (("lf", "\n"), ("del", "\x7f"), ("nel", "\x85")):
        key = "x" + char + "~/y"
        raw_key = fx.canonical(key)
        data = b'{"schema":1,' + raw_key + b':0,' + raw_key + b':1}'
        ctx.decode_case("C11.presentation.duplicate." + label, data,
                        ref.line("refused: duplicate_key " + ref.pointer([key])), 1,
                        "C9/D3 controls after RFC6901 + before final LF")
    for path, label in ((["operations", 0, "obligations", 0], "name"), (["notices", 0], "reason"),
                        (["removed", 0], "toolchain")):
        case("c1-control." + label, changed(path, lambda node, label=label: node.update({label: "x\x85"})))
    case("c1-control.axiom", changed(["operations", 0, "obligations", 0],
         lambda node: node.update({"axioms": ["x\x85"]})))
    rng = random.Random(ctx.seed)
    generated = []
    for i in range(48):
        operations = []
        for j in range(rng.randrange(6)):
            states = [("proven", []), ("open", []), ("open", ["sorryAx"]),
                      ("trusts", ["Custom.a", "Custom.z"])]
            status, axioms = rng.choice(states)
            operations.append(fx.operation(id=f"dep{j}.op", digest=f"{i + j:064x}", obligations=[{
                "name": rng.choice(["p", "proof-é", "😀"]), "status": status, "axioms": axioms}]))
        value = fx.index(operations=operations)
        generated.append(value)
    def generated_roundtrip(noncanonical: bool = False) -> None:
        for i, value in enumerate(generated):
            assert ref.index_error(value) is None
            data = (json.dumps(value, ensure_ascii=True, indent=1).encode() if noncanonical else
                    fx.canonical(value) + b"\n")
            proc = ctx.decode(f"property-{int(noncanonical)}-{i}", data)
            ctx.eq(proc.returncode, 0, f"generated sample {i} exit")
            ctx.eq(proc.stdout, fx.canonical(value) + b"\n", f"generated sample {i} canonical bytes")
    for noncanonical in (False, True):
        ctx.add("C11.property." + ("normalize" if noncanonical else "roundtrip"), "F11",
                "C6/C9 canonical typed round trip", lambda noncanonical=noncanonical: generated_roundtrip(noncanonical),
                "48 fixed-seed valid schema values; 0..5 operations; every wire status")
    def usage_decode() -> None:
        for args in (["index", "decode"], ["index", "decode", "missing.json", "extra"],
                     ["index", "decode", "missing.json"]):
            root = ctx.work / ("decode-usage-" + str(len(args)))
            root.mkdir(exist_ok=True)
            proc = ctx.call(root, list(args), dev=True)
            ctx.eq(proc.returncode, 2, "decode usage/unreadable exit")
            ctx.eq(proc.stdout, b"", "decode usage/unreadable stdout")
    ctx.add("C11.usage-unreadable", "F11", "C9 driver decode", usage_decode)


def register_history(ctx: Any) -> None:
    fx = ctx.fx
    canonical = fx.canonical
    def prepare(name: str) -> Path:
        root = ctx.work / ("history-" + name)
        root.mkdir()
        fx.init_git(root)
        return root
    def write(root: Path, value: Any) -> None:
        (root / "index.json").write_bytes(canonical(value) + b"\n")
    def check_case(name: str, setup: Callable[[Path], tuple[int, list[str], str | None]]) -> None:
        def check() -> None:
            root = prepare(name)
            code, lines, stderr = setup(root)
            proc = ctx.call(root, ["index", "history"], dev=True)
            ctx.eq(proc.returncode, code, "history exit")
            ctx.eq(proc.stdout, ("\n".join(lines) + "\n").encode() if lines else b"", "history ordered lines")
            if stderr is None:
                ctx.eq(proc.stderr, b"", "history stderr")
            else:
                ctx.eq(proc.stderr, (stderr + "\n").encode(), "history infrastructure line")
        ctx.add("C10." + name, "F10", "C7/C9 history", check)
    def root_empty(root: Path) -> tuple[int, list[str], None]:
        fx.commit(root, None)
        return 0, [], None
    check_case("root-absent", root_empty)
    def root_index(root: Path) -> tuple[int, list[str], None]:
        fx.commit(root, fx.index(operations=[fx.operation()]))
        return 0, [], None
    check_case("root-index", root_index)
    def non_index_parent(root: Path) -> tuple[int, list[str], None]:
        fx.commit(root, None)
        fx.commit(root, fx.index(operations=[fx.operation()]))
        return 0, [], None
    check_case("parent-absent", non_index_parent)
    def variant(label: str) -> Callable[[Path], tuple[int, list[str], None]]:
        def setup(root: Path) -> tuple[int, list[str], None]:
            head = fx.commit(root, fx.index(operations=[fx.operation()]))
            if label == "working-malformed":
                (root / "index.json").write_bytes(b"{")
                return 1, ["history: working tree: index.json does not decode: malformed"], None
            if label == "working-absent":
                (root / "index.json").unlink()
                return 1, [f"history: {head}: base64.encode@1.0.0 vanished"], None
            value = fx.index(operations=[fx.operation()])
            what = ""
            if label == "changed":
                value["operations"][0]["digest"] = "3" * 64
                what = "changed its digest"
            elif label == "vanished":
                value["operations"] = []
                what = "vanished"
            elif label.startswith("removed"):
                record = fx.removed_record(last=head)
                value["operations"] = []
                value["removed"] = [record]
                value["notices"] = [fx.notice()]
                if label in ("removed-good", "removed-wrong-last", "removed-digest-first"):
                    value["toolchain"] = "leanprover/lean4:v9.9.9"
                if label == "removed-wrong-last":
                    record["last_commit"] = "0" * 40
                    what = f": the removal names lastCommit {'0' * 40}, expected {head}"
                elif label == "removed-digest-first":
                    record["digest"] = "3" * 64
                    value["toolchain"] = fx.TOOLCHAIN
                    what = "changed its digest"
                elif label == "removed-same-toolchain":
                    what = "was removed without a toolchain change"
            write(root, value)
            if label == "removed-good":
                return 0, [], None
            phrase = "base64.encode@1.0.0" + (what if what.startswith(":") else " " + what)
            return 1, [f"history: {head}: {phrase}"], None
        return setup
    for label in ("working-malformed", "working-absent", "changed", "vanished", "removed-good",
                  "removed-same-toolchain", "removed-wrong-last", "removed-digest-first"):
        check_case(label, variant(label))
    def committed_removal(root: Path, extra: bool = False) -> tuple[int, list[str], None]:
        old = fx.commit(root, fx.index(operations=[fx.operation()]))
        value = fx.index(removed=[fx.removed_record(last=old)], notices=[fx.notice()],
                         toolchain="leanprover/lean4:v9.9.9")
        fx.commit(root, value)
        if extra:
            fx.commit(root, value)
        return 0, [], None
    check_case("committed-removal", committed_removal)
    check_case("preserved-removal", lambda root: committed_removal(root, True))
    def two_baselines(root: Path) -> tuple[int, list[str], None]:
        parent = fx.commit(root, fx.index(operations=[fx.operation()]))
        head = fx.commit(root, fx.index(operations=[fx.operation()]))
        write(root, fx.index(operations=[fx.operation(digest="3" * 64)]))
        return 1, [f"history: {sha}: base64.encode@1.0.0 changed its digest" for sha in (head, parent)], None
    check_case("head-then-parent", two_baselines)
    def notice_edit(root: Path) -> tuple[int, list[str], None]:
        head = fx.commit(root, fx.index(operations=[fx.operation()], notices=[fx.notice()]))
        write(root, fx.index(operations=[fx.operation()], notices=[fx.notice(reason="changed")]))
        return 1, [f"history: {head}: the notices do not extend this commit's"], None
    check_case("notice-edited", notice_edit)
    def notice_append(root: Path) -> tuple[int, list[str], None]:
        value = fx.index(operations=[fx.operation()], notices=[fx.notice(reason="first")])
        fx.commit(root, value)
        value["notices"].append(fx.notice(reason="second"))
        write(root, value)
        return 0, [], None
    check_case("notice-appended", notice_append)
    def removed_edit(root: Path, drop: bool = False) -> tuple[int, list[str], None]:
        old = fx.commit(root, fx.index(operations=[fx.operation()]))
        value = fx.index(removed=[fx.removed_record(last=old)], notices=[fx.notice()],
                         toolchain="leanprover/lean4:v9.9.9")
        head = fx.commit(root, value)
        if drop:
            value["removed"] = []
            value["notices"] = []
        else:
            value["removed"][0]["digest"] = "3" * 64
        write(root, value)
        lines = [f"history: {head}: the removed records do not extend this commit's"]
        if drop:
            lines.append(f"history: {head}: the notices do not extend this commit's")
            lines.append(f"history: {old}: base64.encode@1.0.0 vanished")
        else:
            lines.append(f"history: {old}: base64.encode@1.0.0 changed its digest")
        return 1, lines, None
    check_case("removed-edited", removed_edit)
    check_case("removed-vanished", lambda root: removed_edit(root, True))
    def baseline_bad(root: Path) -> tuple[int, list[str], None]:
        (root / "index.json").write_bytes(b"{")
        head = fx.commit(root, None)
        write(root, fx.index())
        return 1, [f"history: {head}: index.json does not decode: malformed"], None
    check_case("baseline-undecodable", baseline_bad)
    def shallow(root: Path) -> tuple[int, list[str], str]:
        fx.commit(root, fx.index(operations=[fx.operation()]))
        (root / ".git/shallow").write_text(fx.git(root, "rev-parse", "HEAD") + "\n")
        (root / "index.json").write_bytes(b"{")
        return 2, [], "history: shallow repository: fetch the full history"
    check_case("shallow-precedence", shallow)
    def missing_parent() -> None:
        root = prepare("missing-parent")
        parent = fx.commit(root, fx.index(operations=[fx.operation()]))
        fx.commit(root, fx.index(operations=[fx.operation()]))
        (root / ".git/objects" / parent[:2] / parent[2:]).unlink()
        write(root, fx.index())
        proc = ctx.call(root, ["index", "history"], dev=True)
        ctx.eq(proc.returncode, 2, "unreadable parent exit outranks violations")
        ctx.eq(proc.stdout, b"", "exit 2 prints no violation")
        ctx.eq(proc.stderr.startswith(f"history: cannot read {parent}: ".encode()) and proc.stderr.endswith(b"\n"),
               True, "fixed cannot-read prefix + parent SHA")
    ctx.add("C10.parent-unreadable", "F10", "C7/C9 infrastructure precedence", missing_parent)
    def not_git(suffix: str = "") -> None:
        root = ctx.work / ("not-git" + suffix)
        root.mkdir()
        # Inside the suite's own repository would otherwise discover an ancestor .git.
        env = {"GIT_CEILING_DIRECTORIES": str(root.parent)}
        proc = ctx.call(root, ["index", "history", str(root)], dev=True, env=env)
        ctx.eq(proc.returncode, 2, "not-git exit")
        ctx.eq(proc.stdout, b"", "not-git stdout")
        ctx.eq(proc.stderr, ctx.ref.line(f"history: not a git work tree: {root}"), "not-git exact line")
    ctx.add("C10.not-worktree", "F10", "C9 history worktree", not_git)
    ctx.add("C10.presentation.control-path", "F10", "C9/D3 history path escaping",
            lambda: not_git("\n\x85"))
    def merge_logs(root: Path, removed: bool = False) -> tuple[int, list[str], None]:
        if removed:
            old = fx.commit(root, fx.index(operations=[fx.operation()]))
            base = fx.index(removed=[fx.removed_record(last=old)], notices=[fx.notice()],
                            toolchain="leanprover/lean4:v9.9.9")
            common = fx.commit(root, base)
        else:
            base = fx.index(operations=[fx.operation()])
            common = fx.commit(root, base)
        fx.git(root, "branch", "right", common)
        left_value = copy.deepcopy(base)
        if removed:
            left_value["removed"][0]["digest"] = "3" * 64
        else:
            left_value["notices"] = [fx.notice(reason="left")]
        left = fx.commit(root, left_value)
        fx.git(root, "switch", "-q", "right")
        right_value = copy.deepcopy(base)
        if removed:
            right_value["removed"][0]["digest"] = "4" * 64
        else:
            right_value["notices"] = [fx.notice(reason="right")]
        right = fx.commit(root, right_value)
        write(root, left_value)
        fx.git(root, "add", "index.json")
        tree = fx.git(root, "write-tree")
        head = fx.git(root, "commit-tree", tree, "-p", left, "-p", right, "-m", "merge fixture")
        fx.git(root, "reset", "--hard", head)
        what = "removed records" if removed else "notices"
        return 1, [f"history: {head}: the parents' {what} diverge: rebase to linearize",
                   f"history: {right}: the {what} do not extend this commit's"], None
    check_case("parents-notices-diverge", merge_logs)
    check_case("parents-removed-diverge", lambda root: merge_logs(root, True))
    def preserved_other_parent(root: Path) -> tuple[int, list[str], None]:
        common = fx.commit(root, fx.index())
        fx.git(root, "branch", "right", common)
        left_old = fx.commit(root, fx.index(operations=[fx.operation()]))
        removed = fx.index(removed=[fx.removed_record(last=left_old)], notices=[fx.notice()],
                           toolchain="leanprover/lean4:v9.9.9")
        left = fx.commit(root, removed)
        fx.git(root, "switch", "-q", "right")
        right = fx.commit(root, fx.index(operations=[fx.operation()]))
        write(root, removed)
        fx.git(root, "add", "index.json")
        tree = fx.git(root, "write-tree")
        head = fx.git(root, "commit-tree", tree, "-p", left, "-p", right, "-m", "preserved record merge")
        fx.git(root, "reset", "--hard", head)
        return 0, [], None
    check_case("removal-witness-preserved-across-parent", preserved_other_parent)
    def default_dir() -> None:
        root = prepare("explicit-dir")
        fx.commit(root, fx.index())
        a = ctx.call(root, ["index", "history"], dev=True)
        b = ctx.call(ctx.work, ["index", "history", str(root)], dev=True)
        ctx.eq((a.returncode, a.stdout, a.stderr), (0, b"", b""), "default cwd history")
        ctx.eq((b.returncode, b.stdout, b.stderr), (0, b"", b""), "explicit directory history")
    ctx.add("C10.explicit-dir", "F10", "C9 history cwd/dir", default_dir)
