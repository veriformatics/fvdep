"""Black-box P/L/E cases: project choice, actual Git snapshots, and entry resolution."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import json
import os
import re
import shutil
import threading
from pathlib import Path
from urllib.parse import quote

from tests.oracle.harness import (
    NEXT, ROOTS, TEXT, TRIAL, Context, Op, assert_regular_644, case, cc_escape, commit, edit_index,
    git, held_lock, index_row, jtext, manifest, need, proxy_entries, put, refresh_digest, wait_until,
)
from tests.oracle.reference import expect, request, trial

UNKNOWN = "trial.not_listed@1.0.0"
WEIGHTS = (2, -3, 5)
TRIAL_REQ = request(TRIAL, *WEIGHTS)
TRIAL_REPLY = trial(TRIAL, *WEIGHTS)
NEXT_REPLY = trial(NEXT, *WEIGHTS)
TOO_NEW = "leanprover/lean4:v99.0.0"
FETCH_ERROR = r"Fetch failed: .+\."
TOOLCHAIN_ERR = "Library commit {} uses Lean {}; this fvdep checks Lean {}. Install the matching fvdep or change the library pin."


def fetch_calls(log: Path) -> list[dict]:
    return [row for row in proxy_entries(log) if "fetch" in row["argv"]]


def unknown(c: Context, target: Op | str, **kwargs) -> None:
    name = target.target if isinstance(target, Op) else target
    c.oracle(target, **kwargs).failure(re.escape(f"unknown target {name}"))


def inconsistent(c: Context, op: Op, pin: str) -> None:
    c.oracle(op).failure(re.escape(f"the library snapshot {pin} is inconsistent:") + r" .+",
                         absent=("unknown target",))


def set_main(repo: Path, oid: str) -> None:
    git(repo, "update-ref", "refs/heads/main", oid)


@case("P.nearest", "P1–P3; O3", "nearest ancestor's old pin wins over outer project and newer main")
def nearest(c: Context) -> None:
    c.lib()
    f = c.need_fixture()
    outer = c.project(c.work / "outer", f.second)
    inner = c.project(outer / "inner", f.first)
    leaf = inner / "a" / "b"
    leaf.mkdir(parents=True)
    unknown(c, NEXT, cwd=leaf)
    c.published(f.first)
    need(not (c.store() / "head.json").exists(), "a pin was recorded as the head")
    need(not (c.store() / "trees" / f.second).exists(), "an outer/current head snapshot was fetched")


@case("P.explicit", "P1–P3; §2", "explicit project overrides a nearer pin; no project writes")
def explicit(c: Context) -> None:
    c.lib()
    f = c.need_fixture()
    nearer = c.project(c.work / "nearer", f.first)
    explicit_p = c.project(c.work / "explicit with space", f.second)
    # The consumer's vendored copy must never supply the served index.
    put(explicit_p, ".lake/packages/fvdep/index.json", "not an index")
    lock = put(explicit_p, "fvdep.lock", b"not read by oracle\x00")
    saved = {(d / "fvdep.toml"): (d / "fvdep.toml").read_bytes() for d in (nearer, explicit_p)}
    saved[lock] = lock.read_bytes()
    expect(c.oracle(NEXT, TRIAL_REQ, cwd=nearer, project=explicit_p), NEXT_REPLY)
    for file, raw in saved.items():
        need(file.read_bytes() == raw, f"oracle modified {file.name}")
    for project in (nearer, explicit_p):
        need(not (project / ".fvdep-writer.lock").exists(), "read-only oracle acquired a writer lock")


@case("P.explicit-missing", "P1; O3", "an explicit directory without a manifest refuses instead of consulting ancestors")
def explicit_missing(c: Context) -> None:
    c.lib()
    near = c.project(c.work / "near", c.need_fixture().second)
    elsewhere = near / "missing"
    elsewhere.mkdir()
    c.oracle(NEXT, TRIAL_REQ, cwd=near, project=elsewhere).failure(r"fvdep\.toml")
    need(not c.store().exists(), "missing project fell through to library selection")


def irregular_manifest(c: Context, shape: str, explicit: bool = False) -> None:
    c.lib()
    near = c.project(c.work / "outer", c.need_fixture().second)
    inner = near / "inner"
    inner.mkdir()
    file = inner / "fvdep.toml"
    if shape == "link":
        file.symlink_to(near / "fvdep.toml")
    else:
        os.mkfifo(file)
    c.oracle(NEXT, TRIAL_REQ, cwd=near if explicit else inner, project=inner if explicit else None).failure(
        r"\bio\b", r"fvdep\.toml", "link" if shape == "link" else r"(?i)regular|special|fifo",
    )
    need(not c.store().exists(), "irregular project fell through to library selection")


@case("P.manifest-link", "P1; O3", "nearest manifest symlink: io refusal, no fallback")
def nearest_link(c: Context) -> None:
    irregular_manifest(c, "link")


@case("P.explicit-link", "P1; O3", "explicit manifest symlink: io refusal, not followed")
def explicit_link(c: Context) -> None:
    irregular_manifest(c, "link", explicit=True)


@case("P.manifest-fifo", "P1; O3", "nearest manifest FIFO: io refusal without a reader wait")
def manifest_fifo(c: Context) -> None:
    irregular_manifest(c, "fifo")


@case("P.manifest-invalid", "P2; §7; U3 T1/T3", "invalid TOML, schema, key, pin and byte encoding refuse without head selection")
def manifest_invalid(c: Context) -> None:
    c.lib()
    pin = c.need_fixture().second
    for raw, reason in (
        ("schema = [\n", r"[0-9]+:[0-9]+"),
        (manifest(pin).replace("schema = 1", "schema = 2"), r"schema"),
        ("unexpected = 0\n" + manifest(pin), r"unexpected"),
        (manifest(pin.upper()), r"commit"),
        (b"\xef\xbb\xbf" + manifest(pin).encode(), r"(?i)BOM|byte 0"),
        (b"#\xff\n" + manifest(pin).encode(), r"(?i)UTF-8|offset"),
    ):
        c.project(c.work, pin, raw)
        c.oracle(NEXT, TRIAL_REQ).failure(r"fvdep\.toml", reason)
        need(not c.store().exists(), "invalid manifest fell through to library selection")


@case("P.manifest-size", "P2; §7", "65,536-byte valid manifest accepted; 65,537 bytes refused")
def manifest_size(c: Context) -> None:
    c.lib()
    pin = c.need_fixture().first
    body = manifest(pin).encode()
    exact = body + b"#" + b"x" * (65_536 - len(body) - 2) + b"\n"
    c.project(c.work, pin, exact + b"\n")
    c.oracle(TRIAL).failure(r"fvdep\.toml", r"(?i)schema|too_large")
    need(not c.store().exists(), "oversized manifest fell through to library selection")
    c.project(c.work, pin, exact)
    expect(c.oracle(TRIAL))
    c.published(pin)


@case("L.anchor-relative", "L1, L5–L6", "same relative source spelling gets distinct keys, trees and offline head records")
def relative_sources(c: Context) -> None:
    f = c.need_fixture()
    a, b = c.work / "a", c.work / "b"
    a.mkdir()
    b.mkdir()
    ra, rb = c.lib(first=True, into=a / "mirror"), c.lib(into=b / "mirror")
    expect(c.oracle(TRIAL, TRIAL_REQ, cwd=a, source="mirror"), TRIAL_REPLY)
    _, head_a = c.noted(f.first, ra)
    expect(c.oracle(NEXT, TRIAL_REQ, cwd=b, source="mirror"), NEXT_REPLY)
    _, head_b = c.noted(f.second, rb)
    need(head_a["source"] != head_b["source"], "distinct anchored source paths collided")
    ra.rename(a / "offline")
    result = c.oracle(TRIAL, TRIAL_REQ, cwd=a, source="mirror")
    expect(result, TRIAL_REPLY)
    need(re.search(rb"Last successful fetch: " + head_a["fetched"].encode() + rb"\.", result.err),
         "fallback did not use the first anchored source's fetch record")


@case("L.redact-url", "L1, L3", "synthetic URL userinfo never reaches diagnostics or a successful head record")
def redact(c: Context) -> None:
    src = c.lib()
    userinfo = "oracle-test-user:oracle-test-credential"
    url = f"file://{userinfo}@localhost{quote(str(src))}"
    redacted = url.replace(userinfo, "***")
    # file: never contacts a network service, even if a defective implementation bypasses the shim.
    diagnostic = f"fatal: '{url}' does not appear to be a git repository\n".encode()
    enable = c.home / "local-transport-ready"
    log = c.proxy("git", f"""if 'fetch' in args:
    if not os.path.exists({str(enable)!r}):
        os.write(2, {diagnostic!r})
        sys.exit(128)
    args = [{str(src)!r} if arg == {url!r} else arg for arg in args]
""")
    c.oracle(TRIAL, source=url).failure(re.escape(redacted), absent=(userinfo, "oracle-test-credential"))
    need(len(fetch_calls(log)) == 1, "the local diagnostic fixture did not receive a fetch")
    enable.touch()
    result = c.oracle(TRIAL, TRIAL_REQ, source=url)
    expect(result, TRIAL_REPLY)
    raw, _ = c.noted(c.need_fixture().second, url)
    need(b"oracle-test-credential" not in raw + result.err, "URL userinfo reached the record or progress output")


@case("L.publish-blobs", "L2, L4–L5; I3", "publish allowed raw blobs (no checkout filters; 100755 becomes 0644)")
def publish(c: Context) -> None:
    src = c.lib()
    name = "Fvdep/Trial/fixture-note.txt"
    raw = b"first\nsecond\n"
    put(src, name, raw).chmod(0o755)
    put(src, ".gitattributes", name + " text eol=crlf\n")
    put(src, "excluded.txt", "outside the root allowlist\n")
    (src / "excluded-link").symlink_to("excluded.txt")
    pin = commit(src)
    need(git(src, "show", f"{pin}:{name}") == raw, "fixture raw-blob control is not LF")
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)
    c.noted(pin)
    tree = c.published(pin)
    names = {os.fsdecode(x) for x in git(src, "ls-tree", "-r", "-z", "--name-only", pin, "--", *ROOTS).split(b"\0") if x}
    paths = list(tree.rglob("*"))
    need(not any(p.is_symlink() for p in paths), "snapshot contains a symlink")
    stored = {str(p.relative_to(tree)) for p in paths if not p.is_dir()}
    need(stored == names | {".complete"}, f"stored paths differ from the library root allowlist: {stored ^ names}")
    for path in names:
        file = tree / path
        assert_regular_644(file)
        need(file.read_bytes() == git(src, "show", f"{pin}:{path}"), f"snapshot transformed blob {path}")
    need((c.store() / "lock").is_file(), "source store lacks its permanent lock")
    need(not list((c.store() / "tmp").glob("*")), "fetch staging leaked")


@case("L.rebuild-incomplete", "L2, L5–L6", "replace a pre-existing tree without .complete, never read its bytes")
def incomplete(c: Context) -> None:
    c.lib()
    f = c.need_fixture()
    pin_dir = c.store() / "trees" / f.first
    put(pin_dir, "index.json", b"not json")
    dust = put(pin_dir, "incomplete-canary", b"must disappear")
    abandoned = c.store() / "tmp" / "2147483647.1.git"
    abandoned.mkdir(parents=True)
    c.project(c.work, f.first)
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)
    need(c.published(f.first) == pin_dir and not dust.exists(), "incomplete tree was not replaced")
    need(not (c.store() / "head.json").exists(), "pin rebuild wrote head.json")
    need(not abandoned.exists(), "fetch staging of an impossible PID was not cleaned")


@case("L.damaged-head", "L5–L6", "corrupt/noncanonical record, missing tree, or incomplete tree are store faults")
def damaged_head(c: Context) -> None:
    src = c.lib()
    f = c.need_fixture()
    expect(c.oracle(TRIAL))
    raw, obj = c.noted(f.second)
    p = c.store() / "head.json"
    src.rename(c.home / "offline")
    pattern = re.escape(f"the library store of {src} is damaged:") + r" .+"
    bad_records = (b"{", jtext(obj | {"schema": 2}), b" " + raw,
                   jtext(obj | {"source": "f" * 64}), jtext(obj | {"fetched": "yesterday"}))
    for bad in bad_records:
        p.write_bytes(bad)
        c.oracle(TRIAL, TRIAL_REQ).failure(pattern, absent=("Last successful fetch: never.",))
        need(p.read_bytes() == bad, "a failed head fetch overwrote a damaged record")
    p.write_bytes(raw)
    tree = c.published(f.second)
    aside = c.home / "complete-away"
    tree.rename(aside)
    c.oracle(TRIAL, TRIAL_REQ).failure(pattern, absent=("Last successful fetch: never.",))
    aside.rename(tree)
    (tree / ".complete").unlink()
    c.oracle(TRIAL, TRIAL_REQ).failure(pattern, absent=("Last successful fetch: never.",))


FETCH_FLAGS = (
    "--depth=1", "--atomic", "--no-tags", "--no-prune", "--no-recurse-submodules", "--no-auto-maintenance",
    "--no-write-commit-graph", "--no-write-fetch-head", "--refmap=",
)
FETCH_CONFIG = (
    "fetch.fsckObjects=true", "fetch.fsck.badFilemode=error", "fetch.fsck.gitattributesSymlink=error",
    "fetch.fsck.gitignoreSymlink=error", "fetch.fsck.gitmodulesParse=error", "core.hooksPath=/dev/null",
    "core.fsmonitor=false", "credential.helper=", "credential.interactive=false", "core.sshCommand=ssh -o BatchMode=yes",
    "http.followRedirects=false", "transfer.bundleURI=false", "promisor.acceptFromServer=none", "gc.auto=0",
)
FETCH_ENV = {
    "PATH", "LC_ALL", "GIT_CONFIG_NOSYSTEM", "GIT_CONFIG_GLOBAL", "GIT_TERMINAL_PROMPT", "GIT_ASKPASS",
    "SSH_ASKPASS", "HOME",
}


@case("L.head-then-pin", "L2–L6; P2", "distinct shallow direct refspecs, private fetch repos, pin never rewrites last head")
def head_pin(c: Context) -> None:
    src = c.lib()
    f = c.need_fixture()
    log = c.proxy("git")
    expect(c.oracle(NEXT, TRIAL_REQ), NEXT_REPLY)
    before, _ = c.noted(f.second)
    dev_project = c.project(c.work / "pinned", f.first)
    expect(c.oracle(TRIAL, TRIAL_REQ, cwd=dev_project), TRIAL_REPLY)
    c.published(f.first)
    need(c.head()[0] == before, "pin fetch overwrote the head record")
    fetches = fetch_calls(log)
    need(len(fetches) == 2, f"expected two fetches, got {len(fetches)}")
    private = []
    for row, ref in zip(fetches, ("+refs/heads/main:refs/fvdep/head", f"+{f.first}:refs/fvdep/pin"), strict=True):
        args = row["argv"]
        need(args[-3:] == ["--", str(src), ref], f"wrong fetch source/refspec: {args[-3:]!r}")
        need(set(FETCH_FLAGS + FETCH_CONFIG) <= set(args), f"missing isolation/bounded-fetch flags: {args!r}")
        need(set(row["env"]) == FETCH_ENV, f"git received ambient or missing environment keys: {row['env']!r}")
        repo = Path(args[args.index("-C") + 1]) if "-C" in args else Path(row["cwd"])
        need(repo.parent == c.store() / "tmp" and re.fullmatch(r"[0-9]+\.[0-9]+\.git", repo.name),
             f"fetch did not run in its private bare repository: {repo.name}")
        private.append(repo)
    need(len(set(private)) == 2 and not any(p.exists() for p in private), "fetch repositories were reused or leaked")
    inits = [row["argv"] for row in proxy_entries(log) if "init" in row["argv"]]
    need(len(inits) == 2 and all({"--bare", "-q", "--template="} <= set(x) for x in inits),
         "fresh bare init did not disable ambient templates")


@case("L.pin-offline", "L6; P2", "warm pin serves without fetch; uncached pin never reuses the stored head")
def pin_offline(c: Context) -> None:
    src = c.lib()
    f = c.need_fixture()
    log = c.proxy("git")
    expect(c.oracle(NEXT, TRIAL_REQ), NEXT_REPLY)
    raw, _ = c.noted(f.second)
    src.rename(c.home / "offline")
    project = c.project(c.work / "warm-pin", f.second)
    good = c.oracle(NEXT, TRIAL_REQ, cwd=project)
    expect(good, NEXT_REPLY)
    need(b"Fetch failed:" not in good.err and len(fetch_calls(log)) == 1, "published pin attempted a fetch")
    c.project(project, f.first)
    c.oracle(TRIAL, TRIAL_REQ, cwd=project).failure(FETCH_ERROR, absent=("Last successful fetch:",))
    need(c.head()[0] == raw and not (c.store() / "trees" / f.first).exists(), "pin failure published another head")


@case("L.offline-head", "L5–L6", "local transport loss serves last fetched head + its exact stored UTC time")
def offline_head(c: Context) -> None:
    src = c.lib()
    expect(c.oracle(NEXT, TRIAL_REQ), NEXT_REPLY)
    raw, obj = c.noted(c.need_fixture().second)
    src.rename(c.home / "unreachable")
    result = c.oracle(NEXT, TRIAL_REQ)
    expect(result, NEXT_REPLY)
    notice = rf"^Fetch failed: .+\. Last successful fetch: {re.escape(obj['fetched'])}\.$"
    need(any(re.fullmatch(notice, s) for s in result.err.decode().split("\n")), "missing exact offline notice")
    need(c.head()[0] == raw, "offline head read rewrote head.json")


@case("L.never-fetched", "L6; §3", "unreachable local source with no head says never, exit 2", fixture=False)
def never_fetched(c: Context) -> None:
    c.oracle(TRIAL, TRIAL_REQ).failure(r"^Fetch failed: .+\. Last successful fetch: never\.$")
    need(not (c.store() / "head.json").exists(), "never-fetched failure wrote a head record")


@case("L.required", "L4, L6", "each required library file missing is a received-but-failing candidate, not fallback")
def required(c: Context) -> None:
    src = c.lib()
    f = c.need_fixture()
    expect(c.oracle(TRIAL))
    saved, _ = c.noted(f.second)
    for path in ("lakefile.lean", "lean-toolchain", "index.json", "Fvdep.lean", "Fvdep/Registry.lean"):
        git(src, "reset", "--hard", f.second)
        (src / path).unlink()
        pin = commit(src, f"Omit {path}")
        c.oracle(TRIAL, TRIAL_REQ).failure(r"is no fvdep library", absent=("Last successful fetch:",))
        need(c.head()[0] == saved and not (c.store() / "trees" / pin).exists(), "malformed candidate replaced the head")


@case("L.link", "L4, L6", "a link under a library path is named verbatim and does not replace last head")
def link(c: Context) -> None:
    src = c.lib()
    expect(c.oracle(TRIAL))
    before, _ = c.noted(c.need_fixture().second)
    path = "Fvdep/Trial/linked.txt"
    (src / path).symlink_to("../../../lean-toolchain")
    pin = commit(src)
    c.oracle(TRIAL, TRIAL_REQ).failure(re.escape(f"the library snapshot {pin} holds a link at {path}"),
                                     absent=("Last successful fetch:",))
    need(c.head()[0] == before, "a link-containing candidate changed head.json")


@case("L.gitlink", "L4", "submodule-mode entry under a library path refuses; no checkout or recursion")
def gitlink(c: Context) -> None:
    src = c.lib()
    path = "Fvdep/Trial/imported"
    pin = c.need_fixture().second
    git(src, "update-index", "--add", "--cacheinfo", f"160000,{pin},{path}")
    git(src, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "Gitlink fixture")
    head = git(src, "rev-parse", "HEAD").decode().strip()
    c.oracle(TRIAL).failure(re.escape(f"the library snapshot {head} holds a submodule at {path}"))


@case("L.fsck-mode", "L3–L4, L6", "a bad raw tree mode refuses during fsck or tree policy, never fallback")
def fsck_mode(c: Context) -> None:
    src = c.lib()
    pin = c.need_fixture().second
    expect(c.oracle(TRIAL))
    before, _ = c.noted(pin)
    oid = git(src, "rev-parse", f"{pin}^{{tree}}").decode().strip()
    entries = git(src, "cat-file", "tree", oid)
    old = b"100644 index.json\x00"
    need(entries.count(old) == 1, "raw mode plant lacks its positive control")
    tree = git(src, "hash-object", "--literally", "-t", "tree", "-w", "--stdin",
               data=entries.replace(old, b"100664 index.json\x00")).decode().strip()
    damaged = git(src, "commit-tree", tree, "-p", pin, "-m", "Bad mode fixture").decode().strip()
    set_main(src, damaged)
    c.oracle(TRIAL, TRIAL_REQ).failure(r"(?i)badfilemode|bad file ?mode|holds an entry of mode 100664",
                                      absent=("Last successful fetch:",))
    need(c.head()[0] == before, "bad-mode candidate changed head.json")
    need(not list((c.store() / "tmp").glob("*")), "failed fsck left a private repository")


@case("L.invalid-paths", "L4; I3", "reject leading-dot components and invalid UTF-8 filename bytes")
def invalid_paths(c: Context) -> None:
    src = c.lib()
    for tail, reason in ((".oracle-dot/name", r"(?:\.oracle-dot|path component)"),
                         (os.fsdecode(b"invalid-\xff.txt"), r"(?i)UTF-8|invalid.path")):
        git(src, "reset", "--hard", c.need_fixture().second)
        put(src, "Fvdep/Trial/" + tail, b"path fixture")
        pin = commit(src)
        c.oracle(TRIAL).failure(reason, absent=("Last successful fetch:",))
        need(not (c.store() / "trees" / pin).exists(), "invalid path was published")


@case("L.path-depth", "L4", "32 relative components accepted; 33 refused")
def path_depth(c: Context) -> None:
    src = c.lib()
    base = c.need_fixture().second
    for n in (33, 32):
        path = "/".join(["Fvdep", *(["depth"] * (n - 2)), "file.txt"])
        put(src, path, b"data")
        pin = commit(src)
        result = c.oracle(TRIAL)
        if n == 33:
            result.failure(r"(?i)depth|components|too deep|33", absent=("Last successful fetch:",))
            need(not (c.store() / "trees" / pin).exists(), "over-depth snapshot was published")
            git(src, "reset", "--hard", base)
        else:
            expect(result)
            need((c.published(pin) / path).read_bytes() == b"data", "max-depth blob missing")


def tree_record(path: bytes, *, directory: bool = False, mode: str | None = None) -> bytes:
    # L4 shaped observations: valid-looking OIDs are enough because the test stops at the
    # first blob query. No synthetic long path ever reaches the host filesystem.
    source_mode = mode or ("040000" if directory else "100644")
    kind, size = ("tree", "-") if directory else ("blob", "0")
    return f"{source_mode} {kind} {'7' * 40} {size:>7}\t".encode() + path + b"\x00"


def listed_paths(transcript: bytes) -> list[bytes]:
    return [record.split(b"\t", 1)[1] for record in transcript.split(b"\x00") if record]


def tree_proxy(c: Context, appendix: Path) -> Path:
    return c.proxy("git", f"""if 'ls-tree' in args and '-r' in args and args[-1] == 'Fvdep':
    import subprocess
    child = subprocess.run([real, *args], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, check=False)
    if child.returncode:
        sys.exit(child.returncode)
    sys.stdout.buffer.write(child.stdout)
    with open({str(appendix)!r}, 'rb') as f:
        sys.stdout.buffer.write(f.read())
    sys.exit(0)
if 'cat-file' in args and '--batch' in args:
    os.write(2, b'oracle-blob-checkpoint\\n')
    sys.exit(128)
""")


def check_tree_limit(c: Context, log: Path, *, crosses: bool) -> None:
    start = len(proxy_entries(log))
    result = c.oracle(TRIAL)
    result.failure(r"(?i)path|size|bytes|limit" if crosses else r"(?i)blob|cat-file")
    entries = proxy_entries(log)[start:]
    need(any("ls-tree" in row["argv"] for row in entries), "tree transcript was not used")
    saw_batch = any("cat-file" in row["argv"] and "--batch" in row["argv"] for row in entries)
    need(saw_batch is not crosses, "Git blob-transfer checkpoint disagrees with the inclusive path cap")
    need(not (c.store() / "head.json").exists(), "tree/transfer refusal published a head")


@case("L.path-bytes", "L4; I3", "4,096-byte relative path reaches blob transfer; 4,097-byte path is refused first")
def path_bytes(c: Context) -> None:
    c.lib()
    appendix = c.home / "append-tree.bin"
    log = tree_proxy(c, appendix)
    for n in (4096, 4097):
        prefix = b"Fvdep/zzOraclePath"
        listing = [tree_record(prefix, directory=True)]
        while n - len(prefix) > 241:
            prefix += b"/" + b"a" * 240
            listing.append(tree_record(prefix, directory=True))
        path = prefix + b"/" + b"x" * (n - len(prefix) - 1)
        need(len(path) == n and path.count(b"/") < 32, "path-bytes control has an unintended depth/length")
        appendix.write_bytes(b"".join([*listing, tree_record(path)]))
        check_tree_limit(c, log, crosses=n > 4096)


@case("L.path-sum", "L4; I3", "4 MiB cumulative listed path bytes accepted at policy, one more byte refused before blob query")
def path_sum(c: Context) -> None:
    src = c.lib()
    for name in ("FvdepPreview", "FvdepProofs"):
        if (src / name).is_dir():
            shutil.rmtree(src / name)
    pin = commit(src)
    top = git(src, "ls-tree", "-t", "-l", "-z", "--full-tree", pin, "--", *ROOTS)
    recursive = git(src, "ls-tree", "-r", "-t", "-l", "-z", "--full-tree", pin, "--", "Fvdep")
    prefix = b"Fvdep/zzOracleSum"
    directories = [prefix]
    for _ in range(14):
        prefix += b"/" + b"a" * 240
        directories.append(prefix)
    fixed = listed_paths(top) + listed_paths(recursive) + directories
    appendix = c.home / "append-tree.bin"
    log = tree_proxy(c, appendix)
    for n in (4 * 2**20, 4 * 2**20 + 1):
        remaining = n - sum(map(len, fixed))
        count = remaining // (len(prefix) + 129)
        width, extra = divmod(remaining, count)
        files = []
        for i in range(count):
            head = prefix + f"/b{i:05d}".encode()
            length = width + (i < extra)
            need(len(head) <= length <= min(4096, len(prefix) + 251), "path-sum leaf violates another cap")
            files.append(head + b"x" * (length - len(head)))
        need(sum(map(len, fixed + files)) == n and len(fixed + files) <= 10_000,
             "path-sum transcript has an incorrect total or entry count")
        appendix.write_bytes(b"".join([*(tree_record(p, directory=True) for p in directories),
                                        *(tree_record(p) for p in files)]))
        check_tree_limit(c, log, crosses=n > 4 * 2**20)


@case("L.odd-mode", "L4", "an observable unknown tree-listing mode is refused with commit, mode and path")
def odd_mode(c: Context) -> None:
    c.lib()
    appendix = c.home / "append-tree.bin"
    path = b"Fvdep/zzOracleMode.txt"
    appendix.write_bytes(tree_record(path, mode="100666"))
    log = tree_proxy(c, appendix)
    pin = c.need_fixture().second
    c.oracle(TRIAL).failure(re.escape(f"the library snapshot {pin} holds an entry of mode 100666 at {path.decode()}"))
    need(not any("--batch" in row["argv"] for row in proxy_entries(log)), "unrecognized mode reached blob transfer")


@case("L.file-size", "L4", "regular blob at 1 MiB accepted; 1 MiB + one refused before blob transfer")
def file_size(c: Context) -> None:
    src = c.lib()
    rel = "Fvdep/Trial/size-bound.txt"
    log = c.proxy("git")
    for n in (2**20 + 1, 2**20):
        put(src, rel, b"x" * n)
        pin = commit(src)
        start = len(proxy_entries(log))
        result = c.oracle(TRIAL)
        if n > 2**20:
            result.failure(r"(?i)size|bytes|limit", absent=("Last successful fetch:",))
            calls = proxy_entries(log)[start:]
            need(any("ls-tree" in row["argv"] for row in calls), "Git did not list the oversized blob")
            need(not any("--batch" in row["argv"] for row in calls), "blob transfer preceded listed-size refusal")
        else:
            expect(result)
            need((c.published(pin) / rel).stat().st_size == n, "inclusive file-size bound lost its blob")


@case("L.tree-count", "L4; Q3", "count root/tree/blob records, limit exact accepts and one fewer refuses")
def tree_count(c: Context) -> None:
    src = c.lib()
    pin = c.need_fixture().second
    n = git(src, "ls-tree", "-r", "-t", "-z", "--full-tree", pin, "--", *ROOTS).count(b"\x00")
    need(n > len(ROOTS), "tree-count fixture did not include recursive records")
    c.oracle(TRIAL, limits={"treeEntries": n - 1}).failure(r"(?i)tree|entr(?:y|ies)", r"(?i)limit|exceed|too many")
    need(not (c.store() / "trees" / pin).exists(), "over-entry snapshot was published")
    expect(c.oracle(TRIAL, limits={"treeEntries": n}))
    c.published(pin)


@case("L.snapshot-size", "L4; Q3", "sum listed blob sizes, exact limit accepts and one fewer refuses")
def snapshot_size(c: Context) -> None:
    src = c.lib()
    pin = c.need_fixture().second
    rows = git(src, "ls-tree", "-r", "-l", "-z", "--full-tree", pin, "--", *ROOTS).split(b"\x00")
    sizes = [int(w[3]) for row in rows if row and (w := row.split(b"\t", 1)[0].split())[1] == b"blob"]
    n = sum(sizes)
    need(n > max(sizes), "total-byte fixture failed to include multiple blobs")
    c.oracle(TRIAL, limits={"snapshotBytes": n - 1}).failure(r"(?i)size|bytes|limit")
    need(not (c.store() / "trees" / pin).exists(), "oversized snapshot was published")
    expect(c.oracle(TRIAL, limits={"snapshotBytes": n}))
    c.published(pin)


@case("L.diagnostics", "L3; §1", "Git capture at/over cap preserves first-line text and escapes Cc", fixture=False)
def diagnostics(c: Context) -> None:
    first = "oracle-fetch-canary\t\r\x1b\x7f\x85"
    overflow = "PLANT_AFTER_CAPTURE_CAP"
    n = 192
    path = c.home / "git-stderr.bin"
    log = c.proxy("git", f"""if 'fetch' in args:
    with open({str(path)!r}, 'rb') as f:
        sys.stderr.buffer.write(f.read())
    sys.exit(128)
""")
    raw = first.encode()
    exact = raw + b"X" * (n - len(raw) - 2) + b"!\n"
    for data in (exact, exact + b"\x04", raw + b"X" * 200000 + overflow.encode() + b"\nsecond-line\n"):
        path.write_bytes(data)
        result = c.oracle(TRIAL, limits={"gitBytes": n})
        prefix = cc_escape(exact[:-1].decode() if data.startswith(exact) else first)
        result.failure(re.escape(prefix), absent=(overflow, "second-line", r"\u0004"))
        need(result.err.count(b"X") <= n, "captured diagnostics exceed the per-stream byte cap")
    need(len(fetch_calls(log)) == 3, "diagnostic producer was not called on each trial")


@case("L.fetch-timeout", "L3, L6; Q3", "timed-out local fetch group stops, child is reaped and no snapshot is published", fixture=False)
def fetch_timeout(c: Context) -> None:
    started = c.home / "fetch-started"
    ended = c.home / "fetch-ended"
    log = c.proxy("git", f"""if 'fetch' in args:
    import subprocess
    worker = subprocess.Popen([sys.executable, '-I', '-c', 'import time; time.sleep(15)'])
    with open({str(started)!r}, 'w') as f:
        f.write(f'{{os.getpid()}} {{worker.pid}}')
    worker.wait()
    with open({str(ended)!r}, 'w'):
        pass
    sys.exit(128)
""")
    c.oracle(TRIAL, limits={"fetchSeconds": 2}).failure(r"(?i)fetch", r"(?i)deadline|timed?[- ]?out|timeout")
    need(started.is_file() and not ended.exists(), "fetch was not killed during its deadline window")
    pid, worker = map(int, started.read_text().split())
    need(not Path(f"/proc/{pid}").exists(), "timed-out fetch child was not reaped")
    stat_path = Path(f"/proc/{worker}/stat")

    def child_stopped() -> bool:
        try:
            return stat_path.read_text().rsplit(")", 1)[1].split()[0] == "Z"
        except FileNotFoundError:
            return True

    # The outer vflab namespace's init need not reap an orphan, but it cannot still be running.
    wait_until(child_stopped, 2, "the local fetch's child to stop")
    need(len(fetch_calls(log)) == 1, "unexpected fetch attempts")
    need(not (c.store() / "head.json").exists(), "timed-out fetch wrote a head")
    need(not list((c.store() / "tmp").glob("*")), "timed-out fetch leaked staging")


@case("L.lock-timeout", "L2; Q3", "an externally held source flock times out before any fetch", fixture=False)
def lock_timeout(c: Context) -> None:
    log = c.proxy("git")
    with held_lock(c.store() / "lock"):
        c.oracle(TRIAL, limits={"lockSeconds": 1}).failure(
            re.escape(f"infra io: the library store of {c.source} stayed locked"))
    need(not fetch_calls(log), "an acquired foreign lock did not stop fetch")


@case("L.concurrent", "L2, L5–L6", "two parallel callers succeed, one complete tree, no staging residue")
def concurrent(c: Context) -> None:
    c.lib()
    pin = c.need_fixture().second
    log = c.proxy("git", "if 'fetch' in args:\n    time.sleep(0.2)\n")
    started = threading.Barrier(2)

    def call() -> None:
        started.wait(timeout=10)
        expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)

    with ThreadPoolExecutor(max_workers=2) as pool:
        jobs = [pool.submit(call) for _ in range(2)]
        for job in jobs:
            job.result()
    c.noted(pin)
    need({p.name for p in (c.store() / "trees").iterdir()} == {pin}, "concurrent publish created extra trees")
    need(not list((c.store() / "tmp").glob("*")), "concurrent fetch leaked staging")
    need(len(fetch_calls(log)) == 2, "no-project callers must each attempt a head fetch")


@case("L.toolchain", "L5–L7; E1", "incompatible complete head recorded, exact refusal precedes index read; no rollback")
def toolchain(c: Context) -> None:
    src = c.lib()
    f = c.need_fixture()
    expect(c.oracle(TRIAL))
    c.noted(f.second)
    put(src, "lean-toolchain", " \t" + TOO_NEW + "\r\n")
    put(src, "index.json", "{not_json")
    pin = commit(src)
    text = TOOLCHAIN_ERR.format(pin, TOO_NEW, f.toolchain)
    c.oracle(TRIAL, TRIAL_REQ).failure(re.escape(text), absent=("Last successful fetch:",))
    _, head = c.noted(pin)
    src.rename(c.home / "offline")
    c.oracle(TRIAL, TRIAL_REQ).failure(re.escape(text), re.escape(f"Last successful fetch: {head['fetched']}."))


@case("E.target-grammar", "E1; O1, O3; library Naming", "malformed operation targets refuse as usage before touching the source", fixture=False)
def grammar(c: Context) -> None:
    log = c.proxy("git")
    for target in ("trial.weight_mix", "TRIAL.weight_mix@1.0.0", "trial.weight__mix@1.0.0",
                   "trial.0mix@1.0.0", "trial.weight_0mix@1.0.0", "trial.weight_mix@01.0.0",
                   "trial.weight_mix@1.0.0-rc.1", "trial.weight_mix@1.0.0@2.0.0", "@1.0.0"):
        c.oracle(target).failure(r"(?i)usage|invalid target", absent=("Fetch failed", "unknown target"))
    need(not c.cache.exists() and not proxy_entries(log), "malformed target touched the cache or ran git")
    # Distinguish command-specific rejection from pre-unit generic usage.
    help_result = c.local_stdout("oracle", "--help").code(0)
    need(b"oracle" in help_result.out, "oracle has no command-specific help")


@case("E.absent", "E1; L5", "canonical absent id/version and profile target refused, but head is recorded")
def missing(c: Context) -> None:
    c.lib()
    for target in (UNKNOWN, "trial.weight_mix@10.0.0", "npm:base64-js@1.5.1"):
        unknown(c, target)
    c.noted(c.need_fixture().second)


@case("E.removed", "E1; U4 C6", "removed row does not serve even if its source files still exist")
def removed(c: Context) -> None:
    src = c.lib()
    f = c.need_fixture()

    def edit(index):
        row = index_row(index, TRIAL)
        index["operations"].remove(row)
        index["removed"].append({"id": TRIAL.id, "version": TRIAL.version, "digest": row["digest"],
                                  "kind": "operation", "toolchain": f.toolchain, "last_commit": f.first})
        index["notices"].append({"id": TRIAL.id, "version": TRIAL.version,
                                  "reason": "Removed fixture", "replacement": NEXT.version})

    edit_index(src, edit)
    pin = commit(src)
    unknown(c, TRIAL, data=TRIAL_REQ)
    c.noted(pin)


@case("E.retracted", "E1; O1; §8", "listed retraction neither hides the spec nor makes a delivery claim")
def retracted(c: Context) -> None:
    src = c.lib()
    edit_index(src, lambda i: i["notices"].append({"id": TRIAL.id, "version": TRIAL.version,
                                                  "reason": "Retracted fixture", "replacement": NEXT.version}))
    commit(src)
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)


@case("E.bad-index", "E1; U4 C6", "malformed, duplicate and schema-invalid index refuse before absent target")
def bad_index(c: Context) -> None:
    src = c.lib()
    good = (src / "index.json").read_bytes()
    for data, reason in ((b"{bad", r"(?i)malformed|invalid"),
                         (good.replace(b'"schema":1', b'"schema":1,"schema":1'), r"schema"),
                         (good.replace(b'"schema":1', b'"schema":2'), r"schema")):
        need(data != good, "index plant did not change its input")
        put(src, "index.json", data)
        commit(src)
        c.oracle(UNKNOWN).failure(r"index\.json", reason, absent=("unknown target",))


@case("E.inconsistent", "E2", "listed entry with a source/digest mismatch, wrong toolchain or missing entry file refuses")
def bad_identity(c: Context) -> None:
    src = c.lib()
    pin = c.need_fixture().second
    put(src, TRIAL.spec_path, (src / TRIAL.spec_path).read_bytes() + b"\n-- source bytes changed\n")
    inconsistent(c, TRIAL, commit(src, "Stale entry digest"))
    git(src, "reset", "--hard", pin)
    edit_index(src, lambda i: i.update(toolchain=TOO_NEW))
    inconsistent(c, TRIAL, commit(src, "Index tree toolchain mismatch"))
    git(src, "reset", "--hard", pin)
    (src / TRIAL.entry_path).unlink()
    inconsistent(c, TRIAL, commit(src, "Listed entry absent"))


def patch_part(src: Path, op: Op, rel: str, before: str, after: str) -> str:
    text = (src / rel).read_text()
    need(text.count(before) == 1, f"negative fixture edit has no unique anchor: {before!r}")
    put(src, rel, text.replace(before, after))
    refresh_digest(src, op)
    return commit(src)


@case("E.entry-fields", "E2–E3; U4 C2", "coherent bytes with wrong entry id/version or non-def entry are inconsistent")
def bad_entry(c: Context) -> None:
    src = c.lib()
    for before, after in ((f'id := "{TRIAL.id}"', 'id := "trial.other"'),
                          (f'version := "{TRIAL.version}"', 'version := "4.0.0"'),
                          ("def entry :", "opaque entry :")):
        git(src, "reset", "--hard", c.need_fixture().second)
        pin = patch_part(src, TRIAL, TRIAL.entry_path, before, after)
        inconsistent(c, TRIAL, pin)


@case("E.spec-type", "E4; U4 B1", "unsupported type is not misclassified as missing target or parse failure")
def unsupported_type(c: Context) -> None:
    src = c.lib()
    patch_part(src, TRIAL, TRIAL.spec_path,
               "{a : Int} (b c : Int) : Option Int :=\n  if b == c then none else some (a + 2 * b - 3 * c)",
               "(a : Bool) : Bool := !a")
    c.oracle(TRIAL, TRIAL_REQ).failure(
        re.escape(f"the spec of {TRIAL.target} has a type the adapter protocol cannot carry"), absent=("unknown target",))


@case("E.decode-budget", "E5; Q3", "registry decoding exceeding a lowered node budget refuses, then default serves")
def decode_budget(c: Context) -> None:
    c.lib()
    c.oracle(TRIAL, TRIAL_REQ, limits={"decodeNodes": 1}).failure(
        re.escape(f"infra io: the registry entry of {TRIAL.target} exceeds 1 nodes"))
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)


@case("E.selected-only", "E1–E4; I1; §8", "unrelated library root/entry damage does not force full index rebuild or admission")
def selected_only(c: Context) -> None:
    src = c.lib()
    put(src, "Fvdep/Registry.lean", "this is not a valid Lean registry\n")
    edit_index(src, lambda i: index_row(i, NEXT).update(digest="f" * 64))
    commit(src)
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)


@case("X.profile-text", "X1, X5; E4", "real pinned exporter can emit a literal outside the reader's JSON profile")
def export_profile(c: Context) -> None:
    src = c.lib()
    before = "def turnText (xs : List Char) : List Char := xs.reverse"
    text = json.dumps("x" * 65_537)
    patch_part(src, TEXT, TEXT.spec_path, before,
               f"def turnText (xs : List Char) : List Char := xs ++ {text}.toList")
    c.oracle(TEXT).failure(r"the export is outside the reader's profile at line [1-9][0-9]*: .+")


@case("Q.history-and-reuse", "Q2; E2; U5 K7", "new head adds a different version, old closure compiles zero; warm old pin still serves")
def histories(c: Context) -> None:
    src = c.lib(first=True)
    f = c.need_fixture()
    trace = c.home / "build.trace"
    c.env["FVDEP_BUILD_TRACE"] = str(trace)
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)
    c.noted(f.first)
    cold = trace.read_bytes()
    modules = {line.split()[1].decode() for line in cold.splitlines()}
    need({TRIAL.entry, TRIAL.spec, "Fvdep.Semver.Version.V1_0_0"} <= modules,
         "cold build trace lacks its positive entry/spec/independent Version roots")
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)
    need(trace.read_bytes() == cold, "an unchanged head recompiled a closure")
    set_main(src, f.second)
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)
    c.noted(f.second)
    need(trace.read_bytes() == cold, "unrelated new version rebuilt the old closure")
    expect(c.oracle(NEXT, TRIAL_REQ), NEXT_REPLY)
    later = trace.read_bytes()
    added = [line.split()[1].decode() for line in later[len(cold):].splitlines()]
    need(later.startswith(cold) and sorted(added) == sorted((NEXT.spec, NEXT.entry)),
         f"new version compiled more or fewer than its two new modules: {added!r}")
    need(TRIAL_REPLY != NEXT_REPLY, "the two fixture versions do not distinguish behavior")
    src.rename(c.home / "offline")
    c.project(c.work, f.first)
    expect(c.oracle(TRIAL, TRIAL_REQ), TRIAL_REPLY)
    unknown(c, NEXT, data=TRIAL_REQ)
    need(trace.read_bytes() == later and c.head()[1]["commit"] == f.second,
         "warm published old pin rebuilt or changed the last head")
