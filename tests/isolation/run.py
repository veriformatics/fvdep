#!/usr/bin/env python3
"""U5 isolation tests (contract docs/contracts/U5-sandbox.md G1, G3, G4 through D2; MAIN's suite).

Each case runs a python probe inside one `fvdep-dev sandbox run` step (or the helper alone in a
fresh bwrap namespace) and checks, inside the step + from the host, the one mechanism its tag names.
Credit = red on a mutant of the runner (`tests/isolation/mutants.py`: STUB = every mechanism off,
steps still running, + one mutant per guard). Scratch lives under the repo's `.gate/` (below
`$HOME`: the stub's writable home bind reaches it).
"""

from __future__ import annotations

import argparse
import ast
import os
import secrets
import shutil
import socket
import stat
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Callable
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DEV = ROOT / "tool" / ".lake" / "build" / "bin" / "fvdep-dev"
PY = "/usr/bin/python3"

Case = tuple[str, str, Callable[[Path], None]]
CASES: list[Case] = []


def case(cid: str, mech: str) -> Callable[[Callable[[Path], None]], Callable[[Path], None]]:
    def register(f: Callable[[Path], None]) -> Callable[[Path], None]:
        CASES.append((cid, mech, f))
        return f

    return register


class Fail(Exception):
    pass


def need(cond: bool, msg: str) -> None:
    if not cond:
        raise Fail(msg)


def sandbox(script: str, *opts: str, env: dict[str, str] | None = None, timeout: int = 180,
            pass_fds: tuple[int, ...] = ()) -> subprocess.CompletedProcess[str]:
    argv = [str(DEV), "sandbox", "run", *opts, "--", PY, "-I", "-c", script]
    return subprocess.run(argv, capture_output=True, text=True, env=env, timeout=timeout,
                          pass_fds=pass_fds, check=False)


def report(r: subprocess.CompletedProcess[str]) -> dict[str, str]:
    """The probe's `KEY value` lines (D2 relays them as `out: KEY value`)."""
    out: dict[str, str] = {}
    for line in r.stdout.splitlines():
        if line.startswith("out: "):
            key, _, value = line[5:].partition(" ")
            out[key] = value
    return out


def ran(r: subprocess.CompletedProcess[str]) -> dict[str, str]:
    need(r.returncode == 0, f"fvdep-dev exit {r.returncode}: {r.stderr.strip()[:300]}")
    need("outcome exited 0" in r.stdout.splitlines(), f"step: {r.stdout.strip()[:400]}")
    return report(r)


def failed(rep: dict[str, str], key: str) -> bool:
    """The probe reported an error (an errno or a refusal), not `ok`."""
    return rep.get(key) not in (None, "ok")


def holders(marker: str) -> list[int]:
    """Host processes whose command line holds `marker`."""
    found = []
    for p in Path("/proc").iterdir():
        if p.name.isdigit() and int(p.name) != os.getpid():
            try:
                if marker.encode() in (p / "cmdline").read_bytes():
                    found.append(int(p.name))
            except OSError:
                pass
    return found


def gone(marker: str, seconds: float) -> bool:
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        if not holders(marker):
            return True
        time.sleep(0.1)
    return not holders(marker)


WRITE = """import os
for p in {targets!r}:
    try:
        fd = os.open(p, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        os.close(fd)
        print('W:' + p, 'ok')
    except OSError as e:
        print('W:' + p, e.errno)
"""


@case("G1.write.host", "layout")
def write_host(tmp: Path) -> None:
    home, cache, src = tmp / "home", tmp / "cache", tmp / "src"
    for d in (home, cache, src):
        d.mkdir()
    (src / "data").write_text("source")
    targets = [str(home / "m"), str(cache / "m"), str(src / "m"), "/fvdep/src/m", "/m", "/dev/m",
               "/usr/m"]
    env = dict(os.environ, FVDEP_CACHE=str(cache))
    rep = ran(sandbox(WRITE.format(targets=targets), "--src", str(src), env=env))
    for p in targets:
        need(failed(rep, "W:" + p), f"the step wrote {p}: {rep.get('W:' + p)}")
    for d in (home, cache, src):
        need(not (d / "m").exists(), f"a host file appeared: {d / 'm'}")


NETWORK = """import socket
for key, addr in (('L', ('127.0.0.1', {port})), ('P', ('1.1.1.1', 443))):
    s = socket.socket()
    s.settimeout(3)
    try:
        s.connect(addr)
        print(key, 'ok')
    except OSError as e:
        print(key, e.errno)
try:
    socket.getaddrinfo('example.com', 443)
    print('D ok')
except OSError as e:
    print('D', e.errno)
"""


@case("G1.network", "netns")
def network(tmp: Path) -> None:
    srv = socket.socket()
    srv.bind(("127.0.0.1", 0))
    srv.listen(4)
    srv.settimeout(0.2)
    seen: list[int] = []
    stop = threading.Event()

    def accept() -> None:
        while not stop.is_set():
            try:
                conn, _ = srv.accept()
                seen.append(1)
                conn.close()
            except OSError:
                pass

    t = threading.Thread(target=accept)
    t.start()
    try:
        rep = ran(sandbox(NETWORK.format(port=srv.getsockname()[1])))
    finally:
        stop.set()
        t.join()
        srv.close()
    for key in "LPD":
        need(failed(rep, key), f"network {key} reached: {rep.get(key)}")
    need(not seen, "the host listener accepted a connection from the step")


@case("G1.proc", "pidns")
def proc(tmp: Path) -> None:
    host = os.getpid()
    script = (f"import os\nprint('H', os.path.exists('/proc/{host}'))\n"
              "print('N', max(int(p) for p in os.listdir('/proc') if p.isdigit()))\n")
    rep = ran(sandbox(script))
    need(rep.get("H") == "False", f"the step sees the host process {host}")
    need(int(rep.get("N", "0")) < 100, f"the step sees pid {rep.get('N')}")


@case("G1.userns", "userns")
def userns(tmp: Path) -> None:
    script = ("import os\ntry:\n    os.unshare(os.CLONE_NEWUSER)\n    print('U ok')\n"
              "except OSError as e:\n    print('U', e.errno)\n")
    rep = ran(sandbox(script))
    # ENOSPC: bwrap's --disable-userns caps nested user namespaces (an AppArmor or capability
    # refusal reads EPERM/EACCES, so this pins the runner's own mechanism).
    need(rep.get("U") == "28", f"unshare(CLONE_NEWUSER) inside the step: {rep.get('U')}")


FDS = """import os
print('S', sorted(int(x) for x in os.listdir('/proc/self/fd')))
print('I', sorted(int(x) for x in os.listdir('/proc/1/fd')))
try:
    os.write(9, b'x')
    print('W ok')
except OSError as e:
    print('W', e.errno)
"""


@case("G1.fds", "closefrom")
def fds(tmp: Path) -> None:
    host = tmp / "host-file"
    fd = os.open(host, os.O_WRONLY | os.O_CREAT, 0o644)
    os.dup2(fd, 9)
    try:
        rep = ran(sandbox(FDS, pass_fds=(9,)))
    finally:
        os.close(9)
        os.close(fd)
    own = set(ast.literal_eval(rep.get("S", "[-1]")))
    init = set(ast.literal_eval(rep.get("I", "[-1]")))
    need(own <= {0, 1, 2, 3}, f"the child holds descriptors {sorted(own)}")
    need(not init & {3, 4, 9}, f"bwrap's pid 1 holds descriptors {sorted(init)}")
    need(failed(rep, "W"), "the step wrote through an inherited descriptor")
    need(host.stat().st_size == 0, "the host file changed")


HELPER = """import ctypes, os
pp = os.getppid()
try:
    fd = os.open(f'/proc/{pp}/fd/4', os.O_WRONLY)
    os.close(fd)
    print('F ok')
except OSError as e:
    print('F', e.errno)
try:
    with open(f'/proc/{pp}/mem', 'rb') as m:
        m.read(1)
    print('M ok')
except OSError as e:
    print('M', e.errno)
libc = ctypes.CDLL(None, use_errno=True)
print('P', 'ok' if libc.ptrace(16, pp, None, None) == 0 else ctypes.get_errno())
"""


@case("G1.helper", "nodump")
def helper(tmp: Path) -> None:
    rep = ran(sandbox(HELPER))
    need(failed(rep, "F"), "the child opened its helper's descriptor 4")
    need(failed(rep, "M"), "the child read its helper's memory")
    need(failed(rep, "P"), "the child attached to its helper")


@case("G1.env", "clearenv")
def env(tmp: Path) -> None:
    secret = "g1-secret-" + secrets.token_hex(8)
    script = ("import os\nprint('K', ','.join(sorted(os.environ)))\n"
              "print('D', os.environ.get('PWD'))\n"
              f"print('S', any({secret!r} in v for v in os.environ.values()))\n")
    rep = ran(sandbox(script, env=dict(os.environ, FVDEP_G1_SECRET=secret)))
    # bwrap sets PWD itself at `--chdir` (bubblewrap 0.11.1): the layout's cwd, no host value.
    need(rep.get("K") == "HOME,LC_ALL,PATH,PWD,TMPDIR", f"the step's environment: {rep.get('K')}")
    need(rep.get("D") == "/fvdep/src", f"PWD = {rep.get('D')}")
    need(rep.get("S") == "False", "the supervisor's secret reached the step")


@case("G1.grandchild", "killall")
def grandchild(tmp: Path) -> None:
    marker = "g1-detached-" + secrets.token_hex(8)
    script = ("import subprocess\n"
              "subprocess.Popen(['/bin/sh', '-c', 'trap \"\" TERM HUP; while :; do sleep 1; done', "
              f"{marker!r}], start_new_session=True)\nprint('G started')\n")
    # A short deadline: without the step's own PID namespace + kill-all the grandchild keeps the
    # pipes open, so the step ends at the deadline (+ the runner's drain bound), not at its exit.
    ran(sandbox(script, "--deadline", "5"))
    need(gone(marker, 5), f"a detached grandchild outlived its step: {holders(marker)}")


@case("G1.supervisor-kill", "pdeathsig")
def supervisor_kill(tmp: Path) -> None:
    marker = "g1-orphan-" + secrets.token_hex(8)
    argv = [str(DEV), "sandbox", "run", "--deadline", "120", "--", PY, "-I", "-c",
            f"import time; time.sleep(300)  # {marker}"]
    p = subprocess.Popen(argv, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        end = time.monotonic() + 30
        while time.monotonic() < end and not any(
                Path(f"/proc/{q}/cmdline").read_bytes().startswith(PY.encode())
                for q in holders(marker) if Path(f"/proc/{q}/cmdline").exists()):
            time.sleep(0.1)
        p.kill()
        p.wait()
        need(gone(marker, 10), f"a step process outlived its killed supervisor: {holders(marker)}")
    finally:
        if p.poll() is None:
            p.kill()


# 64 KiB files, below the per-file cap (1 MiB / 8): the tmpfs size stops them, not RLIMIT_FSIZE.
TMPFS = """import os
for key, d in (('W', '/fvdep/work/fill'), ('T', '/tmp/fill')):
    os.makedirs(d)
    err = 'ok'
    for i in range(64):
        try:
            with open(f'{d}/{i}', 'wb') as f:
                f.write(bytes(65536))
        except OSError as e:
            err = str(e.errno)
            break
    print(key, err)
"""


@case("G1.tmpfs", "size")
def tmpfs(tmp: Path) -> None:
    rep = ran(sandbox(TMPFS, "--work-bytes", "1048576", "--tmp-bytes", "1048576"))
    need(rep.get("W") == "28", f"/fvdep/work took 4 MiB: {rep.get('W')}")
    need(rep.get("T") == "28", f"/tmp took 4 MiB: {rep.get('T')}")


LIMITS = """for line in open('/proc/self/limits'):
    f = line.split()
    if line.startswith('Max core file size'):
        print('C', f[-3], f[-2])
    if line.startswith('Max file size'):
        print('F', f[-3], f[-2])
"""


@case("G1.core", "core-limit")
def core(tmp: Path) -> None:
    """The step's processes run under RLIMIT_CORE = 1 (the kernel then skips the host's
    `core_pattern` pipe: vflab's apport, as root) + RLIMIT_FSIZE = the per-file cap; read, never
    crashed (a mutant without the limit must not reach apport)."""
    rep = ran(sandbox(LIMITS))
    need(rep.get("C") == "1 1", f"RLIMIT_CORE inside the step: {rep.get('C')}")
    need(rep.get("F") == "134217728 134217728", f"RLIMIT_FSIZE inside the step: {rep.get('F')}")


@case("G4.file-cap", "fsize")
def file_cap(tmp: Path) -> None:
    """A1: a file written past the per-file cap ends its writer by SIGXFSZ (a signal death: the
    helper exits 128 + 25) at exactly the cap; a writer ignoring SIGXFSZ (python) gets EFBIG; a cap
    above --work-bytes / 8 is a usage error."""
    argv = [str(DEV), "sandbox", "run", "--file-bytes", "100000", "--", "/bin/sh", "-c",
            "exec head -c 300000 /dev/zero >/fvdep/work/out/big"]
    r = subprocess.run(argv, capture_output=True, text=True, timeout=180, check=False)
    lines = r.stdout.splitlines()
    need("outcome exited 153" in lines, f"head past the cap: {r.stdout[:300]}")
    need(any(s.startswith("file big 100000 ") for s in lines), f"the capped file: {r.stdout[:300]}")
    script = ("try:\n    open('/fvdep/work/big', 'wb').write(bytes(300000))\n    print('E ok')\n"
              "except OSError as e:\n    print('E', e.errno)\n")
    rep = ran(sandbox(script, "--file-bytes", "100000"))
    need(rep.get("E") == "27", f"python past the cap: {rep.get('E')}")
    bad = sandbox("print('ran')", "--work-bytes", "800000", "--file-bytes", "100001")
    need(bad.returncode == 2 and "outcome" not in bad.stdout,
         f"a cap above --work-bytes / 8 ran: exit {bad.returncode}")


WRAPPER = """#!/bin/sh
if [ "$1" = "--version" ]; then exec {real} "$@"; fi
prev=""
for a in "$@"; do
  case "$prev" in {src}) [ "$a" = {dest} ] && rm -rf -- "$prev" ;; esac
  prev="$a"
done
exec {real} "$@"
"""

# `lean` first on PATH for D2's preflight: its prefix = a fake sysroot (bin/lean + bin/leanexport).
FAKE_LEAN = """#!/bin/sh
[ "$1" = --print-prefix ] && echo '{prefix}' && exit 0
exit 1
"""


@case("G3.bind-removed", "setup")
def bind_removed(tmp: Path) -> None:
    """A bind source removed between plan + spawn (a PATH wrapper deletes it, then execs the real
    bwrap) → setup_failed, never a run: the run directory's source tree (also the cwd) + helper
    directory (bwrap's chdir or exec would fail without them anyway), and the toolchain's sysroot
    (a Python step never reads it: the bind alone notices; a fake prefix, the one path the wrapper
    may delete there, so a real toolchain is never touched)."""
    real = shutil.which("bwrap")
    need(real is not None, "bwrap is not on PATH")
    prefix = tmp / "sysroot"
    (prefix / "bin").mkdir(parents=True)
    for tool in ("lean", "leanexport"):
        (prefix / "bin" / tool).touch(mode=0o700)
    for dest, src in (("/fvdep/src", "/*"), ("/fvdep/step", "/*"),
                      ("/fvdep/sysroot", f"'{prefix}'")):
        wrap = tmp / ("bin" + dest.replace("/", "-"))
        wrap.mkdir()
        (wrap / "bwrap").write_text(WRAPPER.format(real=real, dest=dest, src=src))
        (wrap / "bwrap").chmod(stat.S_IRWXU)
        if dest == "/fvdep/sysroot":
            (wrap / "lean").write_text(FAKE_LEAN.format(prefix=prefix))
            (wrap / "lean").chmod(stat.S_IRWXU)
        env = dict(os.environ, PATH=f"{wrap}:{os.environ.get('PATH', '')}")
        r = sandbox("print('ran')", env=env)
        need(r.returncode == 0, f"{dest}: fvdep-dev exit {r.returncode}: {r.stderr.strip()[:300]}")
        lines = r.stdout.splitlines()
        need(any(s.startswith("outcome setup_failed: ") for s in lines),
             f"{dest} removed: {r.stdout[:300]}")
        need(not any(s.startswith("outcome exited") for s in lines),
             f"a step ran without {dest}")
    need(not prefix.exists(), "the wrapper left the fake sysroot in place")


def helper_alone(tmp: Path, script: str) -> subprocess.CompletedProcess[str]:
    """`script` (sh) in a fresh bwrap PID namespace beside a copy of the helper at
    /fvdep/step/fvdep-step: the helper is never PID 2 there, so a broken kill-all guard still
    reaches that namespace alone."""
    bwrap = shutil.which("bwrap")
    need(bwrap is not None, "bwrap is not on PATH")
    step = tmp / "step"
    step.mkdir()
    shutil.copy(DEV.parent / "fvdep-step", step / "fvdep-step")
    argv = [str(bwrap), "--unshare-all", "--unshare-user", "--die-with-parent", "--new-session",
            "--ro-bind", "/usr", "/usr", "--symlink", "usr/lib", "/lib", "--symlink", "usr/lib64",
            "/lib64", "--symlink", "usr/bin", "/bin", "--ro-bind", str(step), "/fvdep/step",
            "--tmpfs", "/fvdep/work", "--proc", "/proc", "--dev", "/dev", "--", "/bin/sh", "-c",
            script]
    return subprocess.run(argv, capture_output=True, text=True, timeout=60, check=False)


@case("G1.killall-guard", "pid2")
def killall_guard(tmp: Path) -> None:
    """kill-all refused unless the helper is PID 2: here PID 4 inside a fresh PID namespace (its
    sibling survives) + a host process in another session outside it (the canary) outlives the
    case."""
    script = ('sleep 30 & s=$!; /fvdep/step/fvdep-step -- /bin/true 2>&1; '
              'if kill -0 "$s" 2>/dev/null; then echo SURVIVED; fi; kill "$s"')
    canary = subprocess.Popen(["/usr/bin/sleep", "300"], start_new_session=True)
    try:
        r = helper_alone(tmp, script)
        need(canary.poll() is None, "a host process outside the step's PID namespace died")
        need("kill-all refused" in r.stdout,
             f"the helper's kill-all was not refused: {r.stdout[:300]}")
        need("SURVIVED" in r.stdout, "a sibling of the helper died")
    finally:
        canary.kill()
        canary.wait()


@case("R8.channel", "channel")
def channel(tmp: Path) -> None:
    """The helper frames onto descriptor 4 only when it inherited a pipe there: started without
    it (the Lean runtime then opens its own io_uring at 4) or with a regular file there, it warns
    + writes nothing; with a pipe the frame arrives."""
    script = ('/fvdep/step/fvdep-step -- /bin/true 2>&1 | grep -c "no descriptor 4"; '
              ': >/fvdep/work/f; /fvdep/step/fvdep-step -- /bin/true 4>/fvdep/work/f 2>&1 '
              '| grep -c "no descriptor 4"; wc -c </fvdep/work/f; '
              '/fvdep/step/fvdep-step -- /bin/true 4>&1 2>/dev/null | grep -ac fvdep/step/1')
    r = helper_alone(tmp, script)
    got = r.stdout.split()
    need(got[:1] == ["1"], f"started without descriptor 4: {r.stdout!r}")
    need(got[1:3] == ["1", "0"], f"a regular file at descriptor 4 was used: {r.stdout!r}")
    need(got[3:] == ["1"], f"no frame on an inherited pipe: {r.stdout!r} {r.stderr[:200]!r}")


@case("G2.link-plant", "noframe-links")
def link_plant(tmp: Path) -> None:
    """A step plants a link (to a file the step reads), a FIFO + a mode-000 directory under
    /fvdep/work/out beside a regular file: the regular file alone is framed (no link followed, no
    FIFO opened, the locked directory skipped), the step ends, the link's target is untouched."""
    src = tmp / "src"
    src.mkdir()
    secret = src / "secret"
    secret.write_bytes(b"u5-g2-secret")
    script = ("import os\n"
              "o = '/fvdep/work/out'\n"
              "os.makedirs(o + '/locked')\n"
              "open(o + '/locked/inner', 'w').write('x')\n"
              "os.chmod(o + '/locked', 0)\n"
              "os.symlink('/fvdep/src/secret', o + '/link')\n"
              "os.mkfifo(o + '/fifo')\n"
              "open(o + '/ok', 'w').write('ok')\n")
    r = sandbox(script, "--src", str(src))
    need(r.returncode == 0, f"fvdep-dev exit {r.returncode}: {r.stderr[:300]!r}")
    lines = r.stdout.splitlines()
    need("outcome exited 0" in lines and "frame complete" in lines, f"step: {r.stdout[:300]!r}")
    framed = [x.split()[1] for x in lines if x.startswith("file ")]
    need(framed == ["ok"], f"framed {framed!r}, expected only ok")
    need(secret.read_bytes() == b"u5-g2-secret", "the link's target changed")


@case("P1.library-first", "order")
def library_first(tmp: Path) -> None:
    """Phase 1's library roots check runs before any consumer compile (contract P1): an absent spec
    root = exit 2 even when the implementation itself does not compile (exit 1 otherwise)."""
    proj = tmp / "project"
    shutil.copytree(ROOT / "tests/sandbox/fixtures/honest", proj)
    pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    manifest = proj / "fvdep.toml"
    manifest.write_text(manifest.read_text().replace("0" * 40, pin))
    (proj / "SandboxTrial/Impl.lean").write_text("def broken := u5_first_missing\n")
    env = dict(os.environ, FVDEP_CACHE=str(tmp / "cache"))
    argv = [str(DEV), "phase", "check", str(proj), "base64.encode", "--library", str(ROOT),
            "--spec-module", "Fvdep.Base64.Encode.V1_0_0",
            "--spec", "Fvdep.Base64.Encode.V1_0_0.u5_absent"]
    r = subprocess.run(argv, capture_output=True, text=True, env=env, timeout=600, check=False)
    lines = r.stdout.splitlines()
    need(r.returncode == 2, f"exit {r.returncode}: {r.stdout[:400]!r}")
    need(any(x.startswith("infra io: ") and "u5_absent" in x for x in lines),
         f"no infra line naming the root: {r.stdout[:400]!r}")
    need(not any(x.startswith("phase1 failed") for x in lines),
         "the consumer's own failure outranked the absent library root")


@case("G4.print-flood", "retention")
def print_flood(tmp: Path) -> None:
    # 10^9 lines (2 GB) through a 1 KiB diagnostic cap (contract G4).
    script = "import sys\nfor _ in range(200):\n    sys.stdout.buffer.write(b'x\\n' * 5000000)\n"
    argv = [str(DEV), "sandbox", "run", "--diagnostic-bytes", "1024", "--", PY, "-I", "-c", script]
    with (tmp / "out").open("w") as out:
        p = subprocess.Popen(argv, stdout=out, stderr=subprocess.DEVNULL)
        _, status, usage = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
    text = (tmp / "out").read_text()
    need(p.returncode == 0, f"fvdep-dev exit {p.returncode}")
    need("stdout 2000000000 dropped 1999998976" in text.splitlines(), "stdout counts differ")
    need(usage.ru_maxrss < 400 * 1024, f"fvdep-dev peak RSS {usage.ru_maxrss} KiB")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case", default=os.environ.get("FVDEP_ISOLATION_CASE", ""),
                    help="id substring")
    args = ap.parse_args()
    if not DEV.exists():
        print(f"fvdep-dev is not built: {DEV}", file=sys.stderr)
        return 2
    base = ROOT / ".gate" / "isolation"
    base.mkdir(parents=True, exist_ok=True)
    chosen = [c for c in CASES if args.case in c[0]]
    bad = 0
    for cid, mech, f in chosen:
        tmp = Path(tempfile.mkdtemp(dir=base))
        start = time.monotonic()
        try:
            f(tmp)
            print(f"PASS {cid} [{mech}] {time.monotonic() - start:.1f}s", flush=True)
        except Exception as e:  # noqa: BLE001  # a crashed case reports like a failed one
            bad += 1
            print(f"FAIL {cid} [{mech}]: {type(e).__name__}: {e}", flush=True)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    print(f"SUMMARY {len(chosen)} cases; {len(chosen) - bad} passed; {bad} failed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
