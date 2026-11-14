"""Adversarial consumer fixtures; each reason comes from Conformance method."""
import os
import random
import re
import socket
import stat
import threading

from harness import SEED, case, checked_modules, one_module, proof_entry, receipt_valid, saved, unchanged


for fixture in ("honest-fn", "renamed-multimodule"):
    @case(f"conformance.{fixture}", "U8", "Decisions Conformance method; library Operations", f"{fixture} proves the trusted equality over its declared closure")
    def honest(ctx, fixture=fixture):
        project = ctx.project(fixture)
        before = saved(project)
        module = one_module(ctx.call("check", "--json", cwd=project), 0)
        assert module["verdict"] == "proven" and module["policy_met"] is True, module
        assert module["evidence"] == "proof" and module["lock"] is None
        receipt_valid(module["receipt"], evidence="proof")
        unchanged(project, before)


@case("conformance.honest-launch", "U8", "Decisions Launch set; library Operations", "All six launch operations accept honest aliases and independent proof modules")
def honest_launch(ctx):
    project = ctx.project("honest-launch")
    modules = checked_modules(ctx.call("check", "--json", cwd=project), 0)
    assert {m["module"] for m in modules} == {"base64.encode", "base64.decode", "base64.encode_url", "base64.decode_url", "semver.parse", "semver.compare"}
    assert all(m["verdict"] == "proven" and m["policy_met"] for m in modules)


@case("conformance.honest-abi", "U8", "Decisions C-library delivery; library C ABI shapes", "ABI encoder and decoder proofs use the exact lifted statements")
def honest_abi(ctx):
    project = ctx.project("honest-abi")
    modules = checked_modules(ctx.call("check", "--json", cwd=project), 0)
    assert len(modules) == 2
    assert all(m["verdict"] == "proven" and m["receipt"]["request"]["shape"] == "abi" for m in modules)


for fixture, codes, detail in [
    ("forged-kernel", {"kernel_reject", "graph_mismatch"}, None),
    ("sorry", {"axiom"}, "sorryAx"),
    ("custom-axiom", {"axiom"}, "Proof.assumption"),
    ("native-decide", {"axiom"}, None),
    ("wrong-statement", {"statement_mismatch"}, None),
    ("macro-statement", {"statement_mismatch", "graph_mismatch"}, None),
    ("wrong-implementation", {"build_failed"}, "Proof.lean"),
    ("tampered-vendor", {"build_failed", "statement_mismatch", "graph_mismatch"}, None),
]:
    @case(f"conformance.reject.{fixture}", "U8", "Decisions Conformance method; Verification profile; interface §§4/6", f"{fixture} cannot supply proof evidence for the trusted challenge")
    def reject(ctx, fixture=fixture, codes=codes, detail=detail):
        project = ctx.project(fixture)
        before = saved(project)
        result = ctx.call("check", "--json", cwd=project)
        module = one_module(result, 1)
        assert module["verdict"] == "not_proven" and module["policy_met"] is False, module
        reasons = module["reasons"]
        assert any(reason["code"] in codes for reason in reasons), reasons
        if detail:
            assert detail in " ".join(reason["detail"] for reason in reasons), reasons
        unchanged(project, before)


for fixture, needle in [
    ("implemented-by", "implemented_by"), ("extern", "extern"), ("run-cmd", "run_cmd"),
    ("initialize", "initialize"), ("unsafe", "unsafe"), ("partial", "partial"),
    ("opaque", "opaque"), ("metaprogram", "macro"), ("skip-kernel-option", "skipKernelTC"),
]:
    @case(f"profile.reject.{fixture}", "U8", "Decisions Conformance method (implementation profile)", f"The positive allowlist refuses {needle} and names its original source location")
    def profile_refusal(ctx, fixture=fixture, needle=needle):
        project = ctx.project(fixture)
        before = saved(project)
        module = one_module(ctx.call("check", "--json", cwd=project), 1)
        assert module["verdict"] == "not_proven", module
        reasons = module["reasons"]
        assert any(r["code"] == "profile_construct" for r in reasons), reasons
        diagnostic = " ".join(r["detail"] for r in reasons)
        assert needle in diagnostic and re.search(r"Impl\.lean:\d+", diagnostic), diagnostic
        unchanged(project, before)
        assert not (project / "rewritten.c").exists(), "implementation initializer executed"


for fixture, module_name in [("import-lean", "Lean"), ("import-lake", "Lake")]:
    @case(f"profile.reject.{fixture}", "U8", "Decisions Conformance method (imports)", f"Implementation imports cannot include {module_name}")
    def import_refusal(ctx, fixture=fixture, module_name=module_name):
        project = ctx.project(fixture)
        module = one_module(ctx.call("check", "--json", cwd=project), 1)
        assert module["verdict"] == "not_proven"
        assert any(r["code"] == "import_not_allowed" and module_name in r["detail"] for r in module["reasons"])


@case("profile.reject.reserved-module", "U8", "Decisions Conformance method; library Naming", "An implementation cannot shadow the trusted spec module")
def reserved_module(ctx):
    project = ctx.project("reserved-module")
    module = one_module(ctx.call("check", "--json", cwd=project), 1)
    assert module["verdict"] == "not_proven"
    assert any(r["code"] == "reserved_module" for r in module["reasons"])


@case("profile.reserved-name-boundary", "U8", "library Naming (LEAD-DIRECTIVES D4a)", "Reserved roots are exact Init/Std/Lean/Lake or any first component starting Fvdep", "property")
def reserved_name_boundary(ctx):
    rng = random.Random(SEED ^ 8)
    names = ["Init.X", "Std.X", "Lean.X", "Lake.X", "Fvdep", "FvdepCore.X", "FvdepIO.X", "FvdepX"]
    names.extend(["Acme.Init", "Acme.FvdepCore"])
    names.extend(f"Fvdep{rng.randrange(100, 1000)}.X" for _ in range(3))
    names.extend(root + "More" + str(rng.randrange(100, 1000)) for root in ("Init", "Std", "Lean", "Lake"))
    spec = "Fvdep.Base64.Encode.V1_0_0.encode"
    for name in names:
        project = ctx.manifest({"base64.encode": proof_entry(impl=f"{name}.encode", impl_modules=[name])})
        source = project / (name.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(f"import Fvdep.Base64.Encode.V1_0_0\nnamespace {name}\ndef encode : List UInt8 → List Char := {spec}\nend {name}\n")
        (project / "Proof.lean").write_text(f"import {name}\nnamespace Proof\ntheorem encode_eq : @{name}.encode = @{spec} := rfl\nend Proof\n")
        first = name.split(".", 1)[0]
        reserved = first in {"Init", "Std", "Lean", "Lake"} or first.startswith("Fvdep")
        result = ctx.call("check", "--json", cwd=project)
        if reserved:
            assert result.returncode in {1, 2}, (name, result.text)
            if result.returncode == 1:
                module = one_module(result)
                assert module["verdict"] == "not_proven"
                assert any(reason["code"] == "reserved_module" for reason in module["reasons"]), (name, module)
            else:
                error = result.document()["error"]
                assert error["code"] in {"reserved_module", "schema"} and name in error["detail"], (name, error)
        else:
            assert one_module(result, 0)["verdict"] == "proven", name


@case("profile.comments-not-constructs", "U8", "Decisions Conformance method (syntax kinds)", "Forbidden words inside comments do not become forbidden syntax constructs")
def comments_not_constructs(ctx):
    project = ctx.project()
    path = project / "Impl.lean"
    path.write_text(path.read_text() + "\n-- unsafe partial opaque extern run_cmd initialize implemented_by macro\n")
    module = one_module(ctx.call("check", "--json", cwd=project), 0)
    assert module["verdict"] == "proven", module


@case("profile.walks-whole-tree", "U8", "Decisions Conformance method (whole tree)", "A forbidden construct in an unused implementation declaration is refused")
def whole_tree(ctx):
    project = ctx.project()
    path = project / "Impl.lean"
    path.write_text(path.read_text() + "\nnamespace Hidden\nunsafe def neverCalled : Nat := 0\nend Hidden\n")
    module = one_module(ctx.call("check", "--json", cwd=project), 1)
    assert any(r["code"] == "profile_construct" for r in module["reasons"]), module


@case("sandbox.consumer-lakefile-ignored", "U8", "Decisions Conformance method (fvdep-written build config); interface §1", "Consumer build hooks never run during a conformance check")
def consumer_lakefile(ctx):
    project = ctx.project("consumer-build-hook")
    sentinel = ctx.base / "outside-canary"
    assert not sentinel.exists()
    one_module(ctx.call("check", "--json", cwd=project), 0)
    assert not sentinel.exists(), "the consumer's lakefile ran"


@case("sandbox.proof-write-confined", "U8", "Decisions Conformance method (sandbox + supervisor isolation)", "Arbitrary proof build code cannot change an existing file outside the sandbox")
def proof_write(ctx):
    project = ctx.project("proof-write-outside")
    sentinel = ctx.base / "outside-canary"
    sentinel.write_bytes(b"outside: unchanged\0\xff")
    expected = sentinel.read_bytes()
    result = ctx.call("check", "--json", cwd=project)
    # Proof build IO is legal; the confinement, not a forced proof verdict, is the predicate.
    assert result.returncode in {0, 1}, result.text
    assert sentinel.read_bytes() == expected, "proof build escaped the sandbox"


@case("sandbox.proof-network-confined", "U8", "Decisions Conformance method (no network)", "Proof build code cannot reach a listening host socket")
def proof_network(ctx):
    project = ctx.project("proof-network")
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        listener.settimeout(0.2)
        port = listener.getsockname()[1]
        # Positive control: the endpoint really accepts a host connection.
        with socket.create_connection(("127.0.0.1", port), timeout=1) as control:
            control.sendall(b"control")
        connection, _ = listener.accept()
        with connection:
            assert connection.recv(32) == b"control"
        path = project / "Proof.lean"
        path.write_text(path.read_text().replace("@PORT@", str(port)))
        observed = []
        stop = threading.Event()

        def receive():
            while not stop.is_set():
                try:
                    connection, _ = listener.accept()
                except TimeoutError:
                    continue
                with connection:
                    observed.append(True)

        thread = threading.Thread(target=receive, daemon=True)
        thread.start()
        try:
            result = ctx.call("check", "--json", cwd=project)
            assert result.returncode in {0, 1}, result.text
        finally:
            stop.set()
            thread.join(timeout=2)
        assert not observed, "proof code reached the host network"


@case("sandbox.proof-link-plant", "U8", "Decisions Conformance method (link plant acceptance)", "A symlink planted by proof build code cannot become a trusted supervisor output")
def proof_link(ctx):
    project = ctx.project("proof-symlink")
    sentinel = ctx.base / "outside-canary"
    sentinel.write_text("outside: unchanged")
    before = saved(project)
    module = one_module(ctx.call("check", "--json", cwd=project), 1)
    assert module["verdict"] == "not_proven", module
    assert sentinel.read_text() == "outside: unchanged"
    unchanged(project, before)


@case("sandbox.snapshot-link-refused", "U8", "Decisions Conformance method (snapshots refuse links)", "A snapshot refuses a consumer symlink without following or modifying its target")
def snapshot_link(ctx):
    project = ctx.project()
    sentinel = ctx.base / "outside-canary"
    sentinel.write_text("outside")
    (project / "plant").symlink_to(sentinel)
    before = saved(project)
    result = ctx.call("check", "--json", cwd=project)
    assert result.returncode in {1, 2}, result.text
    assert re.search(r"link|symlink", result.text, re.IGNORECASE), result.text
    assert sentinel.read_text() == "outside"
    unchanged(project, before)


@case("sandbox.snapshot-fifo-refused", "U8", "Decisions Conformance method (snapshots refuse special files)", "A snapshot refuses a FIFO promptly instead of blocking while reading it")
def snapshot_fifo(ctx):
    project = ctx.project()
    fifo = project / "plant-fifo"
    os.mkfifo(fifo)
    assert stat.S_ISFIFO(fifo.stat().st_mode)
    before = saved(project)
    result = ctx.call("check", "--json", cwd=project, timeout=15)
    assert result.returncode in {1, 2}, result.text
    assert re.search(r"special|fifo|regular", result.text, re.IGNORECASE), result.text
    unchanged(project, before)


@case("conformance.no-differential-fallback", "U8", "interface §5; Decisions Proof policy", "Development policy never turns a failed proof into matching test evidence")
def no_fallback(ctx):
    project = ctx.project("sorry", policy="development")
    module = one_module(ctx.call("check", "--json", cwd=project), 1)
    assert module["evidence"] == "proof" and module["verdict"] == "not_proven"
    assert module["policy_met"] is False


@case("conformance.text-block", "U8", "interface §4; Decisions Readings", "A proven text verdict states the trusted base and lifecycle snapshot")
def text_block(ctx):
    project = ctx.project()
    _, pin = ctx.library()
    result = ctx.call("check", cwd=project).code(0)
    assert result.stdout.splitlines()[0] == "PROVEN base64.encode@1.0.0 Impl.encode"
    assert "Trusted base: " in result.stdout
    assert f"Status as of library commit {pin} (never fetched)" in result.stdout
    assert "DELIVERED" not in result.stdout, "check is not the status command"
