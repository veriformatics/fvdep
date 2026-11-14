"""Invocation cases: docs/interface.md §§1–2; U1 foundation K2."""
import re

from harness import case, saved, unchanged


@case("invocation.version", "U1", "interface §1; U1 K2", "Version uses stdout alone and exactly one LF")
def version(ctx):
    result = ctx.call("--version").code(0)
    assert re.fullmatch(r"fvdep [^\s]+\n", result.stdout), result.stdout
    assert result.stderr == "", result.stderr


for suffix, args in [
    ("help", ("help",)), ("help-flag", ("--help",)),
    ("help-help", ("help", "help")), ("help-option", ("help", "--help")),
]:
    @case(f"invocation.{suffix}", "U1", "interface §1; U1 K2", f"{suffix} emits usage on stdout alone")
    def help_case(ctx, args=args):
        result = ctx.call(*args).code(0)
        assert result.stdout.strip() and "fvdep" in result.stdout.lower(), result.stdout
        assert result.stderr == "", result.stderr


for suffix, args in [
    ("empty", ()), ("unrecognized-command", ("not-a-command",)),
    ("unrecognized-option", ("--not-an-option",)),
    ("version-extra", ("--version", "extra")),
    ("help-extra", ("help", "help", "extra")),
    ("help-unrecognized", ("help", "not-a-command")),
    ("help-unrecognized-option", ("help", "--not-an-option")),
]:
    @case(f"invocation.{suffix}", "U1", "interface §1; U1 K2", f"{suffix} emits usage on stderr alone and exits 2")
    def usage_case(ctx, args=args):
        result = ctx.call(*args).code(2)
        assert result.stdout == "", result.stdout
        assert result.stderr.strip() and "fvdep" in result.stderr.lower(), result.stderr
        assert list(ctx.base.iterdir()) == [], "usage invocation had a filesystem effect"


for command in ("check", "status", "lock", "upgrade", "outdated", "build-lib"):
    args = (command, "base64.encode") if command in {"upgrade", "build-lib"} else (command,)

    @case(f"invocation.no-project.{command}", "U8", "interface §1", f"{command} without a project gives the exact recovery diagnostic")
    def no_project(ctx, args=args):
        result = ctx.call(*args).code(2)
        assert result.stdout == ""
        assert result.stderr == 'No fvdep.toml found. Run "fvdep init" in your project directory.\n', result.stderr


for command in ("init", "list", "show", "check", "status", "lock", "upgrade", "fetch", "outdated",
                "diff", "scan", "profile", "build-lib", "brief", "trust", "admit", "oracle", "index"):
    @case(f"invocation.command-help.{command}", "U8", "interface §1", f"{command} --help needs no project or library")
    def command_help(ctx, command=command):
        result = ctx.call(command, "--help").code(0)
        assert "fvdep" in result.stdout.lower() and command in result.stdout
        assert result.stderr == "", result.stderr
        assert list(ctx.base.iterdir()) == [], "help invocation had a filesystem effect"


@case("invocation.nearest-project", "U8", "interface §1", "Commands find the nearest ancestor manifest")
def nearest_project(ctx):
    project = ctx.differential()
    nested = project / "a/b/c"
    nested.mkdir(parents=True)
    before = saved(project)
    result = ctx.call("check", "--json", cwd=nested).code(0).document()
    assert [m["module"] for m in result["result"]["modules"]] == ["base64.encode"]
    unchanged(project, before)


@case("invocation.explicit-project", "U8", "interface §1", "--project overrides the working directory")
def explicit_project(ctx):
    project = ctx.differential()
    result = ctx.call("--project", str(project), "check", "--json").code(0).document()
    assert [m["module"] for m in result["result"]["modules"]] == ["base64.encode"]


@case("invocation.trust-offline", "U8", "interface §1; Decisions Self-verification scope", "trust reads no library and names the verification profile and residual trust")
def trust_offline(ctx):
    result = ctx.call("trust", env={"FVDEP_LIBRARY_URL": str(ctx.base / "absent")}).code(0)
    for text in ("Lean", "con-leche", "NanoDa", "propext", "Classical.choice", "Quot.sound"):
        assert text.lower() in result.stdout.lower(), (text, result.stdout)
    for term in ("compiler", "runtime", "parser", "elaborator", "export", "filesystem", "bwrap", "git", "HACL", "FFI", "interpreter", "shim", "binding"):
        assert term.lower() in result.stdout.lower(), (term, result.stdout)
    assert re.search(r"[0-9a-f]{64}", result.stdout), "trust omits profile digests"
