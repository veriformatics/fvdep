"""Only the specified queue surface is pinned before the U13 state schema."""
from harness import case


@case("growth.queue-add-pinned", "U13", "interface §9", "The user queue persists an exact package version in its isolated growth state")
def queue_pinned(ctx):
    ctx.grow("queue", "add", "npm:semver@7.7.3").code(0)
    result = ctx.grow("queue", "list").code(0)
    assert "npm:semver@7.7.3" in result.stdout, result.stdout
    assert (ctx.base / "growth").is_dir()


@case("growth.queue-add-unpinned", "U13", "interface §9", "The user queue accepts a package without inventing an exact resolved version")
def queue_unpinned(ctx):
    ctx.grow("queue", "add", "npm:base64-js").code(0)
    result = ctx.grow("queue", "list").code(0)
    assert "npm:base64-js" in result.stdout, result.stdout


for name, args in [("no-command", ()), ("missing-target", ("queue", "add")),
                   ("bad-target", ("queue", "add", "no-ecosystem")),
                   ("extra-argument", ("queue", "list", "extra"))]:
    @case(f"growth.usage.{name}", "U13", "interface §§2/9", f"Growth invocation {name} is usage failure rather than an attempt or admission")
    def usage(ctx, args=args):
        result = ctx.grow(*args).code(2)
        assert result.stdout == "", result.stdout
        assert result.stderr.strip(), result.stderr
        assert "ATTEMPT " not in result.text
