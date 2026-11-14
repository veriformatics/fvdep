"""D1: output-write failure is exit 2, with a diagnostic if stderr accepts it."""
import errno
import os
import subprocess

from harness import case


def full_sink():
    file = open("/dev/full", "wb", buffering=0)
    try:
        os.write(file.fileno(), b"control")
    except OSError as exc:
        if exc.errno != errno.ENOSPC:
            file.close()
            raise AssertionError(f"unexpected output-error control: {exc}") from exc
    else:
        file.close()
        raise AssertionError("the output-error positive control unexpectedly accepted bytes")
    return file


for name, argv in [("version", ["--version"]), ("help", ["--help"])]:
    @case(f"invocation.output-io.{name}", "U1", "interface §2 (LEAD-DIRECTIVES D1)", f"A failed {name} stdout write exits 2 and diagnoses the failed output")
    def stdout_failure(ctx, argv=argv):
        with full_sink() as sink:
            result = subprocess.run([str(ctx.binary), *argv], cwd=ctx.base, env=ctx.env,
                                    stdout=sink, stderr=subprocess.PIPE, text=True, timeout=15, check=False)
        assert result.returncode == 2, (result.returncode, result.stderr)
        assert result.stderr.startswith("Could not write the output: "), result.stderr
        assert result.stderr.rstrip().endswith("."), result.stderr
        assert list(ctx.base.iterdir()) == [], "output failure changed the filesystem"


def broken_sink():
    reader, writer = os.pipe()
    os.close(reader)
    try:
        os.write(writer, b"control")
    except BrokenPipeError:
        return writer
    except Exception:
        os.close(writer)
        raise
    os.close(writer)
    raise AssertionError("the broken-pipe positive control accepted bytes")


for name, argv in [("version", ["--version"]), ("help", ["--help"])]:
    @case(f"invocation.broken-pipe.{name}", "U1", "interface §2 (LEAD-DIRECTIVES D2)", f"A broken {name} stdout pipe exits 2 without a stderr message")
    def stdout_broken_pipe(ctx, argv=argv):
        writer = broken_sink()
        try:
            result = subprocess.run([str(ctx.binary), *argv], cwd=ctx.base, env=ctx.env,
                                    stdout=writer, stderr=subprocess.PIPE, text=True, timeout=15, check=False)
        finally:
            os.close(writer)
        assert result.returncode == 2 and result.stderr == "", (result.returncode, result.stderr)
        assert list(ctx.base.iterdir()) == []


@case("invocation.broken-pipe.stderr", "U1", "interface §2 (LEAD-DIRECTIVES D2)", "A broken usage stderr pipe exits 2 and keeps stdout empty")
def stderr_broken_pipe(ctx):
    writer = broken_sink()
    try:
        result = subprocess.run([str(ctx.binary)], cwd=ctx.base, env=ctx.env,
                                stdout=subprocess.PIPE, stderr=writer, text=True, timeout=15, check=False)
    finally:
        os.close(writer)
    assert result.returncode == 2 and result.stdout == "", (result.returncode, result.stdout)


@case("invocation.output-io.stderr", "U1", "interface §2 (LEAD-DIRECTIVES D1)", "A failed usage stderr write stays exit 2 and never spills usage onto stdout")
def stderr_failure(ctx):
    with full_sink() as sink:
        result = subprocess.run([str(ctx.binary)], cwd=ctx.base, env=ctx.env, stdout=subprocess.PIPE,
                                stderr=sink, text=True, timeout=15, check=False)
    assert result.returncode == 2 and result.stdout == "", (result.returncode, result.stdout)
