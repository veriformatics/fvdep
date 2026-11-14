#!/usr/bin/env python3
"""Growth-agent stand-in. Set FVDEP_AGENT to `python3 -I <this-file>`.

Modes are fixture-owned, not a product API. Successful mode makes a draft only;
no agent output is an admission verdict. U13 supplies its staging/record schema.
"""
import json
import os
import signal
import sys
import time
from pathlib import Path


def main():
    mode = os.environ.get("FVDEP_STUB_MODE", "draft")
    if mode == "login-unavailable":
        print("Subscription login unavailable", file=sys.stderr)
        return 23
    if mode == "crash":
        os.kill(os.getpid(), signal.SIGKILL)
    if mode == "hang":
        while True:
            time.sleep(60)
    if mode == "refuse":
        print("The supplied inputs do not justify a contract.")
        return 0
    message = sys.stdin.buffer.read()
    record = {"argv": sys.argv[1:], "input_bytes": len(message), "mode": mode}
    Path("agent-stub.json").write_text(json.dumps(record, sort_keys=True) + "\n")
    if mode == "escape":
        outside = os.environ.get("FVDEP_STUB_OUTSIDE")
        if outside:
            try:
                Path(outside).write_text("escaped")
            except OSError:
                pass
    print("Draft recorded. Admission must judge it independently.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
