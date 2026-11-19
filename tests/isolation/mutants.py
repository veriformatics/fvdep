#!/usr/bin/env python3
"""Credit for the isolation cases (MAIN's; contract docs/contracts/U5-sandbox.md G): each mutant =
exact replacements in the runner, shim or helper, each applied once; its cases run through
`tests/isolation/run.sh` (the helper built by name), a case counts as killed when it FAILs; files
restored + the real binaries rebuilt after each. The only sanctioned way to weaken the runner
(`.claude/rules/sandbox.md`): refuses outside a PID namespace of the job's own
(`tools/pidns-check.sh`), and no mutant runs a crash without `RLIMIT_CORE` = 1 (STUB drops the
file cap with the core limit: no `SIGXFSZ`, no core). Edits the tree in place ⇒ a vflab workspace
alone, from the repo root, with the fvapi session told first:
`FVDEP_VFLAB_MEMORY=6G tools/vflab-run bash -c 'python3 -I tests/isolation/mutants.py [KEY ...]'`
→ `.gate/mutants-isolation/<KEY>.log` + `results.tsv`, one `MUT` line each."""
import subprocess
import sys
from pathlib import Path

SPAWN = "c/fvdep_spawn.c"
STEP = "tool/FvdepIO/Step.lean"
RUNNER = "tool/FvdepIO/Sandbox.lean"
CORE = "tool/FvdepCore/Sandbox.lean"

STUB_ARGS = (
    "-- MUTANT STUB: every isolation flag dropped + a writable home bind.\n"
    "partial def stubArgs (home : String) : List String → List String\n"
    '  | "--unshare-all" :: r => stubArgs home r\n'
    '  | "--disable-userns" :: r => stubArgs home r\n'
    '  | "--die-with-parent" :: r => stubArgs home r\n'
    '  | "--clearenv" :: r => stubArgs home r\n'
    '  | "--size" :: _ :: r => stubArgs home r\n'
    '  | "--remount-ro" :: _ :: r => stubArgs home r\n'
    '  | "--" :: r => ["--bind", home, home, "--"] ++ r\n'
    "  | a :: r => a :: stubArgs home r\n"
    "  | [] => []\n\n")

# (key + label, edits (path, old, new), the cases run (a run.sh --case substring; "" = all), the
# cases it must fail, the build that must fail ("" = none)).
CORE_PHASE = "tool/FvdepCore/Phase.lean"

MUTANTS = [
    ("STUB every isolation mechanism off, steps still run",
     [(SPAWN, "        (e = closefrom(&fa, 5)) != 0) {", "        (e = 0) != 0) {"),
      (SPAWN, "    e = posix_spawn(&pid, cpath, &fa, &attr, cargv, envp);",
       "    (void)envp;\n"
       "    e = posix_spawn(&pid, cpath, &fa, &attr, cargv, environ);"),
      (STEP, "    match ← Spawn.nodump () with\n    | .error e =>\n"
       '      warn s!"prctl: {Spawn.errnoText e}"\n    | .ok _ =>\n      pure ()\n'
       "    let channel ← Spawn.channel 4\n    match ← Spawn.coreLimit 1 with\n"
       '    | .error e =>\n      warn s!"setrlimit: {Spawn.errnoText e}"\n    | .ok _ =>\n'
       "      pure ()\n    if let some n := r.fileBytes then\n"
       "      match ← Spawn.fileLimit n.toUInt64 with\n      | .error e =>\n"
       '        warn s!"setrlimit RLIMIT_FSIZE: {Spawn.errnoText e}"\n      | .ok _ =>\n'
       "        pure ()\n",
       "    let channel : Except Nat Unit := .ok ()\n"),
      (STEP, "    -- `kill(-1)` answers `ESRCH` (3) when no other process is left: the usual "
       "end of a step.\n    match ← Spawn.killAll () with\n    | .error 3 | .ok _ =>\n"
       "      pure ()\n"
       '    | .error e =>\n      warn s!"kill-all refused: {Spawn.errnoText e}"\n', ""),
      (RUNNER, "/-- One step: `bwrap` (an absolute path, T1's) runs `bwrapArgs spec`. -/\ndef run",
       STUB_ARGS + "/-- One step: `bwrap` (an absolute path, T1's) runs `bwrapArgs spec`. -/\n"
       "def run"),
      (RUNNER, '  match ← FvdepIO.Spawn.bwrap bwrap ("bwrap" :: bwrapArgs spec).toArray with',
       '  let home := (← IO.getEnv "HOME").getD "/"\n'
       '  match ← FvdepIO.Spawn.bwrap bwrap ("bwrap" :: stubArgs home (bwrapArgs spec)).toArray '
       "with")],
     "", ["G1.write.host", "G1.network", "G1.proc", "G1.userns", "G1.fds", "G1.helper", "G1.env",
          "G1.grandchild", "G1.supervisor-kill", "G1.tmpfs", "G1.core", "G4.file-cap"], ""),
    ("GUARD kill-all admitted for PID 4 in place of PID 2",
     [(SPAWN, "    if (getpid() != 2) {", "    if (getpid() != 4) {")],
     "G1.killall-guard", ["G1.killall-guard"], ""),
    ("CHANNEL descriptor 4 taken unchecked",
     [(SPAWN, "    if ((flags & FD_CLOEXEC) != 0 || fstat((int)fd, &st) != 0 || "
       "!S_ISFIFO(st.st_mode)) {", "    if (fstat((int)fd, &st) != 0) {")],
     "R8.channel", ["R8.channel"], ""),
    ("SETUP a setup failure read as the deadline kill",
     [(RUNNER, "        { outcome := classify (statusLines p.status) killed (firstLine p.err.head)",
       "        { outcome := classify (statusLines p.status) (killed || !p.err.head.isEmpty)\n"
       "              (firstLine p.err.head)")],
     "G3.bind-removed", ["G3.bind-removed"], ""),
    ("ROBIND a missing bind source skipped (`--ro-bind-try`)",
     [(CORE, '  | .roBind s d => ["--ro-bind", s, d]',
       '  | .roBind s d => ["--ro-bind-try", s, d]')],
     "G3.bind-removed", ["G3.bind-removed"], "FvdepAudit.Sandbox.Proof"),
    ("HOARD every stdout chunk kept",
     [(RUNNER, "  overflow : Bool := false\n",
       "  overflow : Bool := false\n  hoard : Array ByteArray := #[]\n"),
      (RUNNER, "  | 0 => { p with out := p.out.push keep chunk }\n",
       "  | 0 => { p with out := p.out.push keep chunk, hoard := p.hoard.push chunk }\n")],
     "G4.print-flood", ["G4.print-flood"], ""),
    ("G2 the helper follows links (lstat → stat, the no-follow open dropped)",
     [(STEP, "      match ← e.path.symlinkMetadata.toBaseIO with", "      match ← e.path.metadata.toBaseIO with"),
      (SPAWN, "    int fd = open(cpath, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC);",
       "    int fd = open(cpath, O_RDONLY | O_NONBLOCK | O_CLOEXEC);")],
     "G2.", ["G2.link-plant"], ""),
    ("P1 the library roots check after the window (consumer code first)",
     [(CORE_PHASE, "  (if n == 1 then [Step.libraryRoots] else []) ++ steps order",
       "  steps order ++ (if n == 1 then [Step.libraryRoots] else [])")],
     "P1.", ["P1.library-first"], ""),
]


def run(argv: list[str], cwd: str = ".") -> subprocess.CompletedProcess[str]:
    return subprocess.run(argv, capture_output=True, text=True, cwd=cwd, check=False)


def main() -> int:
    if run(["bash", "tools/pidns-check.sh"]).returncode != 0:
        print("mutants: not inside a PID namespace of this job's own: nothing ran", file=sys.stderr)
        return 2
    only = sys.argv[1:]
    out = Path(".gate/mutants-isolation")
    out.mkdir(parents=True, exist_ok=True)
    summary = []
    for label, edits, cases, must_fail, must_break in MUTANTS:
        key = label.split()[0]
        if only and key not in only:
            continue
        files = sorted({path for path, _, _ in edits})
        saved = {path: Path(path).read_text() for path in files}
        status, fails, broke = "ran", [], ""
        try:
            for path, old, new in edits:
                text = Path(path).read_text()
                if text.count(old) != 1:
                    status = f"noapply:{path}:{text.count(old)}"
                    break
                Path(path).write_text(text.replace(old, new))
            if status == "ran":
                narrow = ["--case", cases] if cases else []
                suite = run(["bash", "tests/isolation/run.sh", *narrow])
                log = suite.stdout + suite.stderr
                fails = [ln.split()[1] for ln in suite.stdout.splitlines()
                         if ln.startswith("FAIL ")]
                if must_break:
                    build = run(["lake", "build", must_break], cwd="tool")
                    log += build.stdout + build.stderr
                    errs = [ln for ln in build.stdout.splitlines() if "error" in ln]
                    broke = errs[0][:200] if build.returncode != 0 and errs else "built"
                (out / f"{key}.log").write_text(log)
        finally:
            for path, text in saved.items():
                Path(path).write_text(text)
        killed = [c for c in must_fail if c in fails]
        missed = [c for c in must_fail if c not in fails]
        verdict = "ok" if status == "ran" and not missed and broke != "built" else "MISSED"
        summary.append(f"{key}\t{status}\t{','.join(fails)}\t{','.join(missed)}\t{broke}")
        proof = f" proof: {broke}" if must_break else ""
        print(f"MUT {key} {verdict} {status} killed={len(killed)}/{len(must_fail)} "
              f"missed={','.join(missed) or '-'}{proof}", flush=True)
    rebuilt = run(["lake", "build", "«fvdep-dev»", "«fvdep-step»"], cwd="tool")
    print(f"MUT rebuild rc {rebuilt.returncode}", flush=True)
    (out / "results.tsv").write_text("\n".join(summary) + "\n")
    return 0 if rebuilt.returncode == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
