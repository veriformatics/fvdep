---
paths:
  - "tool/FvdepIO/Library.lean"
  - "tool/FvdepIO/Git.lean"
  - "tool/FvdepIO/Project.lean"
  - "tool/FvdepCore/Library.lean"
  - "tool/FvdepDev/Library.lean"
---

# Library snapshots (contract `docs/contracts/U5b-oracle.md` P + L)

- git argv = separate elements (each `-c` value its own; the root = the last element of each recursive `ls-tree`); a git call other than the fetch + the init never carries a bare `fetch` or `init` element: tester-7's `PATH` shims (`tests/oracle/`, merged at U5b-O) match on them + count the calls.
- git's environment = exactly L3's list (`gitEnv`). New git behaviour or a git upgrade → `tools/vflab-run bash tools/git-probe.sh` (the exact L3 argv + environment per failure class: exit, objects received, stderr) first, then extend `transportLine` with the measured line + its `lake test` sample (`LibraryR.transportLines`); server text (`remote:`, `remote error:`) never counts.
- The group kill (`FvdepIO.Git.killGroup`) happens before the reap alone (an unreaped leader holds its group id); the normal path reaps without a kill.
- Store writes happen under the store lock; `removeAll` never follows a link; every refusal text comes from `FvdepCore.Library` (tested presentation).
