---
paths:
  - "tool/FvdepCore/Judge/**"
  - "tool/FvdepAudit/Judge/**"
  - "tool/FvdepDev/Judge.lean"
  - "docs/contracts/U7-judge.md"
  - "docs/verification-profile.json"
---

# Judge + verification profile (contract `docs/contracts/U7-judge.md`)

- K2's kernel texts (`leanAccept`, `leanReject`, `quotReject`, `conAccept*`, `conReject`, `conDecline`, `nanodaReject`) = reviewed data against the measured outputs of the pinned binaries (leanchecker prints its accept line before the quotient post-check + a multi-line rejection; con-leche's decline carries ` t=<s>` run time ⇒ `declineDetail` cuts it: two equal declines compare equal); a kernel or toolchain bump re-measures each + its `lake test` case.
- `docs/verification-profile.json` = `v1.text` exactly (`lake test`, case `judge V2`); after a `v1` change regenerate: `tools/vflab-run bash -c 'cd tool && lake build -q «fvdep-dev» >/dev/null && .lake/build/bin/fvdep-dev judge profile' > docs/verification-profile.json`. v1's `implementationFreeze` = `docs/profile-freeze.txt`'s digest (same case): a U6 re-freeze updates both.
- v1's pins (the three kernel binaries' SHA-256 + T1's `fingerprint`) = the release asset's bytes (GitHub's recorded digest of `lean-<v>-linux.tar.zst` checked against the download, its binaries hashed, the fingerprint = `fvdep-dev cache fingerprint` on an install of it); `lake test`'s `judge K4` re-checks the installed toolchain on every gate host (vflab, CI) ⇒ a toolchain bump re-pins all four in the same commit. v1's deadlines + W (`work`) = Q1's (contract Q1: the launch cases' maxima × 10, deadlines floored at 60 s; re-measure after a kernel, toolchain or launch-case change: `FVDEP_JUDGE_KEEP=<dir> bash tests/judge/run.sh` ×3 alone, then the max `time kernel <k>` + `judge work` lines of its `E.*` logs); `opaques` + `canaries` stay provisional until C (U7-F); the freeze (V3) records at U7-F.
- Kernel steps run through `FvdepIO.Judge.run` (K4's `pinCheck` before any step, e2 staged + re-hashed, each kernel alone, all three run); D3's stub kernels = `fvdep-dev judge kernels … --kernel-binary <k>=<script>` (a `#!/bin/sh` script inside the step: `/usr` is bound; a file it writes under `/fvdep/work/out` = infrastructure).
- Stage `judge-suite` (`tests/judge/run.sh`, contract U7 E + R): the 10 launch cases PROVEN (D1) + R's regressions — source-level proofs in `tests/judge/r/` (a fresh project each, D1) + byte edits of `E.fn.encode`'s kept exports (`tests/judge/edit.py`, D2 `fvdep-dev judge run`: always SIMULATION); a new attack class → one case naming its stage + the line it prints.
