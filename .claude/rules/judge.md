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
- v1's deadlines, W (`work`), `opaques`, `canaries` + `fingerprint` stay provisional until Q (U7-E) + C (U7-F); the freeze (V3) records at U7-F.
