/* Project snapshot shim (docs/contracts/U5-sandbox.md S1; ledger residue `project-snapshot`): one
 * `openat` + `fstat` per call, errno answered at once (no retry, no policy). The walk, the caps +
 * every refusal stay in Lean (`FvdepIO.Snapshot`; decision `FvdepCore.Phase.snapDecide`).
 * Lean ABI: `b_lean_obj_arg` = borrowed. */
#ifndef FVDEP_SNAPSHOT_H
#define FVDEP_SNAPSHOT_H

#include <lean/lean.h>

/* S1: openat(dir, name, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_NOCTTY | O_CLOEXEC) + fstat →
 * `.ok #[fd, st_mode & S_IFMT, st_size]` | `.error errno`; a failed fstat closes the descriptor.
 * `name` = one path component, else EINVAL before any call: empty, `.`, `..`, a `/` anywhere or an
 * interior NUL (O_NOFOLLOW covers a name's last component alone, `..` leaves `dir`, an absolute
 * name ignores it, C would cut at the NUL). */
LEAN_EXPORT lean_obj_res fvdep_snapshot_open(uint32_t dir, b_lean_obj_arg name);

#endif
