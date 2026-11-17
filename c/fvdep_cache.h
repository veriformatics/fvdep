/* Build cache shim (docs/contracts/U5-sandbox.md K4, K5; ledger residue `cache-fs`): one libc call
 * per export, errno answered at once (no retry, no policy): results are `Except Nat Unit`
 * (`.error errno` | `.ok ()`); a string with an interior NUL (which C would cut there) → EINVAL.
 * Locks (flock), publication, pins, eviction + validation stay in Lean (`FvdepIO.Cache`).
 * Lean ABI: `b_lean_obj_arg` = borrowed. */
#ifndef FVDEP_CACHE_H
#define FVDEP_CACHE_H

#include <lean/lean.h>

/* K4: link(src, dst) — a view's hard link to an entry's artifact (a link at src is linked itself,
 * never followed). */
LEAN_EXPORT lean_obj_res fvdep_cache_link(b_lean_obj_arg src, b_lean_obj_arg dst);
/* K5: utimensat(AT_FDCWD, path, NULL, AT_SYMLINK_NOFOLLOW) — the entry's `used` stamp set to now
 * (explicit: atime is unreliable on `noatime` mounts; a link at path is stamped itself). */
LEAN_EXPORT lean_obj_res fvdep_cache_touch(b_lean_obj_arg path);

#endif
