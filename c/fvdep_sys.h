/* Persistence shim (docs/contracts/U3-codecs.md F1): each `fvdep_sys_*` syscall export issues
 * exactly one libc call and answers `Except Nat Nat` (`.error errno` | `.ok value`; `read`:
 * `Except Nat ByteArray`) as a Lean IO result; the writer guard (mutex + closed flag + finalizer
 * close-if-open) owns one create-owned descriptor. Lean ABI: `b_lean_obj_arg` = borrowed. */
#ifndef FVDEP_SYS_H
#define FVDEP_SYS_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* open(path, O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW, mode) */
LEAN_EXPORT lean_obj_res fvdep_sys_open_file(b_lean_obj_arg path, uint32_t mode);
/* open(path, O_RDONLY|O_DIRECTORY|O_CLOEXEC) */
LEAN_EXPORT lean_obj_res fvdep_sys_open_dir(b_lean_obj_arg path);
/* open(path, O_RDONLY|O_CLOEXEC) */
LEAN_EXPORT lean_obj_res fvdep_sys_open_read(b_lean_obj_arg path);
/* open(path, O_RDWR|O_CREAT|O_CLOEXEC|O_NOFOLLOW, 0644) */
LEAN_EXPORT lean_obj_res fvdep_sys_open_lock(b_lean_obj_arg path);
/* write(fd, bytes + offset, count); offset + count beyond the array → .error EINVAL */
LEAN_EXPORT lean_obj_res fvdep_sys_write(uint32_t fd, b_lean_obj_arg bytes, size_t offset,
                                         size_t count);
/* read(fd, buf, count) → the bytes read (a fresh ByteArray) */
LEAN_EXPORT lean_obj_res fvdep_sys_read(uint32_t fd, size_t count);
/* fsync(fd) */
LEAN_EXPORT lean_obj_res fvdep_sys_sync(uint32_t fd);
/* close(fd) */
LEAN_EXPORT lean_obj_res fvdep_sys_close(uint32_t fd);
/* rename(source, target) */
LEAN_EXPORT lean_obj_res fvdep_sys_rename(b_lean_obj_arg source, b_lean_obj_arg target);
/* unlink(path) */
LEAN_EXPORT lean_obj_res fvdep_sys_unlink(b_lean_obj_arg path);
/* flock(fd, LOCK_EX|LOCK_NB) */
LEAN_EXPORT lean_obj_res fvdep_sys_lock(uint32_t fd);

/* Writer guard: new (takes ownership of fd), acquire (locks the guard; → (fd, closed)), mark_closed
 * (under the guard), release (unlocks). The finalizer closes the fd once if still open. */
LEAN_EXPORT lean_obj_res fvdep_sys_writer_new(uint32_t fd, b_lean_obj_arg path);
LEAN_EXPORT lean_obj_res fvdep_sys_writer_acquire(b_lean_obj_arg writer);
LEAN_EXPORT lean_obj_res fvdep_sys_writer_mark_closed(b_lean_obj_arg writer);
LEAN_EXPORT lean_obj_res fvdep_sys_writer_release(b_lean_obj_arg writer);

#endif
