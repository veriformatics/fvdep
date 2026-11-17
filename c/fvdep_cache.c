/* Build cache shim (docs/contracts/U5-sandbox.md K4, K5; residue `cache-fs`): the mechanism alone;
 * pins, publication, eviction + validation stay in Lean. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "fvdep_cache.h"

static lean_obj_res fvdep_cache_result(int result) {
    if (result < 0) {
        lean_object *r = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(r, 0, lean_usize_to_nat((size_t)errno));
        return lean_io_result_mk_ok(r);
    }
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(0));
    return lean_io_result_mk_ok(r);
}

/* A Lean string with an interior NUL would reach the kernel cut at it (another path than the
 * caller's): EINVAL. */
static const char *fvdep_cache_cstr(b_lean_obj_arg s) {
    const char *c = lean_string_cstr(s);
    return strlen(c) + 1 == lean_string_size(s) ? c : NULL;
}

LEAN_EXPORT lean_obj_res fvdep_cache_link(b_lean_obj_arg src, b_lean_obj_arg dst) {
    const char *s = fvdep_cache_cstr(src);
    const char *d = fvdep_cache_cstr(dst);
    if (s == NULL || d == NULL) {
        errno = EINVAL;
        return fvdep_cache_result(-1);
    }
    return fvdep_cache_result(link(s, d));
}

LEAN_EXPORT lean_obj_res fvdep_cache_touch(b_lean_obj_arg path) {
    const char *p = fvdep_cache_cstr(path);
    if (p == NULL) {
        errno = EINVAL;
        return fvdep_cache_result(-1);
    }
    return fvdep_cache_result(utimensat(AT_FDCWD, p, NULL, AT_SYMLINK_NOFOLLOW));
}
