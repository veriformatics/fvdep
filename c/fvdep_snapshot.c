/* Project snapshot shim (docs/contracts/U5-sandbox.md S1; residue `project-snapshot`): the
 * mechanism alone; the walk, the caps + every refusal stay in Lean. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "fvdep_snapshot.h"

static lean_obj_res fvdep_snapshot_error(int error) {
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, lean_usize_to_nat((size_t)error));
    return lean_io_result_mk_ok(r);
}

/* One path component: nonempty, neither `.` nor `..`, no `/`, no interior NUL. Kept here, below
 * every caller: the Lean walk checks the module-name grammar first, this guard holds without it. */
static int fvdep_snapshot_component(b_lean_obj_arg name) {
    const char *c = lean_string_cstr(name);
    size_t n = strlen(c);
    return n > 0 && n + 1 == lean_string_size(name) && strchr(c, '/') == NULL &&
           strcmp(c, ".") != 0 && strcmp(c, "..") != 0;
}

LEAN_EXPORT lean_obj_res fvdep_snapshot_open(uint32_t dir, b_lean_obj_arg name) {
    if (!fvdep_snapshot_component(name)) {
        return fvdep_snapshot_error(EINVAL);
    }
    int fd = openat((int)dir, lean_string_cstr(name),
                    O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_NOCTTY | O_CLOEXEC);
    if (fd < 0) {
        return fvdep_snapshot_error(errno);
    }
    struct stat st;
    if (fstat(fd, &st) != 0) {
        int e = errno;
        close(fd);
        return fvdep_snapshot_error(e);
    }
    size_t size = st.st_size < 0 ? 0 : (size_t)st.st_size;
    lean_object *a = lean_alloc_array(3, 3);
    lean_array_set_core(a, 0, lean_usize_to_nat((size_t)fd));
    lean_array_set_core(a, 1, lean_usize_to_nat((size_t)(st.st_mode & S_IFMT)));
    lean_array_set_core(a, 2, lean_usize_to_nat(size));
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, a);
    return lean_io_result_mk_ok(r);
}
