/* Persistence shim (docs/contracts/U3-codecs.md F1; port of fvapi 02d99d1 c/fvapi_fsync.c): policy
 * stays in Lean; each syscall export issues exactly one libc call (dynamic symbols: an LD_PRELOAD
 * interposer sees them) and returns errno at once, no retry. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <unistd.h>

#include "fvdep_sys.h"

typedef struct {
    ssize_t value;
    int error;
} fvdep_sys_result;

static fvdep_sys_result fvdep_result(ssize_t value) {
    return (fvdep_sys_result){value, value < 0 ? errno : 0};
}

static lean_obj_res fvdep_response(fvdep_sys_result r) {
    lean_object *result = lean_alloc_ctor(r.value < 0 ? 0 : 1, 1, 0);
    lean_ctor_set(result, 0,
                  lean_usize_to_nat(r.value < 0 ? (size_t)r.error : (size_t)r.value));
    return lean_io_result_mk_ok(result);
}

LEAN_EXPORT lean_obj_res fvdep_sys_open_file(b_lean_obj_arg path, uint32_t mode) {
    return fvdep_response(fvdep_result(open(lean_string_cstr(path),
                                            O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW,
                                            (mode_t)mode)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_open_dir(b_lean_obj_arg path) {
    return fvdep_response(fvdep_result(open(lean_string_cstr(path),
                                            O_RDONLY | O_DIRECTORY | O_CLOEXEC)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_open_read(b_lean_obj_arg path) {
    return fvdep_response(fvdep_result(open(lean_string_cstr(path), O_RDONLY | O_CLOEXEC)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_open_lock(b_lean_obj_arg path) {
    return fvdep_response(fvdep_result(open(lean_string_cstr(path),
                                            O_RDWR | O_CREAT | O_CLOEXEC | O_NOFOLLOW, 0644)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_write(uint32_t fd, b_lean_obj_arg bytes, size_t offset,
                                         size_t count) {
    size_t size = lean_sarray_size(bytes);
    if (offset > size || count > size - offset) {
        return fvdep_response((fvdep_sys_result){-1, EINVAL});
    }
    return fvdep_response(fvdep_result(write((int)fd, lean_sarray_cptr(bytes) + offset, count)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_read(uint32_t fd, size_t count) {
    lean_object *chunk = lean_alloc_sarray(1, 0, count);
    ssize_t n = read((int)fd, lean_sarray_cptr(chunk), count);
    if (n < 0) {
        int error = errno;
        lean_dec(chunk);
        lean_object *result = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(result, 0, lean_usize_to_nat((size_t)error));
        return lean_io_result_mk_ok(result);
    }
    lean_to_sarray(chunk)->m_size = (size_t)n;
    lean_object *result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, chunk);
    return lean_io_result_mk_ok(result);
}

LEAN_EXPORT lean_obj_res fvdep_sys_sync(uint32_t fd) {
    return fvdep_response(fvdep_result(fsync((int)fd)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_close(uint32_t fd) {
    return fvdep_response(fvdep_result(close((int)fd)));
}

LEAN_EXPORT lean_obj_res fvdep_sys_rename(b_lean_obj_arg source, b_lean_obj_arg target) {
    return fvdep_response(fvdep_result(rename(lean_string_cstr(source), lean_string_cstr(target))));
}

LEAN_EXPORT lean_obj_res fvdep_sys_unlink(b_lean_obj_arg path) {
    return fvdep_response(fvdep_result(unlink(lean_string_cstr(path))));
}

LEAN_EXPORT lean_obj_res fvdep_sys_lock(uint32_t fd) {
    return fvdep_response(fvdep_result(flock((int)fd, LOCK_EX | LOCK_NB)));
}

/* The guard covers the Lean policy's whole operation, not each syscall (fvapi). */
typedef struct {
    pthread_mutex_t guard;
    int fd;
    bool closed;
    char *path;
} fvdep_writer;

static void fvdep_guard_check(int result) {
    if (result != 0) {
        lean_internal_panic("fvdep sys: native writer guard failed");
    }
}

static void fvdep_writer_finalize(void *data) {
    fvdep_writer *writer = data;
    fvdep_guard_check(pthread_mutex_lock(&writer->guard));
    if (!writer->closed) {
        writer->closed = true;
        (void)close(writer->fd);
    }
    fvdep_guard_check(pthread_mutex_unlock(&writer->guard));
    fvdep_guard_check(pthread_mutex_destroy(&writer->guard));
    free(writer->path);
    free(writer);
}

static void fvdep_writer_foreach(void *data, b_lean_obj_arg visitor) {
    (void)data;
    (void)visitor;
}

static lean_external_class *fvdep_writer_class;
static pthread_once_t fvdep_writer_once = PTHREAD_ONCE_INIT;

static void fvdep_register_writer(void) {
    fvdep_writer_class = lean_register_external_class(fvdep_writer_finalize, fvdep_writer_foreach);
}

LEAN_EXPORT lean_obj_res fvdep_sys_writer_new(uint32_t fd, b_lean_obj_arg path) {
    fvdep_guard_check(pthread_once(&fvdep_writer_once, fvdep_register_writer));
    fvdep_writer *writer = malloc(sizeof(*writer));
    if (writer == NULL) {
        (void)close((int)fd);
        lean_internal_panic("fvdep sys: native writer allocation failed");
    }
    writer->path = strdup(lean_string_cstr(path));
    if (writer->path == NULL) {
        free(writer);
        (void)close((int)fd);
        lean_internal_panic("fvdep sys: native writer path allocation failed");
    }
    writer->fd = (int)fd;
    writer->closed = false;
    fvdep_guard_check(pthread_mutex_init(&writer->guard, NULL));
    return lean_io_result_mk_ok(lean_alloc_external(fvdep_writer_class, writer));
}

LEAN_EXPORT lean_obj_res fvdep_sys_writer_acquire(b_lean_obj_arg object) {
    fvdep_writer *writer = lean_get_external_data(object);
    fvdep_guard_check(pthread_mutex_lock(&writer->guard));
    lean_object *snapshot = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(snapshot, 0, lean_usize_to_nat((size_t)writer->fd));
    lean_ctor_set(snapshot, 1, lean_box(writer->closed));
    return lean_io_result_mk_ok(snapshot);
}

LEAN_EXPORT lean_obj_res fvdep_sys_writer_mark_closed(b_lean_obj_arg object) {
    fvdep_writer *writer = lean_get_external_data(object);
    writer->closed = true;
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res fvdep_sys_writer_release(b_lean_obj_arg object) {
    fvdep_writer *writer = lean_get_external_data(object);
    fvdep_guard_check(pthread_mutex_unlock(&writer->guard));
    return lean_io_result_mk_ok(lean_box(0));
}
