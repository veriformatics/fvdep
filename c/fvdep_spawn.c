/* Sandbox spawn shim (docs/contracts/U5-sandbox.md R2, R4, R8; residue `sandbox-spawn`): the
 * mechanism alone; descriptor roles, deadlines, retention + framing stay in Lean. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "fvdep_spawn.h"

extern char **environ;

typedef int (*fvdep_closefrom_fn)(posix_spawn_file_actions_t *, int);

/* glibc ≥ 2.34's posix_spawn_file_actions_addclosefrom_np, resolved at run time: the Lean
 * toolchain links against its own older glibc (an undefined symbol at link time), while the
 * system's libc answers at run time. Absent → NULL: the spawn refuses (ENOSYS) rather than run a
 * step with inherited descriptors open. */
static fvdep_closefrom_fn fvdep_closefrom(void) {
    fvdep_closefrom_fn fn;
    *(void **)(&fn) = dlsym(RTLD_DEFAULT, "posix_spawn_file_actions_addclosefrom_np");
    return fn;
}

static lean_obj_res fvdep_error(int error) {
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, lean_usize_to_nat((size_t)error));
    return lean_io_result_mk_ok(r);
}

static lean_obj_res fvdep_values(size_t n, const size_t *vs) {
    lean_object *a = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) {
        lean_array_set_core(a, i, lean_usize_to_nat(vs[i]));
    }
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, a);
    return lean_io_result_mk_ok(r);
}

static lean_obj_res fvdep_unit(int result) {
    if (result < 0) {
        return fvdep_error(errno);
    }
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, lean_box(0));
    return lean_io_result_mk_ok(r);
}

/* A Lean string with an interior NUL would reach the kernel cut at it (another path or argument
 * than the caller's): EINVAL. */
static int fvdep_cstr(b_lean_obj_arg s, const char **out) {
    const char *c = lean_string_cstr(s);
    if (strlen(c) + 1 != lean_string_size(s)) {
        return EINVAL;
    }
    *out = c;
    return 0;
}

/* argv as a NULL-terminated array over the borrowed Lean strings (the caller frees the array), or
 * NULL with *e = ENOMEM or EINVAL (an element with an interior NUL). */
static char **fvdep_argv(b_lean_obj_arg argv, int *e) {
    size_t n = lean_array_size(argv);
    char **out = malloc((n + 1) * sizeof(char *));
    if (out == NULL) {
        *e = ENOMEM;
        return NULL;
    }
    for (size_t i = 0; i < n; i++) {
        const char *s;
        if ((*e = fvdep_cstr(lean_array_get_core(argv, i), &s)) != 0) {
            free(out);
            return NULL;
        }
        out[i] = (char *)s;
    }
    out[n] = NULL;
    return out;
}

/* The spawned process starts with an empty signal mask + every catchable signal at its default:
 * an ignored disposition (the Lean runtime ignores SIGPIPE) survives exec. */
static int fvdep_attr(posix_spawnattr_t *attr) {
    sigset_t none, all;
    sigemptyset(&none);
    sigfillset(&all);
    sigdelset(&all, SIGKILL);
    sigdelset(&all, SIGSTOP);
    int e = posix_spawnattr_init(attr);
    if (e != 0) {
        return e;
    }
    if ((e = posix_spawnattr_setsigmask(attr, &none)) != 0 ||
        (e = posix_spawnattr_setsigdefault(attr, &all)) != 0 ||
        (e = posix_spawnattr_setflags(attr, POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF)) != 0) {
        posix_spawnattr_destroy(attr);
    }
    return e;
}

LEAN_EXPORT lean_obj_res fvdep_spawn_bwrap(b_lean_obj_arg path, b_lean_obj_arg argv) {
    const char *cpath;
    int e = fvdep_cstr(path, &cpath);
    if (e != 0) {
        return fvdep_error(e);
    }
    /* read + write ends of stdout, stderr, status (3), output (4) */
    int fds[8];
    int made = 0;
    while (made < 8) {
        int p[2];
        if (pipe2(p, O_CLOEXEC) != 0) {
            e = errno;
            goto fail;
        }
        /* Every end above 4: a write end already at its target descriptor would keep its
         * close-on-exec flag through dup2, and one at another pipe's target would be overwritten
         * before its own dup2. */
        for (int k = 0; k < 2; k++) {
            if (p[k] < 5) {
                int moved = fcntl(p[k], F_DUPFD_CLOEXEC, 5);
                if (moved < 0) {
                    e = errno;
                    close(p[0]);
                    close(p[1]);
                    goto fail;
                }
                close(p[k]);
                p[k] = moved;
            }
        }
        fds[made] = p[0];
        fds[made + 1] = p[1];
        made += 2;
    }
    fvdep_closefrom_fn closefrom = fvdep_closefrom();
    if (closefrom == NULL) {
        e = ENOSYS;
        goto fail;
    }
    char **cargv = fvdep_argv(argv, &e);
    if (cargv == NULL) {
        goto fail;
    }
    posix_spawn_file_actions_t fa;
    if ((e = posix_spawn_file_actions_init(&fa)) != 0) {
        free(cargv);
        goto fail;
    }
    if ((e = posix_spawn_file_actions_addopen(&fa, 0, "/dev/null", O_RDONLY, 0)) != 0 ||
        (e = posix_spawn_file_actions_adddup2(&fa, fds[1], 1)) != 0 ||
        (e = posix_spawn_file_actions_adddup2(&fa, fds[3], 2)) != 0 ||
        (e = posix_spawn_file_actions_adddup2(&fa, fds[5], 3)) != 0 ||
        (e = posix_spawn_file_actions_adddup2(&fa, fds[7], 4)) != 0 ||
        /* bwrap passes every inherited descriptor into the sandbox (vflab, bubblewrap 0.11.1) */
        (e = closefrom(&fa, 5)) != 0) {
        posix_spawn_file_actions_destroy(&fa);
        free(cargv);
        goto fail;
    }
    posix_spawnattr_t attr;
    if ((e = fvdep_attr(&attr)) != 0) {
        posix_spawn_file_actions_destroy(&fa);
        free(cargv);
        goto fail;
    }
    char *envp[] = {NULL};
    pid_t pid;
    e = posix_spawn(&pid, cpath, &fa, &attr, cargv, envp);
    posix_spawnattr_destroy(&attr);
    posix_spawn_file_actions_destroy(&fa);
    free(cargv);
    if (e != 0) {
        goto fail;
    }
    for (int k = 1; k < 8; k += 2) {
        close(fds[k]);
    }
    size_t vs[5] = {(size_t)pid, (size_t)fds[0], (size_t)fds[2], (size_t)fds[4], (size_t)fds[6]};
    return fvdep_values(5, vs);
fail:
    for (int k = 0; k < made; k++) {
        close(fds[k]);
    }
    return fvdep_error(e);
}

LEAN_EXPORT lean_obj_res fvdep_spawn_poll(b_lean_obj_arg fds, uint32_t timeout) {
    size_t n = lean_array_size(fds);
    struct pollfd *p = calloc(n ? n : 1, sizeof(struct pollfd));
    size_t *vs = malloc((n ? n : 1) * sizeof(size_t));
    if (p == NULL || vs == NULL) {
        free(p);
        free(vs);
        return fvdep_error(ENOMEM);
    }
    for (size_t i = 0; i < n; i++) {
        p[i].fd = (int)lean_usize_of_nat(lean_array_get_core(fds, i));
        p[i].events = POLLIN;
    }
    int r = poll(p, (nfds_t)n, timeout > INT32_MAX ? INT32_MAX : (int)timeout);
    if (r < 0) {
        int e = errno;
        free(p);
        free(vs);
        return fvdep_error(e);
    }
    for (size_t i = 0; i < n; i++) {
        vs[i] = (size_t)(unsigned short)p[i].revents;
    }
    lean_obj_res out = fvdep_values(n, vs);
    free(p);
    free(vs);
    return out;
}

LEAN_EXPORT lean_obj_res fvdep_spawn_kill(uint32_t pid, uint32_t sig) {
    /* The supervisor signals its own bwrap child alone: pid 0 (its process group) or a value that
     * reads as negative (-1 = every process it may signal: on vflab, the whole shared login) is
     * refused. */
    if ((pid_t)pid <= 0) {
        errno = EINVAL;
        return fvdep_unit(-1);
    }
    return fvdep_unit(kill((pid_t)pid, (int)sig));
}

LEAN_EXPORT lean_obj_res fvdep_spawn_wait(uint32_t pid) {
    int status;
    if (waitpid((pid_t)pid, &status, 0) < 0) {
        return fvdep_error(errno);
    }
    size_t vs[2];
    if (WIFSIGNALED(status)) {
        vs[0] = 1;
        vs[1] = (size_t)WTERMSIG(status);
    } else {
        vs[0] = 0;
        vs[1] = (size_t)WEXITSTATUS(status);
    }
    return fvdep_values(2, vs);
}

LEAN_EXPORT lean_obj_res fvdep_step_nodump(lean_obj_arg unit) {
    (void)unit;
    return fvdep_unit(prctl(PR_SET_DUMPABLE, 0, 0, 0, 0));
}

LEAN_EXPORT lean_obj_res fvdep_step_channel(uint32_t fd) {
    /* The supervisor's output pipe arrives inherited, so without FD_CLOEXEC (exec closed every
     * descriptor that had it). Started without it, the number is this process's own: Lean 4.35's
     * libuv opens an io_uring there (vflab), close-on-exec like every descriptor it opens. */
    int flags = fcntl((int)fd, F_GETFD);
    if (flags < 0)
        return fvdep_unit(-1);
    struct stat st;
    if ((flags & FD_CLOEXEC) != 0 || fstat((int)fd, &st) != 0 || !S_ISFIFO(st.st_mode)) {
        errno = EBADF;
        return fvdep_unit(-1);
    }
    return fvdep_unit(fcntl((int)fd, F_SETFD, flags | FD_CLOEXEC));
}

LEAN_EXPORT lean_obj_res fvdep_step_core_limit(uint32_t limit) {
    struct rlimit r = {limit, limit};
    return fvdep_unit(setrlimit(RLIMIT_CORE, &r));
}

LEAN_EXPORT lean_obj_res fvdep_step_file_limit(uint64_t bytes) {
    struct rlimit r = {(rlim_t)bytes, (rlim_t)bytes};
    return fvdep_unit(setrlimit(RLIMIT_FSIZE, &r));
}

LEAN_EXPORT lean_obj_res fvdep_step_spawn(b_lean_obj_arg argv, b_lean_obj_arg stdout_path) {
    if (lean_array_size(argv) == 0) {
        return fvdep_error(EINVAL);
    }
    const char *out;
    int e = fvdep_cstr(stdout_path, &out);
    if (e != 0) {
        return fvdep_error(e);
    }
    char **cargv = fvdep_argv(argv, &e);
    if (cargv == NULL) {
        return fvdep_error(e);
    }
    posix_spawn_file_actions_t fa;
    if ((e = posix_spawn_file_actions_init(&fa)) != 0) {
        free(cargv);
        return fvdep_error(e);
    }
    if (out[0] != '\0' &&
        (e = posix_spawn_file_actions_addopen(&fa, 1, out,
                                              O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0644)) != 0) {
        posix_spawn_file_actions_destroy(&fa);
        free(cargv);
        return fvdep_error(e);
    }
    posix_spawnattr_t attr;
    if ((e = fvdep_attr(&attr)) != 0) {
        posix_spawn_file_actions_destroy(&fa);
        free(cargv);
        return fvdep_error(e);
    }
    pid_t pid;
    e = posix_spawnp(&pid, cargv[0], &fa, &attr, cargv, environ);
    posix_spawnattr_destroy(&attr);
    posix_spawn_file_actions_destroy(&fa);
    free(cargv);
    if (e != 0) {
        return fvdep_error(e);
    }
    size_t vs[1] = {(size_t)pid};
    return fvdep_values(1, vs);
}

LEAN_EXPORT lean_obj_res fvdep_step_killall(lean_obj_arg unit) {
    (void)unit;
    /* kill(-1) reaches every process of the caller's PID namespace that it may signal: run outside
     * the step's fresh namespace it killed every process of the shared login on vflab. Inside, the
     * helper is PID 2 (bwrap's init = 1); in the host's namespace PID 2 is kthreadd, so no user
     * process passes this check. */
    if (getpid() != 2) {
        errno = EPERM;
        return fvdep_unit(-1);
    }
    return fvdep_unit(kill(-1, SIGKILL));
}

LEAN_EXPORT lean_obj_res fvdep_step_statvfs(b_lean_obj_arg path) {
    const char *cpath;
    int e = fvdep_cstr(path, &cpath);
    if (e != 0) {
        return fvdep_error(e);
    }
    struct statvfs s;
    if (statvfs(cpath, &s) != 0) {
        return fvdep_error(errno);
    }
    size_t vs[1] = {(size_t)s.f_bavail};
    return fvdep_values(1, vs);
}

LEAN_EXPORT lean_obj_res fvdep_step_open_regular(b_lean_obj_arg path) {
    const char *cpath;
    int e = fvdep_cstr(path, &cpath);
    if (e != 0) {
        return fvdep_error(e);
    }
    int fd = open(cpath, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC);
    if (fd < 0) {
        return fvdep_error(errno);
    }
    struct stat st;
    if (fstat(fd, &st) != 0) {
        e = errno;
        close(fd);
        return fvdep_error(e);
    }
    if (!S_ISREG(st.st_mode)) {
        close(fd);
        return fvdep_error(0);
    }
    size_t vs[2] = {(size_t)fd, (size_t)st.st_size};
    return fvdep_values(2, vs);
}
