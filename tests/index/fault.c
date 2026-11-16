#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

/* Root process alone: Lean/Lake children compile normally. Only fixture paths are touched. */
__attribute__((constructor)) static void owner(void) {
    if (getenv("FVDEP_INDEX_FAULT") && !getenv("FVDEP_INDEX_FAULT_PID")) {
        char pid[32];
        snprintf(pid, sizeof(pid), "%ld", (long)getpid());
        setenv("FVDEP_INDEX_FAULT_PID", pid, 1);
    }
}

static int deny(const char *path) {
    const char *mode = getenv("FVDEP_INDEX_FAULT");
    const char *pid = getenv("FVDEP_INDEX_FAULT_PID");
    if (!mode || !pid || strtol(pid, NULL, 10) != (long)getpid() || !path) return 0;
    const char *root = getenv("FVDEP_INDEX_FAULT_ROOT");
    if (root) {
        if (path[0] == '/') {
            size_t n = strlen(root);
            if (strncmp(root, path, n) || path[n] != '/') return 0;
        } else {
            char cwd[8192];
            if (!getcwd(cwd, sizeof(cwd)) || strcmp(root, cwd)) return 0;
        }
    }
    const char *base = strrchr(path, '/');
    base = base ? base + 1 : path;
    size_t n = strlen(path);
    int hit = (!strcmp(mode, "load") && strstr(path, ".lake/fvdep-index/") &&
               n >= 6 && !strcmp(path + n - 6, ".olean")) ||
              (!strcmp(mode, "write") && !strncmp(base, ".index.json.tmp-", 16));
    if (!hit) return 0;
    const char *log = getenv("FVDEP_INDEX_FAULT_HIT");
    if (log) {
        int fd = (int)syscall(SYS_openat, AT_FDCWD, log, O_WRONLY | O_CREAT | O_APPEND, 0600);
        if (fd >= 0) {
            (void)syscall(SYS_write, fd, mode, strlen(mode));
            (void)syscall(SYS_write, fd, "\n", 1);
            (void)syscall(SYS_close, fd);
        }
    }
    errno = EIO;
    return 1;
}

int open(const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap;
        va_start(ap, flags);
        mode = (mode_t)va_arg(ap, int);
        va_end(ap);
    }
    if (deny(path)) return -1;
    int (*real)(const char *, int, ...) = dlsym(RTLD_NEXT, "open");
    return real(path, flags, mode);
}

int open64(const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap;
        va_start(ap, flags);
        mode = (mode_t)va_arg(ap, int);
        va_end(ap);
    }
    if (deny(path)) return -1;
    int (*real)(const char *, int, ...) = dlsym(RTLD_NEXT, "open64");
    return real(path, flags, mode);
}

int openat(int dir, const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap;
        va_start(ap, flags);
        mode = (mode_t)va_arg(ap, int);
        va_end(ap);
    }
    if (deny(path)) return -1;
    int (*real)(int, const char *, int, ...) = dlsym(RTLD_NEXT, "openat");
    return real(dir, path, flags, mode);
}

FILE *fopen(const char *path, const char *mode) {
    if (deny(path)) return NULL;
    FILE *(*real)(const char *, const char *) = dlsym(RTLD_NEXT, "fopen");
    return real(path, mode);
}

FILE *fopen64(const char *path, const char *mode) {
    if (deny(path)) return NULL;
    FILE *(*real)(const char *, const char *) = dlsym(RTLD_NEXT, "fopen64");
    return real(path, mode);
}

#ifdef FAULT_CONTROL
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    int fd = open(argv[1], O_RDONLY);
    if (fd >= 0) { close(fd); return 1; }
    return errno == EIO ? 0 : 3;
}
#endif
