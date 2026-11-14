#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/syscall.h>
#include <unistd.h>

extern int __open_2(const char *path, int flags);

static void result(long value, int err, const unsigned char *bytes, size_t size) {
    printf("{\"return\":%ld,\"errno\":%d,\"bytes\":\"", value, value < 0 ? err : 0);
    for (size_t i = 0; i < size; i++) printf("%02x", bytes[i]);
    puts("\"}");
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 5) return 2;
    const char *op = argv[1], *path = argv[2];
    unsigned times = argc >= 4 ? (unsigned)strtoul(argv[3], NULL, 10) : 1;
    unsigned count = argc >= 5 ? (unsigned)strtoul(argv[4], NULL, 10) : 16;
    if (!times || times > 200 || count > 4096) return 2;
    unsigned char bytes[4096];
    for (size_t i = 0; i < sizeof(bytes); i++) bytes[i] = (unsigned char)i;
    int fd = -1;
    if (!strcmp(op, "write") || !strcmp(op, "read") || !strcmp(op, "sync") || !strcmp(op, "close") || !strcmp(op, "lock")) {
        fd = (int)syscall(SYS_openat, AT_FDCWD, path, !strcmp(op, "read") ? O_RDONLY : O_RDWR, 0);
        if (fd < 0) return 3;
    } else if (!strcmp(op, "syncDir") || !strcmp(op, "closeDir")) {
        fd = (int)syscall(SYS_openat, AT_FDCWD, path, O_RDONLY | O_DIRECTORY, 0);
        if (fd < 0) return 3;
    }
    for (unsigned i = 0; i < times; i++) {
        errno = 0;
        long value;
        if (!strcmp(op, "create")) value = open(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0644);
        else if (!strcmp(op, "open64")) value = open64(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0644);
        else if (!strcmp(op, "open2")) value = __open_2(path, O_RDONLY | O_CLOEXEC);
        else if (!strcmp(op, "openat")) value = openat(AT_FDCWD, path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0644);
        else if (!strcmp(op, "openDir")) value = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        else if (!strcmp(op, "openRead")) value = open(path, O_RDONLY | O_CLOEXEC);
        else if (!strcmp(op, "openLock")) value = open(path, O_RDWR | O_CREAT | O_CLOEXEC | O_NOFOLLOW, 0644);
        else if (!strcmp(op, "write")) value = write(fd, bytes, count);
        else if (!strcmp(op, "read")) value = read(fd, bytes, count);
        else if (!strcmp(op, "sync") || !strcmp(op, "syncDir")) value = fsync(fd);
        else if (!strcmp(op, "close") || !strcmp(op, "closeDir")) value = close(fd);
        else if (!strcmp(op, "lock")) value = flock(fd, LOCK_EX | LOCK_NB);
        else if (!strcmp(op, "unlink")) value = unlink(path);
        else if (!strcmp(op, "rename")) {
            char source[4096], target[4096];
            if (snprintf(source, sizeof(source), "%s/source", path) >= (int)sizeof(source) ||
                snprintf(target, sizeof(target), "%s/target", path) >= (int)sizeof(target)) return 2;
            value = rename(source, target);
        } else return 2;
        int err = errno;
        size_t size = !strcmp(op, "read") && value > 0 && value <= 4096 ? (size_t)value : 0;
        result(value, err, bytes, size);
        if (value >= 0 && (!strcmp(op, "create") || !strcmp(op, "open64") || !strcmp(op, "openat") ||
            !strcmp(op, "open2") || !strcmp(op, "openRead") || !strcmp(op, "openDir") || !strcmp(op, "openLock")))
            (void)syscall(SYS_close, value);
    }
    if (fd >= 0) (void)syscall(SYS_close, fd);
    return 0;
}
