#include <limits.h>
#include <stdlib.h>

__attribute__((noinline)) static void leak_control(void) {
    volatile unsigned char *p = malloc(97);
    if (!p) exit(3);
    p[0] = 1;
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (argv[1][0] == 'a') {
        volatile unsigned char *p = malloc(8);
        if (!p) return 3;
        volatile size_t at = 9;
        p[at] = 1;
        free((void *)p);
    } else if (argv[1][0] == 'l') {
        leak_control();
    } else if (argv[1][0] == 'u') {
        volatile int maximum = INT_MAX;
        volatile int one = 1;
        volatile int overflow = maximum + one;
        (void)overflow;
    } else {
        unsigned char *p = malloc(8);
        if (!p) return 3;
        p[0] = 1;
        free(p);
    }
    return 0;
}
