#include <chrono>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

int main(int argc, char **argv) {
    int tle = atoi(argv[1]) * 1000;
    pid_t pid;
    size_t time, space;

{
    pid = fork();

    if (pid == -1) {
        perror("fork failed");
        exit(EXIT_FAILURE);
    } else if (pid == 0) {
        freopen ("/dev/null", "w", stdout);
        freopen ("error.log", "a", stderr);
        execv(argv[2], argv + 2);
        exit(EXIT_SUCCESS);
    } else {
        int status;
        space = 0;
        auto started = std::chrono::high_resolution_clock::now();
        while (waitpid(pid, &status, WNOHANG) == 0) {
            auto now = std::chrono::high_resolution_clock::now();
            if (std::chrono::duration_cast<std::chrono::milliseconds>(now - started).count() > tle) {
                char cmd[12345];
                sprintf(cmd, "kill -9 %d\n", pid);
                system(cmd);
                printf("%d %lu\n", tle, space);
                return 0;
            }
            char cmd[12345];
            sprintf(cmd, "pmap -d %d | tail -n 1 | egrep -o \"writeable/private: [0-9]*K\"", pid);
            FILE *f = popen(cmd, "r");
            char *res;
            size_t n = 0;
            getline(&res, &n, f);
            pclose(f);
            if (waitpid(pid, &status, WNOHANG) == 0) {
                size_t cur_mem;
                if (sscanf(res, "writeable/private: %luK\n", &cur_mem) != 1) {
                    fprintf(stderr, "error: pmap\n");
                } else if (cur_mem > space) {
                    space = cur_mem;
                }
            }
            free(res);
        }
    }
}

{
    pid = fork();

    if (pid == -1) {
        perror("fork failed");
        exit(EXIT_FAILURE);
    } else if (pid == 0) {
        freopen ("/dev/null", "w", stdout);
        freopen ("error.log", "a", stderr);
        execv(argv[2], argv + 2);
        exit(EXIT_SUCCESS);
    } else {
        int status;
        auto started = std::chrono::high_resolution_clock::now();
        waitpid(pid, &status, 0);
        auto done = std::chrono::high_resolution_clock::now();
        time = std::chrono::duration_cast<std::chrono::milliseconds>(done - started).count();
    }
}

    printf("%lu %lu\n", time, space);

    return 0;
}
