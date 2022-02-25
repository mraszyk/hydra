#include <chrono>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

int parseline(char *pattern, char *line) {
    size_t res = 0;
    int i = 0;
    while (line[i] && pattern[i]) {
        if (line[i] != pattern[i]) return 0;
        i++;
    }
    while (line[i]==' ' || line[i] == '\t') i++;
    while (line[i] >= '0' && line[i] <= '9') {
        res = 10 * res + (line[i] - '0');
        i++;
    }
    while (line[i]==' ' || line[i] == '\t') i++;
    if (line[i++] != 'k') return 0;
    if (line[i++] != 'B') return 0;
    if (line[i++] != '\n') return 0;
    if (line[i]) return 0;
    return res;
}

int main(int argc, char **argv) {
    int tle = atoi(argv[1]) * 1000;
    pid_t pid;
    size_t time, space;
    char vmdata[666]="VmData:";
    char vmstk[666]="VmStk:";

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
        char fname[666];
        sprintf(fname, "/proc/%d/status", pid);
        int status;
        space = 0;
        auto started = std::chrono::high_resolution_clock::now();
        while (waitpid(pid, &status, WNOHANG) == 0) {
            auto now = std::chrono::high_resolution_clock::now();
            if (tle != 0 && std::chrono::duration_cast<std::chrono::milliseconds>(now - started).count() > tle) {
                char cmd[12345];
                sprintf(cmd, "kill -9 %d\n", pid);
                system(cmd);
                printf("%d %d\n", tle, 0);
                return 0;
            }
            size_t sum = 0;
            FILE *f = fopen(fname, "r");
            while (!feof(f)) {
                char *res;
                size_t n = 0;
                getline(&res, &n, f);
                sum += parseline(vmdata, res);
                sum += parseline(vmstk, res);
                free(res);
            }
            fclose(f);
            if (waitpid(pid, &status, WNOHANG) == 0 && sum > space) {
                space = sum;
            }
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
