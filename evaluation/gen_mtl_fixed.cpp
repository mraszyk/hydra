#include "constants.h"
#include "formula.h"
#include "log.h"
#include "visitors.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>

void gen_fixed_log(Log *log, int n, int len) {
    int ts = 1;
    int line = 0;
    while (len) {
        log->ts[line] = ts++;
        len--;
        log->set(line, 0);
        if (line % 2 == 0) {
            log->set(line, 1);
        }
        line++;
    }
}

int main(int argc, char **argv) {
    if (argc != 6) {
        fprintf(stderr, "gen_mtl_fixed PAST PREFIX_FMLA PREFIX_LOG N LEN\n");
        exit(EXIT_FAILURE);
    }

    int past = atoi(argv[1]);
    int n = atoi(argv[4]);
    int len = atoi(argv[5]);

    Formula *fmla;
    if (past) fmla = new SinceFormula(new_ap(0), new_ap(1), {n, n});
    else fmla = new UntilFormula(new_ap(0), new_ap(1), {n, n});

    print_fmla_hydra(argv[2], fmla);
    if (past) print_fmla_reelay(argv[2], fmla);
    delete fmla;

    Log log(len, 2);
    gen_fixed_log(&log, n, len);
    print_log_hydra(argv[3], &log);
    if (past) print_log_reelay(argv[3], &log);

    return 0;
}
