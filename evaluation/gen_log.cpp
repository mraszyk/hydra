#include "log.h"

int main(int argc, char **argv) {
    if (argc != 7) {
        fprintf(stderr, "gen_log PREFIX TS_CNT ER DELTA SEED APS\n");
        exit(EXIT_FAILURE);
    }
    int ts_cnt = atoi(argv[2]);
    int er = atoi(argv[3]);
    int delta = atoi(argv[4]);
    int seed = atoi(argv[5]);
    int aps = ap_cnt;
    if (argc > 6) aps = atoi(argv[6]);

    Log log = gen_log(ts_cnt, er, delta, seed, aps);

    print_log_hydra(argv[1], &log);
    print_log_monpoly(argv[1], &log);
    print_log_reelay(argv[1], &log);
    print_log_r2u2(argv[1], &log);

    return 0;
}
