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

Formula *pred(int i) {
    return new PredFormula(ap_names[i], i);
}

Formula *neg(Formula *f) {
    return new NegFormula(f);
}

Formula *impl(Formula *f, Formula *g) {
    return new OrFormula(neg(f), g);
}

Formula *always(Formula *f) {
    return neg(new UntilFormula(new BoolFormula(true), neg(f), {0, 0}));
}

Formula *getAndFormula(int n) {
    Formula *cur_pos = impl(pred(n), always(impl(pred(ap_cnt - 1), pred(n))));
    Formula *cur_neg = impl(neg(pred(n)), always(impl(pred(ap_cnt - 1), neg(pred(n)))));
    Formula *cur = new AndFormula(cur_pos, cur_neg);
    if (n > 0) {
        return new AndFormula(getAndFormula(n - 1), cur);
    } else {
        return cur;
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
    if (past) fmla = new SinceFormula(pred(0), pred(1), {n, n});
    else fmla = new UntilFormula(pred(0), pred(1), {n, n});

    print_fmla_hydra(argv[2], fmla);
    print_fmla_monpoly(argv[2], fmla);
    if (past) print_fmla_reelay(argv[2], fmla);
    print_fmla_r2u2(argv[2], fmla);
    delete fmla;

    Log log(len, 2);
    gen_fixed_log(&log, n, len);
    print_log_hydra(argv[3], &log);
    if (past) print_log_reelay(argv[3], &log);
    print_log_r2u2(argv[3], &log);

    return 0;
}
