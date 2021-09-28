#include "constants.h"
#include "formula.h"
#include "log.h"
#include "visitors.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>

void gen_exp_log(Log *log, int n, int len) {
    int ts = 0;
    int line = 0;
    while (len) {
        log->ts[line++] = ts;
        len--;
        for (int m = 0; len && m < (1 << n); m++, len--) {
            log->ts[line] = ts + 1;
            for (int i = 0, k = m; k; i++, k >>= 1) {
                if (k & 1) {
                    log->set(line, i);
                }
            }
            line++;
        }
        if (len) {
            log->ts[line] = ts + 1;
            log->set(line, 0);
            log->set(line, ap_cnt - 1);
            line++;
            len--;
        }
        ts += 3;
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
    if (argc != 5) {
        fprintf(stderr, "gen_mtl_exp PREFIX_FMLA PREFIX_LOG N LEN\n");
        exit(EXIT_FAILURE);
    }

    int n = atoi(argv[3]);
    int len = atoi(argv[4]);

    Formula *andFormula = getAndFormula(n);
    Formula *not_e_1 = new NegFormula(pred(ap_cnt - 1));
    Formula *not_e_2 = new NegFormula(pred(ap_cnt - 1));
    Formula *until = new UntilFormula(not_e_1, new AndFormula(not_e_2, andFormula), {0, 0});
    Formula *fmla = new NextFormula(until, {1, 1});

    print_fmla_hydra(argv[1], fmla);
    print_fmla_monpoly(argv[1], fmla);
    delete fmla;

    Log log(len);
    gen_exp_log(&log, n, len);
    print_log_hydra(argv[2], &log);
    print_log_monpoly(argv[2], &log);

    return 0;
}
