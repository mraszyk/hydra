#include "constants.h"
#include "formula.h"
#include "log.h"
#include "visitors.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>

Formula *pred(int i) {
    return new_ap(i);
}

Regex *reg(int n) {
  if (n == 0) return new StarRegex(new SymbolRegex(pred(0)));
  else return new StarRegex(new TimesRegex(new SymbolRegex(pred(n)), reg(n - 1)));
}

int main(int argc, char **argv) {
    if (argc != 6) {
        fprintf(stderr, "gen_mdl_quad DIR PREFIX_FMLA PREFIX_LOG N LEN\n");
        exit(EXIT_FAILURE);
    }

    int dir_fw = !strcmp(argv[1], "fw");
    int n = atoi(argv[4]);
    int len = atoi(argv[5]);

    Regex *r = reg(n);
    Formula *fmla = NULL;
    if (dir_fw) fmla = new FwFormula(r, {0, 0});
    else fmla = new BwFormula(r, {0, 0});

    print_fmla_hydra(argv[2], fmla);
    delete fmla;

    Log log = gen_log(len - 1, len - 1, 4, 0, n + 1, 0, 1);
    print_log_hydra(argv[3], &log);
    print_log_monpoly(argv[3], &log);

    return 0;
}
