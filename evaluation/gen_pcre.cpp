#include <cstdio>
#include <cstdlib>
#include "../src/formula.h"
#include "../src/util.h"
#include "../src/visitors.h"

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "gen_pcre PREFIX_FMLA PREFIX_LOG N LEN\n");
        exit(EXIT_FAILURE);
    }

    int n = atoi(argv[3]);
    size_t len = (size_t)atoi(argv[4]);

    FILE *f = open_file_type(argv[1], ".pcre", "w");
    fprintf(f, "(?<=(ab){%d}).\n", n);
    fclose(f);

    print_fmla_hydra(argv[1], new BwFormula(new StarRegex(new ConcatRegex(new ConcatRegex(new ConcatRegex(new TestRegex(new PredFormula("a", 'a')), new WildCardRegex()), new TestRegex(new PredFormula("b", 'b'))), new WildCardRegex())), {2 * n, 2 * n}));

    f = open_file_type(argv[2], ".txt", "w");
    for (size_t i = 0; i < len; i++) {
        fprintf(f, "ab");
    }
    fclose(f);

    f = open_file_type(argv[2], ".log", "w");
    for (size_t i = 0; i < len; i++) {
        fprintf(f, "@%lu a\n", 2 * i);
        fprintf(f, "@%lu b\n", 2 * i + 1);
    }
    fclose(f);

    return 0;
}
