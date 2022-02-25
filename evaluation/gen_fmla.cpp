#include "constants.h"
#include "formula.h"
#include "log.h"
#include "visitors.h"

#include <algorithm>
#include <cstdlib>
#include <random>

int sz, maxr, scale, seed, aps;
int dynamic, lookahead, no_past, no_future, bounded_past, tstp;

#define BIT(x, i) (((x)>>(i))&1)

std::mt19937 gen;

interval gen_int(int bounded) {
    if (maxr == 0) {
        return {0, 0};
    }
    int r = gen() % 4;
    if (r == 0) {
        return {0, 0};
    } else if (r == 1) {
        timestamp to = scale * (1 + (gen() % (maxr + !bounded)));
        if (to == scale * (maxr + 1)) to = MAX_TIMESTAMP;
        return {0, to};
    } else {
        timestamp from = (1 + gen() % maxr);
        timestamp to = scale * (from + (gen() % (maxr - from + 1 + !bounded)));
        if (to == scale * (maxr + 1)) to = MAX_TIMESTAMP;
        return {scale * from, to};
    }
}

Formula *gen_fmla_full_MTL(int size) {
    assert(size > 0);
    if (size == 1) {
        int ap = gen() % aps;
        return new_ap(ap);
    } else if (size == 2) {
        int op;
        do {
          op = gen() % 3;
        } while (!((!no_past || (op != 1)) && (!no_future || (op != 2))));
        Formula *subf = gen_fmla_full_MTL(size - 1);
        interval in;
        if (tstp) in = {0, MAX_TIMESTAMP};
        else in = gen_int(op == 2 || bounded_past);
        if (op == 0) {
            return new NegFormula(subf);
        } else if (op == 1) {
            return new PrevFormula(subf, in);
        } else {
            return new NextFormula(subf, in);
        }
    } else {
        int op;
        do {
          op = gen() % 7;
        } while (!((!no_past || (op != 3 && op != 4)) && (!no_future || (op != 5 && op != 6))));
        int lsize = 1 + gen() % (size - 2);
        interval in = gen_int(op == 5 || op == 6 || bounded_past);
        if (op == 0) {
            Formula *subf = gen_fmla_full_MTL(size - 1);
            return new NegFormula(subf);
        } else if (op == 1) {
            Formula *subf1 = gen_fmla_full_MTL(lsize);
            Formula *subf2 = gen_fmla_full_MTL(size - 1 - lsize);
            return new OrFormula(subf1, subf2);
        } else if (op == 2) {
            Formula *subf1 = gen_fmla_full_MTL(lsize);
            Formula *subf2 = gen_fmla_full_MTL(size - 1 - lsize);
            return new AndFormula(subf1, subf2);
        } else if (op == 3) {
            Formula *subf = gen_fmla_full_MTL(size - 1);
            if (tstp) in = {0, MAX_TIMESTAMP};
            return new PrevFormula(subf, in);
        } else if (op == 4) {
            Formula *subf1 = gen_fmla_full_MTL(lsize);
            Formula *subf2 = gen_fmla_full_MTL(size - 1 - lsize);
            return new SinceFormula(subf1, subf2, in);
        } else if (op == 5) {
            Formula *subf = gen_fmla_full_MTL(size - 1);
            if (tstp) in = {0, MAX_TIMESTAMP};
            return new NextFormula(subf, in);
        } else {
            assert(op == 6);
            Formula *subf1 = gen_fmla_full_MTL(lsize);
            Formula *subf2 = gen_fmla_full_MTL(size - 1 - lsize);
            return new UntilFormula(subf1, subf2, in);
        }
    }
}

Formula *gen_fmla_full_MDL(int size);

Regex *gen_regex(int size) {
    assert(size > 1);
    if (size == 2) {
        Formula *fmla = gen_fmla_full_MDL(size - 1);
        if (lookahead && gen() % 2) return new LookaheadRegex(fmla);
        else return new SymbolRegex(fmla);
    } else if (size <= 4) {
        int op = gen() % 2;
        if (op == 0) {
            Formula *fmla = gen_fmla_full_MDL(size - 1);
            if (lookahead && gen() % 2) return new LookaheadRegex(fmla);
            else return new SymbolRegex(fmla);
        } else {
            Regex *subr = gen_regex(size - 1);
            return new StarRegex(subr);
        }
    } else {
        int op = gen() % 4;
        int lsize = 2 + gen() % (size - 4);
        if (op == 0) {
            Formula *fmla = gen_fmla_full_MDL(size - 1);
            if (lookahead && gen() % 2) return new LookaheadRegex(fmla);
            else return new SymbolRegex(fmla);
        } else if (op == 1) {
            Regex *subr1 = gen_regex(lsize);
            Regex *subr2 = gen_regex(size - 1 - lsize);
            return new TimesRegex(subr1, subr2);
        } else if (op == 2) {
            Regex *subr1 = gen_regex(lsize);
            Regex *subr2 = gen_regex(size - 1 - lsize);
            return new PlusRegex(subr1, subr2);
        } else {
            assert(op == 3);
            Regex *subr = gen_regex(size - 1);
            return new StarRegex(subr);
        }
    }
}

Formula *gen_fmla_full_MDL(int size) {
    assert(size > 0);
    Formula *fmla = NULL;
    if (size == 1) {
        int ap = gen() % aps;
        fmla = new_ap(ap);
    } else if (size == 2) {
        Formula *subf = gen_fmla_full_MDL(size - 1);
        fmla = new NegFormula(subf);
    } else {
        int op = gen() % 5;
        int lsize = 1 + gen() % (size - 2);
        if (op == 0) {
            Formula *subf = gen_fmla_full_MDL(size - 1);
            fmla = new NegFormula(subf);
        } else if (op == 1) {
            Formula *subf1 = gen_fmla_full_MDL(lsize);
            Formula *subf2 = gen_fmla_full_MDL(size - 1 - lsize);
            fmla = new OrFormula(subf1, subf2);
        } else if (op == 2) {
            Formula *subf1 = gen_fmla_full_MDL(lsize);
            Formula *subf2 = gen_fmla_full_MDL(size - 1 - lsize);
            fmla = new AndFormula(subf1, subf2);
        } else if (op == 3) {
            interval in = gen_int(bounded_past);
            Regex *subr = NULL;
            while (subr == NULL || !subr->wf()) subr = gen_regex(size - 1);
            fmla = new BwFormula(subr, in);
        } else {
            assert(op == 4);
            interval in = gen_int(1);
            Regex *subr = NULL;
            while (subr == NULL || !subr->wf()) subr = gen_regex(size - 1);
            fmla = new FwFormula(subr, in);
        }
    }
    assert(fmla != NULL);
    return fmla;
}

Formula *gen_fmla() {
    if (dynamic) return gen_fmla_full_MDL(sz);
    else return gen_fmla_full_MTL(sz);
}

int main(int argc, char **argv) {
    if (argc != 8) {
        fprintf(stderr, "gen_fmla PREFIX SIZE MAXR TYPE SCALE SEED APS\n");
        fprintf(stderr, "where TYPE = (b_5 ... b_1 b_0)_2\n");
        fprintf(stderr, "      b_0 <--> including dynamic modalities\n");
        fprintf(stderr, "      b_1 <--> including look-ahead regular expressions\n");
        fprintf(stderr, "      b_2 <--> no past temporal operators\n");
        fprintf(stderr, "      b_3 <--> no future temporal operators\n");
        fprintf(stderr, "      b_4 <--> no unbounded intervals\n");
        fprintf(stderr, "      b_5 <--> ts = tp\n");
        exit(EXIT_FAILURE);
    }

    sz = atoi(argv[2]);
    maxr = atoi(argv[3]);

    int type = atoi(argv[4]);
    dynamic = BIT(type, 0);
    lookahead = BIT(type, 1);
    no_past = BIT(type, 2);
    no_future = BIT(type, 3);
    bounded_past = BIT(type, 4);
    tstp = BIT(type, 5);

    scale = atoi(argv[5]);

    seed = atoi(argv[6]);
    gen.seed(seed);

    aps = ap_cnt;
    if (argc > 7) aps = atoi(argv[7]);

    Formula *fmla = gen_fmla();
    print_fmla_hydra(argv[1], fmla);
    if (!dynamic && no_future && tstp) print_fmla_reelay(argv[1], fmla);
    delete fmla;

    return 0;
}
