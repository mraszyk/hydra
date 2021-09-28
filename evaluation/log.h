#ifndef __LOG_HPP__
#define __LOG_HPP__

#include <cassert>
#include <cstdio>
#include <cstring>
#include <random>

const int ap_cnt = 17;
const char *ap_names[] = {"a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8", "a9", "aA", "aB", "aC", "aD", "aE", "aF", "E"};

struct Log {
    int len;
    int *ts;
    int *log;
    int cols;

    Log(int len, int cols = ap_cnt) : len(len), cols(cols) {
        ts = new int[len];
        log = new int[len * cols];
        memset(log, 0, len * cols * sizeof(int));
    }
    ~Log() {
        delete [] ts;
        delete [] log;
    }
    void set(int line, int ap) {
        assert(0 <= ap && ap < cols);
        log[line * cols + ap] = 1;
    }
    int get(int line, int ap) {
        assert(0 <= ap && ap < cols);
        return log[line * cols + ap];
    }
};

void print_log_hydra_raw(FILE *f_log, Log *log) {
    for (int i = 0; i < log->len; i++) {
        fprintf(f_log, "@%d", log->ts[i]);
        for (int j = 0; j < log->cols; j++) {
            if (log->get(i, j)) fprintf(f_log, " %s", ap_names[j]);
        }
        fprintf(f_log, "\n");
    }
}

void print_log_hydra(const char *fname, Log *log) {
    char *hydra_log_name = new char[strlen(fname) + 5];
    strcpy(hydra_log_name, fname);
    strcat(hydra_log_name, ".log");
    FILE *hydra_log_f = fopen(hydra_log_name, "w");

    print_log_hydra_raw(hydra_log_f, log);

    fclose(hydra_log_f);
}

void print_log_monpoly_raw(FILE *f_log, Log *log) {
    for (int i = 0; i < log->len; i++) {
        fprintf(f_log, "@%d", log->ts[i]);
        for (int j = 0; j < log->cols; j++) {
            if (log->get(i, j)) fprintf(f_log, " %s()", ap_names[j]);
        }
        fprintf(f_log, "\n");
    }
}

void print_log_monpoly(const char *fname, Log *log) {
    char *monpoly_log_name = new char[strlen(fname) + 6];
    strcpy(monpoly_log_name, fname);
    strcat(monpoly_log_name, ".mlog");
    FILE *monpoly_log_f = fopen(monpoly_log_name, "w");

    print_log_monpoly_raw(monpoly_log_f, log);

    fclose(monpoly_log_f);
}

void print_log_reelay_raw(FILE *f_log, Log *log, int col_names) {
    if (col_names) {
        for (int i = 0; i < log->cols; i++) {
            fprintf(f_log, "%s%s", (i == 0 ? "" : ","), ap_names[i]);
        }
        fprintf(f_log, "\n");
    }
    for (int i = 0; i < log->len; i++) {
        for (int j = 0; j < log->cols; j++) {
            fprintf(f_log, "%s%d", (j == 0 ? "" : ","), log->get(i, j));
        }
        fprintf(f_log, "\n");
    }
}

void print_log_reelay(const char *fname, Log *log) {
    char *reelay_log_name = new char[strlen(fname) + 5];
    strcpy(reelay_log_name, fname);
    strcat(reelay_log_name, ".csv");
    FILE *reelay_log_f = fopen(reelay_log_name, "w");

    print_log_reelay_raw(reelay_log_f, log, 1);

    fclose(reelay_log_f);
}

void print_log_r2u2(const char *fname, Log *log) {
    char *r2u2_log_name = new char[strlen(fname) + 5];
    strcpy(r2u2_log_name, fname);
    strcat(r2u2_log_name, ".r2u2");
    FILE *r2u2_log_f = fopen(r2u2_log_name, "w");

    print_log_reelay_raw(r2u2_log_f, log, 0);

    fclose(r2u2_log_f);
}

Log gen_log(int ts_cnt, int er, int delta, int seed, int aps) {
    assert(aps <= ap_cnt);

    std::mt19937 gen;
    gen.seed(seed);

    Log log(ts_cnt * er, aps);

    int ts = 0;
    int line = 0;
    for (int i = 0; i < ts_cnt; i++) {
        for (int j = 0; j < er; j++) {
            log.ts[line] = ts;
            for (int j = 0; j < aps; j++) {
                if (j < 4 && gen() % (er * delta) == 0) continue;
                if (j >= 4 && gen() % 2) continue;
                log.set(line, j);
            }
            line++;
        }
        ts += 1 + gen() % delta;
    }

    return log;
}

#endif /* __LOG_HPP__ */
