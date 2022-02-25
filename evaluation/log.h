#ifndef __LOG_HPP__
#define __LOG_HPP__

#include <cassert>
#include <cstdio>
#include <cstring>
#include <random>

#include "formula.h"

static int ap_cnt = 101;

Formula *new_ap(int i) {
  assert(i < 100);
  char *name = new char[66];
  sprintf(name, "a%02d", i);
  return new AtomFormula(name, i, 1);
}

void print_ap(FILE *f, const char *sep, int i) {
  if (i == ap_cnt - 1) {
    fprintf(f, "%se", sep);
  } else {
    fprintf(f, "%sa%02d", sep, i);
  }
}

Formula *new_eof() {
  static const char *name = "e";
  return new AtomFormula(name, ap_cnt - 1);
}

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
            if (log->get(i, j)) print_ap(f_log, " ", j);
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
            if (log->get(i, j)) {
              print_ap(f_log, " ", j);
              fprintf(f_log, "()");
            }
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
            print_ap(f_log, (i == 0 ? "" : ","), i);
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

Log gen_log(int len, int er, int delta, int seed, int aps, int hi = 4, int last = 0) {
    assert(aps <= ap_cnt);

    std::mt19937 gen;
    gen.seed(seed);

    Log log(len + last, aps);

    int ts = 0;
    int line = 0;

    while (line < len) {
        for (int j = 0; j < er && line < len; j++) {
            log.ts[line] = ts;
            for (int j = 0; j < aps; j++) {
                if (j < hi && gen() % er == 0) continue;
                if (j >= hi && gen() % 2) continue;
                log.set(line, j);
            }
            line++;
        }
        ts += 1 + gen() % delta;
    }
    if (last) log.ts[len] = ts;

    return log;
}

#endif /* __LOG_HPP__ */
