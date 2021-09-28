#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>

#define Val_none Val_int(0)

static value Val_some(value v)
{
    CAMLparam1(v);
    CAMLlocal1(some);
    some = caml_alloc(1, 0);
    Store_field(some, 0, v);
    CAMLreturn(some);
}

static int fd;
static size_t f_size;
static const char *mapped;

CAMLprim value caml_init(value ml_fname) {
    CAMLparam1(ml_fname);
    const char *fname = String_val(ml_fname);
    fd = open(fname, O_RDONLY);
    if (fd < 0) {
        fprintf(stderr, "Error: log file cannot be opened\n");
        CAMLreturn(Int_val(-1));
    }
    struct stat f_stat;
    if (fstat(fd, &f_stat)) {
        fprintf(stderr, "Error: fstat cannot be executed on log file\n");
        CAMLreturn(Int_val(-1));
    }
    f_size = f_stat.st_size;
    mapped = (char *)mmap(NULL, f_size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (mapped == MAP_FAILED) {
        fprintf(stderr, "Error: log file cannot be mmapped\n");
        CAMLreturn(Int_val(-1));
    }
    CAMLreturn(Int_val(0));
}

CAMLprim value caml_close(value ml_val) {
    CAMLparam1(ml_val);
    munmap((void *)mapped, f_size);
    close(fd);
    CAMLreturn(Val_unit);
}

static int check_num(char c) {
    return '0' <= c && c <= '9';
}

static int check_alpha(char c) {
    return ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z');
}

static int check_alphanum(char c) {
    return check_alpha(c) || check_num(c);
}

CAMLprim value caml_run_event(value ml_handle) {
    CAMLparam1(ml_handle);
    CAMLlocal4(ret, cli, cons, aux);
    ret = caml_alloc(3, 0);

    size_t pos = Int_val(ml_handle);

    if (pos == -1 || pos == f_size) {
        CAMLreturn(Val_none);
    }
    if (mapped[pos++] != '@') {
        fprintf(stderr, "Error: each event must start with @\n");
        CAMLreturn(Val_none);
    }

    size_t init_pos = pos;
    while (pos < f_size && !(mapped[pos] == ' ' || mapped[pos] == '\r' || mapped[pos] == '\n')) {
        if (!check_num(mapped[pos++])) {
            fprintf(stderr, "Error: timestamp can only consist of decimal digits\n");
            CAMLreturn(Val_none);
        }
    }
    if (pos == init_pos) {
        fprintf(stderr, "Error: timestamp cannot be empty\n");
        CAMLreturn(Val_none);
    }
    char *ts = (char *)malloc(pos - init_pos + 1);
    strncpy(ts, &mapped[init_pos], pos - init_pos);
    ts[pos - init_pos] = 0;
    aux = caml_copy_string(ts);
    free(ts);
    Store_field(ret, 1, aux);

    cli = Val_emptylist;
    while (pos < f_size && !(mapped[pos] == '\r' || mapped[pos] == '\n')) {
        while (pos < f_size && mapped[pos] == ' ') pos++;
        init_pos = pos;
        while (pos < f_size && !(mapped[pos] == ' ' || mapped[pos] == '\r' || mapped[pos] == '\n')) {
            char c = mapped[pos];
            if (pos++ == init_pos) {
                if (!check_alpha(c)) {
                    fprintf(stderr, "Error: atomic proposition must start with a letter\n");
                    CAMLreturn(Val_none);
                }
            } else {
                if (!check_alphanum(c)) {
                    fprintf(stderr, "Error: atomic proposition must consist of alphanumeric characters\n");
                    CAMLreturn(Val_none);
                }
            }
        }
        if (pos != init_pos) {
            char *e = (char *)malloc(pos - init_pos + 1);
            strncpy(e, &mapped[init_pos], pos - init_pos);
            e[pos - init_pos] = 0;
            aux = caml_copy_string(e);
            free(e);
            cons = caml_alloc(2, 0);
            Store_field(cons, 0, aux);
            Store_field(cons, 1, cli);
            cli = cons;
        }
    }
    while (pos < f_size && (mapped[pos] == '\r' || mapped[pos] == '\n')) pos++;

    Store_field(ret, 0, Val_int(pos));
    Store_field(ret, 2, cli);

    CAMLreturn(Val_some(ret));
}
