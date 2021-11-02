#include <cstdio>
#include <cstdlib>
#include <exception>
#include <stdexcept>

#include "constants.h"
#include "common.h"
#include "formula.h"
#include "parser.h"
#include "lexer.h"
#include "util.h"
#include "visitors.h"

#include "monitor.h"
#include "trie.h"

Formula *getAST(const char *formula)
{
    Formula *fmla;
    yyscan_t scanner;
    YY_BUFFER_STATE state;
 
    if (yylex_init(&scanner)) return NULL;
 
    state = yy_scan_string(formula, scanner);
 
    if (yyparse(&fmla, scanner)) return NULL;
 
    yy_delete_buffer(state, scanner);
    yylex_destroy(scanner);
 
    return fmla;
}

void printUsage()
{
    fprintf(stderr, "hydra MDL LOG [-pure_mdl] [-grep]\n");
    exit(EXIT_FAILURE);
}

void printFmla(Formula *fmla)
{
    printf("Monitoring ");
    PrintHydraFormulaVisitor f(stdout);
    fmla->accept(f);
    printf("\n");
}

struct TimePoint {
    timestamp ts;
    int tp;
    int off;

    TimePoint() : tp(-1) {}
    void update(timestamp new_ts) {
        if (new_ts > ts || tp == -1) {
            off = 0;
        } else {
            off++;
        }
        ts = new_ts;
        tp++;
    }
};
 
int main(int argc, char **argv)
{
    if (argc < 3) {
        printUsage();
    }
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "-pure_mdl")) {
            pure_mdl = 1;
        } else if (!strcmp(argv[i], "-grep")) {
            grep = 1;
        } else {
            printUsage();
        }
    }

    FILE *mtl = fopen(argv[1], "r");
    if (mtl == NULL) {
        fprintf(stderr, "Error: formula file open\n");
        exit(EXIT_FAILURE);
    }

    char *line = NULL;
    size_t length = 0;
    if (getline(&line, &length, mtl) == -1) {
        fprintf(stderr, "Error: formula file read\n");
        exit(EXIT_FAILURE);
    }
    fclose(mtl);
    Formula *fmla;
    try {
        fmla = getAST(line);
    } catch(const std::runtime_error &e) {
        fprintf(stderr, "Error: %s\n", e.what());
        exit(EXIT_FAILURE);
    }
    //if (!grep) printFmla(fmla);
    free(line);

    InputReader *input_reader;

    if (grep) input_reader = new GrepInputReader(argv[2]);
    else input_reader = new MapInputReader(argv[2], &trie);

    MonitorVisitor mv(input_reader);
    fmla->accept(mv);
    Monitor *mon = mv.get_mon();
    TimePoint tp;
    do {
        try {
            BooleanVerdict v = mon->step();
            tp.update(v.ts);
            if (grep) {
                if (v.b == TRUE) printf("%d\n", tp.tp);
            } else if (v.b != UNRESOLVED) {
                printf("%d:%d %s\n", tp.ts, tp.off, (v.b == FALSE ? "false" : "true"));
            }
        } catch (const EOL &e) {
            //if (!grep) printf("Bye.\n");
            break;
        }
    } while(true);

    delete fmla;
    delete mon;
    delete input_reader;

    return 0;
}
