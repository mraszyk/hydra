%{

#include "constants.h"
#include "formula.h"
#include "parser.h"
#include "lexer.h"
#include "trie.h"
#include "util.h"

#include <exception>
#include <stdexcept>

int yyerror(Formula **fmla, yyscan_t scanner, const char *msg) {
    throw std::runtime_error("parsing");
}

%}

%code requires {
    typedef void *yyscan_t;
}

%output  "parser.cpp"
%defines "parser.h"
 
%define api.pure
%lex-param   { yyscan_t scanner }
%parse-param { Formula **fmla }
%parse-param { yyscan_t scanner }

%union {
    char *name;
    timestamp value;
    interval in;
    Regex *regex;
    Formula *fmla;
}

%token TOKEN_FALSE "FALSE"
%token TOKEN_TRUE "TRUE"
%token TOKEN_NEG "NEG"
%token TOKEN_CONJ "CONJ"
%token TOKEN_DISJ "DISJ"
%token TOKEN_PREV "PREV"
%token TOKEN_NEXT "NEXT"
%token TOKEN_SINCE "SINCE"
%token TOKEN_UNTIL "UNTIL"
%token TOKEN_ONCE "ONCE"
%token TOKEN_EVENTUALLY "EVENTUALLY"
%token TOKEN_PAST_ALWAYS "PAST_ALWAYS"
%token TOKEN_ALWAYS "ALWAYS"
%token TOKEN_BACKWARD "BACKWARD"
%token TOKEN_FORWARD "FORWARD"
%token TOKEN_QUESTION "QUESTION"
%token TOKEN_DOT "DOT"
%token TOKEN_PLUS "PLUS"
%token TOKEN_STAR "STAR"
%token TOKEN_INFINITY "INFINITY"
%token TOKEN_OPEN "OPEN"
%token TOKEN_CLOSE "CLOSE"

%token <name> TOKEN_ATOM "ATOM"
%token <value> TOKEN_NUMBER "NUM"
%token TOKEN_INTOPEN "INTOPEN"
%token TOKEN_SEP "SEP"
%token TOKEN_INTCLOSE "INTCLOSE"

%type <value> number
%type <value> infnumber
%type <in> interval
%type <regex> regex
%type <fmla> formula

%nonassoc "BACKWARD" "FORWARD"

%right "SINCE" "UNTIL"
%nonassoc "PREV" "NEXT" "ONCE" "EVENTUALLY" "PAST_ALWAYS" "ALWAYS"
%nonassoc "NEG"
%left "DISJ"
%left "CONJ"
%nonassoc "FALSE" "TRUE" "ATOM"

%left "PLUS"
%left "CONCAT"
%nonassoc "SYMBOL"
%nonassoc "QUESTION" "DOT" "STAR"

%nonassoc "OPEN" "CLOSE"

%%
 
input
    : formula { *fmla = $1; }
    ;

number
    : "NUM" { $$ = $1; }
    ;

infnumber
    : "NUM" { $$ = $1; }
    | "INFINITY" { $$ = MAX_TIMESTAMP; }
    ;

interval
    : %empty                                             { $$ = {0, MAX_TIMESTAMP}; }
    | "INTOPEN" number[l] "SEP" infnumber[r] "INTCLOSE"  { $$ = {$l, $r}; }
    | "INTCLOSE" number[l] "SEP" infnumber[r] "INTOPEN"  { $$ = {$l + 1, $r - 1}; }
    | "INTOPEN" number[l] "SEP" infnumber[r] "INTOPEN"   { $$ = {$l, $r - 1}; }
    | "INTCLOSE" number[l] "SEP" infnumber[r] "INTCLOSE" { $$ = {$l + 1, $r}; }
    ;

regex
    : formula[f] "QUESTION"                             { $$ = new LookaheadRegex($f); }
    | formula[f] %prec "SYMBOL"                         { $$ = new SymbolRegex($f); }
    | "DOT"                                             { $$ = new SymbolRegex(new BoolFormula(true)); }
    | regex[r] "PLUS" regex[s]                          { $$ = new PlusRegex($r, $s); }
    | regex[r] regex[s] %prec "CONCAT"                  { $$ = new TimesRegex($r, $s); }
    | regex[r] "STAR"                                   { $$ = new StarRegex($r); }
    | "OPEN" regex[r] "CLOSE"                           { $$ = $r; }
    ;

formula
    : "FALSE"                                           { $$ = new BoolFormula(false); }
    | "TRUE"                                            { $$ = new BoolFormula(true); }
    | "ATOM"                                            { $$ = new AtomFormula($1, trie.getOrAdd($1), 1); }
    | "NEG" formula[f]                                  { $$ = new NegFormula($f); }
    | formula[f] "CONJ" formula[g]                      { $$ = new AndFormula($f, $g); }
    | formula[f] "DISJ" formula[g]                      { $$ = new OrFormula($f, $g); }
    | "PREV" interval[i] formula[f]                     { $$ = new PrevFormula($f, $i); }
    | "NEXT" interval[i] formula[f]                     { $$ = new NextFormula($f, $i); }
    | formula[f] "SINCE" interval[i] formula[g]         { $$ = new SinceFormula($f, $g, $i); }
    | formula[f] "UNTIL" interval[i] formula[g]         { $$ = new UntilFormula($f, $g, $i); }
    | "ONCE" interval[i] formula[f]                     { $$ = new SinceFormula(new BoolFormula(true), $f, $i); }
    | "EVENTUALLY" interval[i] formula[f]               { $$ = new UntilFormula(new BoolFormula(true), $f, $i); }
    | "PAST_ALWAYS" interval[i] formula[f]              { $$ = new NegFormula(new SinceFormula(new BoolFormula(true), new NegFormula($f), $i)); }
    | "ALWAYS" interval[i] formula[f]                   { $$ = new NegFormula(new UntilFormula(new BoolFormula(true), new NegFormula($f), $i)); }
    | "BACKWARD" interval[i] regex[r] %prec "BACKWARD"  { $$ = new BwFormula(mdlaerial ? new TimesRegex($r, new SymbolRegex(new BoolFormula(true))) : $r, $i); }
    | "FORWARD" interval[i] regex[r] %prec "FORWARD"    { $$ = new FwFormula(mdlaerial ? new TimesRegex($r, new SymbolRegex(new BoolFormula(true))) : $r, $i); }
    | "OPEN" formula[f] "CLOSE"                         { $$ = $f; }
    ;
 
%%
