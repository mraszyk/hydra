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
    Formula *fmla;
    Regex *regex;
    ConsumeRegex *cregex;
}

%token TOKEN_FALSE "FALSE"
%token TOKEN_TRUE "TRUE"
%token TOKEN_NEG "NOT"
%token TOKEN_CONJ "AND"
%token TOKEN_DISJ "OR"
%token TOKEN_PREV "PREV"
%token TOKEN_NEXT "NEXT"
%token TOKEN_SINCE "SINCE"
%token TOKEN_UNTIL "UNTIL"
%token TOKEN_ONCE "ONCE"
%token TOKEN_EVENTUALLY "EVENTUALLY"
%token TOKEN_HISTORICALLY "HISTORICALLY"
%token TOKEN_ALWAYS "ALWAYS"
%token TOKEN_MATCH_PAST "MATCH_PAST"
%token TOKEN_MATCH_FUTURE "MATCH_FUTURE"
%token TOKEN_MATCH_CONSUME_PAST "MATCH_CONSUME_PAST"
%token TOKEN_MATCH_CONSUME_FUTURE "MATCH_CONSUME_FUTURE"
%token TOKEN_QUESTION "?"
%token TOKEN_DOT "."
%token TOKEN_UNION "UNION"
%token TOKEN_STAR "STAR"
%token TOKEN_INFINITY "INF"
%token TOKEN_LPAREN "("
%token TOKEN_RPAREN ")"

%token <name> TOKEN_PRED "PRED"
%token <value> TOKEN_NUMBER "NUM"
%token TOKEN_INTLPAREN "["
%token TOKEN_SEP ","
%token TOKEN_INTRPAREN "]"

%type <value> number
%type <value> infnumber
%type <in> interval
%type <fmla> formula
%type <regex> regex
%type <cregex> cregex

%nonassoc "FALSE" "TRUE" "DOT"
%nonassoc "MATCH_PAST" "MATCH_FUTURE" "MATCH_CONSUME_PAST" "MATCH_CONSUME_FUTURE"
%nonassoc "PREV" "NEXT" "ONCE" "EVENTUALLY" "HISTORICALLY" "ALWAYS"
%left "SINCE" "UNTIL"
%left "DISJ"
%left "CONJ"
%left "PLUS"
%left "CONCAT"
%nonassoc "NOT"
%nonassoc "STAR"
%nonassoc "LOPEN"
%nonassoc "QUESTION"
%nonassoc "INTERVAL"
%nonassoc "PRED"

%%
 
input
    : formula { *fmla = $1; }
    ;

number
    : "NUM" { $$ = $1; }
    ;

infnumber
    : "NUM" { $$ = $1; }
    | "INF" { $$ = MAX_TIMESTAMP; }
    ;

interval
    : "[" number[l] "," infnumber[r] "]" { $$ = {$l, $r}; }
    ;

regex
    : formula[f] "?" { $$ = new TestRegex($f); }
    | "." { $$ = new WildCardRegex(); }
    | regex[left] "UNION" regex[right] { $$ = new OrRegex($left, $right); }
    | regex[left] regex[right] { $$ = new ConcatRegex($left, $right); }
    | regex[body] "STAR" { $$ = new StarRegex($body); }
    | "(" regex[r] ")" { $$ = $r; }
    ;

cregex
    : formula[f] { $$ = new AtomicConsumeRegex($f); }
    | cregex[left] "UNION" cregex[right] { $$ = new OrConsumeRegex($left, $right); }
    | cregex[left] cregex[right] { $$ = new ConcatConsumeRegex($left, $right); }
    | cregex[body] "STAR" { $$ = new StarConsumeRegex($body); }
    | "(" cregex[r] ")" { $$ = $r; }
    ;

formula
    : "FALSE" { $$ = new BoolFormula(false); }
    | "TRUE" { $$ = new BoolFormula(true); }
    | "PRED" { $$ = new PredFormula($1, trie.getOrAdd($1), 1); }
    | "NOT" formula[f] { $$ = new NegFormula($f); }
    | formula[f] "AND" formula[g] { $$ = new AndFormula($f, $g); }
    | formula[f] "OR" formula[g] { $$ = new OrFormula($f, $g); }
    | "PREV" interval[in] formula[f] {
        if (pure_mdl) {
          $$ = new BwFormula(new ConcatRegex(new TestRegex($f), new WildCardRegex()), $in);
        } else {
          $$ = new PrevFormula($f, $in);
        }
      }
    | "PREV" formula[f] {
        if (pure_mdl) {
          $$ = new BwFormula(new ConcatRegex(new TestRegex($f), new WildCardRegex()), inf_in);
        } else {
          $$ = new PrevFormula($f, inf_in);
        }
      }
    | "NEXT" interval[in] formula[f] {
        if (pure_mdl) {
          $$ = new FwFormula(new ConcatRegex(new WildCardRegex(), new TestRegex($f)), $in);
        } else {
          $$ = new NextFormula($f, $in);
        }
      }
    | "NEXT" formula[f] {
        if (pure_mdl) {
          $$ = new FwFormula(new ConcatRegex(new WildCardRegex(), new TestRegex($f)), inf_in);
        } else {
          $$ = new NextFormula($f, inf_in);
        }
      }
    | formula[f] "SINCE" interval[in] formula[g] {
        if (pure_mdl) {
          $$ = new BwFormula(new ConcatRegex(new TestRegex($g), new StarRegex(new ConcatRegex(new WildCardRegex(), new TestRegex($f)))), $in);
        } else {
          $$ = new SinceFormula($f, $g, $in);
        }
      }
    | formula[f] "SINCE" formula[g] {
        if (pure_mdl) {
          $$ = new BwFormula(new ConcatRegex(new TestRegex($g), new StarRegex(new ConcatRegex(new WildCardRegex(), new TestRegex($f)))), inf_in);
        } else {
          $$ = new SinceFormula($f, $g, inf_in);
        }
      }
    | formula[f] "UNTIL" interval[in] formula[g] {
        if (pure_mdl) {
          $$ = new FwFormula(new ConcatRegex(new StarRegex(new ConcatRegex(new TestRegex($f), new WildCardRegex())), new TestRegex($g)), $in);
        } else {
          $$ = new UntilFormula($f, $g, $in);
        }
      }
    | formula[f] "UNTIL" formula[g] {
        if (pure_mdl) {
          $$ = new FwFormula(new ConcatRegex(new StarRegex(new ConcatRegex(new TestRegex($f), new WildCardRegex())), new TestRegex($g)), inf_in);
        } else {
          $$ = new UntilFormula($f, $g, inf_in);
        }
      }
    | "ONCE" interval[in] formula[f] {
        if (pure_mdl) {
          $$ = new BwFormula(new ConcatRegex(new TestRegex($f), new StarRegex(new WildCardRegex())), $in);
        } else {
          $$ = new SinceFormula(new BoolFormula(true), $f, $in);
        }
      }
    | "ONCE" formula[f] {
        if (pure_mdl) {
          $$ = new BwFormula(new ConcatRegex(new TestRegex($f), new StarRegex(new WildCardRegex())), inf_in);
        } else {
          $$ = new SinceFormula(new BoolFormula(true), $f, inf_in);
        }
      }
    | "EVENTUALLY" interval[in] formula[f] {
        if (pure_mdl) {
          $$ = new FwFormula(new ConcatRegex(new StarRegex(new WildCardRegex()), new TestRegex($f)), $in);
        } else {
          $$ = new UntilFormula(new BoolFormula(true), $f, $in);
        }
      }
    | "EVENTUALLY" formula[f] {
        if (pure_mdl) {
          $$ = new FwFormula(new ConcatRegex(new StarRegex(new WildCardRegex()), new TestRegex($f)), inf_in);
        } else {
          $$ = new UntilFormula(new BoolFormula(true), $f, inf_in);
        }
      }
    | "HISTORICALLY" interval[in] formula[f] {
        if (pure_mdl) {
          $$ = new NegFormula(new BwFormula(new ConcatRegex(new TestRegex(new NegFormula($f)), new StarRegex(new WildCardRegex())), $in));
        } else {
          $$ = new NegFormula(new SinceFormula(new BoolFormula(true), new NegFormula($f), $in));
        }
      }
    | "HISTORICALLY" formula[f] {
        if (pure_mdl) {
          $$ = new NegFormula(new BwFormula(new ConcatRegex(new TestRegex(new NegFormula($f)), new StarRegex(new WildCardRegex())), inf_in));
        } else {
          $$ = new NegFormula(new SinceFormula(new BoolFormula(true), new NegFormula($f), inf_in));
        }
      }
    | "ALWAYS" interval[in] formula[f] {
        if (pure_mdl) {
          $$ = new NegFormula(new FwFormula(new ConcatRegex(new StarRegex(new WildCardRegex()), new TestRegex(new NegFormula($f))), $in));
        } else {
          $$ = new NegFormula(new UntilFormula(new BoolFormula(true), new NegFormula($f), $in));
        }
      }
    | "ALWAYS" formula[f] {
        if (pure_mdl) {
          $$ = new NegFormula(new FwFormula(new ConcatRegex(new StarRegex(new WildCardRegex()), new TestRegex(new NegFormula($f))), inf_in));
        } else {
          $$ = new NegFormula(new UntilFormula(new BoolFormula(true), new NegFormula($f), inf_in));
        }
      }
    | "MATCH_PAST" interval[in] regex[r]    { $$ = new BwFormula($r, $in); }
    | "MATCH_PAST" regex[r]                 { $$ = new BwFormula($r, inf_in); }
    | "MATCH_PAST" number[delta] regex[r]   { $$ = new BwOneFormula($r, $delta); }
    | "MATCH_FUTURE" interval[in] regex[r]  { $$ = new FwFormula($r, $in); }
    | "MATCH_FUTURE" regex[r]               { $$ = new FwFormula($r, inf_in); }
    | "MATCH_FUTURE" number[delta] regex[r] { $$ = new FwOneFormula($r, $delta); }
    | "MATCH_CONSUME_PAST" interval[in] cregex[r]   { $$ = new BwConsumeFormula($r, $in); }
    | "MATCH_CONSUME_PAST" cregex[r]                { $$ = new BwConsumeFormula($r, inf_in); }
    | "MATCH_CONSUME_FUTURE" interval[in] cregex[r] { $$ = new FwConsumeFormula($r, $in); }
    | "MATCH_CONSUME_FUTURE" cregex[r]              { $$ = new FwConsumeFormula($r, inf_in); }
    | "(" formula[f] ")" { $$ = $f; }
    ;
 
%%
