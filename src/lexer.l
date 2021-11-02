%{

#include "formula.h"
#include "parser.h"
#include "util.h"

#include <exception>
#include <stdexcept>

%}

%option outfile="lexer.cpp" header-file="lexer.h"
%option warn nodefault

%option reentrant noyywrap never-interactive nounistd
%option bison-bridge

LPAREN      \(
RPAREN      \)
 
INTLPAREN   \[
INTRPAREN   \]

NUMBER      [0-9]*
ALPHA       [a-zA-Z$]
ALPHANUMS   [a-zA-Z$0-9_'"]*
WS          [ \r\n\t]*
 
%%
 
{WS}                { continue; }
false               { return TOKEN_FALSE; }
true                { return TOKEN_TRUE; }
NOT                 { return TOKEN_NEG; }
AND                 { return TOKEN_CONJ; }
OR                  { return TOKEN_DISJ; }
PREV                { return TOKEN_PREV; }
NEXT                { return TOKEN_NEXT; }
SINCE               { return TOKEN_SINCE; }
UNTIL               { return TOKEN_UNTIL; }
ONCE                { return TOKEN_ONCE; }
EVENTUALLY          { return TOKEN_EVENTUALLY; }
HISTORICALLY        { return TOKEN_HISTORICALLY; }
ALWAYS              { return TOKEN_ALWAYS; }
◁                   { return TOKEN_MATCH_PAST; }
▷                   { return TOKEN_MATCH_FUTURE; }
◁r                  { return TOKEN_MATCH_CONSUME_PAST; }
▷r                  { return TOKEN_MATCH_CONSUME_FUTURE; }
\?                  { return TOKEN_QUESTION; }
\.                  { return TOKEN_DOT; }
\+                  { return TOKEN_UNION; }
\*                  { return TOKEN_STAR; }
INFINITY            { return TOKEN_INFINITY; }
{LPAREN}            { return TOKEN_LPAREN; }
{RPAREN}            { return TOKEN_RPAREN; }

{ALPHA}{ALPHANUMS}{LPAREN}{RPAREN}  { yylval->name = new char[strlen(yytext) + 10]; strcpy(yylval->name, yytext); return TOKEN_PRED; }
{ALPHA}{ALPHANUMS}  { yylval->name = new char[strlen(yytext) + 10]; strcpy(yylval->name, yytext); return TOKEN_PRED; }
{NUMBER}            { if (parseNumber(yytext, NULL, &yylval->value)) throw std::runtime_error("interval bounds"); return TOKEN_NUMBER; }
{INTLPAREN}         { return TOKEN_INTLPAREN; }
,                   { return TOKEN_SEP; }
{INTRPAREN}         { return TOKEN_INTRPAREN; }

.                   { throw std::runtime_error("unexpected character"); }
 
%%
