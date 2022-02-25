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

OPEN        \(
CLOSE       \)
 
INTOPEN     \[
INTCLOSE    \]

NUMBER      [0-9]*
ALPHA       [a-zA-Z]
ALPHANUMS   [a-zA-Z0-9]*
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
PAST_ALWAYS         { return TOKEN_PAST_ALWAYS; }
ALWAYS              { return TOKEN_ALWAYS; }
◁                   { return TOKEN_BACKWARD; }
▷                   { return TOKEN_FORWARD; }
\?                  { return TOKEN_QUESTION; }
\.                  { return TOKEN_DOT; }
\+                  { return TOKEN_PLUS; }
\*                  { return TOKEN_STAR; }
INFINITY            { return TOKEN_INFINITY; }
{OPEN}              { return TOKEN_OPEN; }
{CLOSE}             { return TOKEN_CLOSE; }

{ALPHA}{ALPHANUMS}{OPEN}{CLOSE}  { yylval->name = new char[strlen(yytext) + 1]; strcpy(yylval->name, yytext); yylval->name[strlen(yytext) - 2] = 0; return TOKEN_ATOM; }
{ALPHA}{ALPHANUMS}  { yylval->name = new char[strlen(yytext) + 1]; strcpy(yylval->name, yytext); return TOKEN_ATOM; }
{NUMBER}            { if (parseNumber(yytext, NULL, &yylval->value)) throw std::runtime_error("interval bounds"); return TOKEN_NUMBER; }
{INTOPEN}           { return TOKEN_INTOPEN; }
,                   { return TOKEN_SEP; }
{INTCLOSE}          { return TOKEN_INTCLOSE; }

.                   { throw std::runtime_error("unexpected character"); }
 
%%
