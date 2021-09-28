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
INFINITY            { return TOKEN_INFINITY; }
true                { return TOKEN_TRUE; }
false               { return TOKEN_FALSE; }
NOT                 { return TOKEN_NEG; }
AND                 { return TOKEN_CONJ; }
OR                  { return TOKEN_DISJ; }
IMPLIES             { return TOKEN_IMP; }
EQUIV               { return TOKEN_IFF; }
SINCE               { return TOKEN_SINCE; }
UNTIL               { return TOKEN_UNTIL; }
PREV                { return TOKEN_PREV; }
NEXT                { return TOKEN_NEXT; }
◁r                  { return TOKEN_MATCH_CONSUME_PAST; }
◁                   { return TOKEN_MATCH_PAST; }
▷                   { return TOKEN_MATCH_FUTURE; }
ONCE                { return TOKEN_ONCE; }
EVENTUALLY          { return TOKEN_EVENTUALLY; }
HISTORICALLY        { return TOKEN_HISTORICALLY; }
ALWAYS              { return TOKEN_ALWAYS; }
{LPAREN}            { return TOKEN_LPAREN; }
{RPAREN}            { return TOKEN_RPAREN; }
\?                  { return TOKEN_QUESTION; }
\.                  { return TOKEN_DOT; }
\+                  { return TOKEN_UNION; }
\|                  { return TOKEN_CONSUME_UNION; }
\*                  { return TOKEN_STAR; }

{ALPHA}{ALPHANUMS}{LPAREN}{RPAREN}  { yylval->name = new char[strlen(yytext) + 10]; strcpy(yylval->name, yytext); return TOKEN_PRED; }
{ALPHA}{ALPHANUMS}  { yylval->name = new char[strlen(yytext) + 10]; strcpy(yylval->name, yytext); return TOKEN_PRED; }
{NUMBER}            { if (parseNumber(yytext, NULL, &yylval->value)) throw std::runtime_error("interval bounds"); return TOKEN_NUMBER; }
{INTLPAREN}         { return TOKEN_INTLPAREN; }
,                   { return TOKEN_SEP; }
{INTRPAREN}         { return TOKEN_INTRPAREN; }

.                   { throw std::runtime_error("unexpected character"); }
 
%%
