/* A Bison parser, made by GNU Bison 3.3.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2019 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Undocumented macros, especially those whose name start with YY_,
   are private implementation details.  Do not rely on them.  */

#ifndef YY_YY_PARSER_H_INCLUDED
# define YY_YY_PARSER_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif
/* "%code requires" blocks.  */
#line 19 "parser.y" /* yacc.c:1921  */

    typedef void *yyscan_t;

#line 52 "parser.h" /* yacc.c:1921  */

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TOKEN_INFINITY = 258,
    TOKEN_TRUE = 259,
    TOKEN_FALSE = 260,
    TOKEN_NEG = 261,
    TOKEN_CONJ = 262,
    TOKEN_DISJ = 263,
    TOKEN_IMP = 264,
    TOKEN_IFF = 265,
    TOKEN_SINCE = 266,
    TOKEN_UNTIL = 267,
    TOKEN_PREV = 268,
    TOKEN_NEXT = 269,
    TOKEN_MATCH_PAST = 270,
    TOKEN_MATCH_CONSUME_PAST = 271,
    TOKEN_MATCH_FUTURE = 272,
    TOKEN_ONCE = 273,
    TOKEN_EVENTUALLY = 274,
    TOKEN_HISTORICALLY = 275,
    TOKEN_ALWAYS = 276,
    TOKEN_LPAREN = 277,
    TOKEN_RPAREN = 278,
    TOKEN_QUESTION = 279,
    TOKEN_DOT = 280,
    TOKEN_UNION = 281,
    TOKEN_CONSUME_UNION = 282,
    TOKEN_STAR = 283,
    TOKEN_PRED = 284,
    TOKEN_NUMBER = 285,
    TOKEN_INTLPAREN = 286,
    TOKEN_SEP = 287,
    TOKEN_INTRPAREN = 288
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 31 "parser.y" /* yacc.c:1921  */

    char *name;
    timestamp value;
    interval in;
    Formula *fmla;
    Regex *regex;
    ConsumeRegex *cregex;

#line 107 "parser.h" /* yacc.c:1921  */
};

typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif



int yyparse (Formula **fmla, yyscan_t scanner);

#endif /* !YY_YY_PARSER_H_INCLUDED  */
