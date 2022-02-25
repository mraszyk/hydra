%{
open Const
open Verified
%}

%token FALSE
%token TRUE
%token NEG
%token CONJ
%token DISJ
%token PREV
%token NEXT
%token SINCE
%token UNTIL
%token ONCE
%token EVENTUALLY
%token PAST_ALWAYS
%token ALWAYS
%token BACKWARD
%token FORWARD
%token QUESTION
%token DOT
%token PLUS
%token STAR
%token INFINITY
%token OPEN
%token CLOSE
%token EOF

%token <string> ATOM
%token <Verified.VYDRA.nat> NUMBER
%token INTOPEN
%token SEP
%token INTCLOSE

%nonassoc BACKWARD FORWARD

%right SINCE UNTIL
%nonassoc PREV NEXT ONCE EVENTUALLY PAST_ALWAYS ALWAYS
%nonassoc NEG
%left DISJ
%left CONJ
%nonassoc FALSE TRUE ATOM

%left PLUS
%left CONCAT
%nonassoc SYMBOL
%nonassoc QUESTION DOT STAR

%nonassoc OPEN CLOSE

%type <(string, VYDRA.enat) VYDRA.formula> input
%start input

%%

input:
  | f=formula EOF { f }

number:
  | n=NUMBER { n }

infnumber:
  | n=NUMBER { VYDRA.Enat n }
  | INFINITY { VYDRA.Infinity_enat }

interval:
  |                                            { VYDRA.interval_enat (VYDRA.Enat (VYDRA.nat_of_integer (Z.of_int 0))) VYDRA.Infinity_enat true true }
  | INTOPEN l=number SEP r=infnumber INTCLOSE  { VYDRA.interval_enat (VYDRA.Enat l) r true true }
  | INTCLOSE l=number SEP r=infnumber INTOPEN  { VYDRA.interval_enat (VYDRA.Enat l) r false false }
  | INTOPEN l=number SEP r=infnumber INTOPEN   { VYDRA.interval_enat (VYDRA.Enat l) r true false }
  | INTCLOSE l=number SEP r=infnumber INTCLOSE { VYDRA.interval_enat (VYDRA.Enat l) r false true }

regex:
  | f=formula QUESTION                        { VYDRA.Lookahead f }
  | f=formula                                 { VYDRA.Symbol f } %prec SYMBOL
  | DOT                                       { VYDRA.Symbol (VYDRA.Bool true) }
  | r=regex PLUS s=regex                      { VYDRA.Plus (r, s) }
  | r=regex s=regex                           { VYDRA.Times (r, s) } %prec CONCAT
  | r=regex STAR                              { VYDRA.Star r }
  | OPEN r=regex CLOSE                        { r }

formula:
  | FALSE                                     { VYDRA.Bool false }
  | TRUE                                      { VYDRA.Bool true }
  | a=ATOM                                    { VYDRA.Atom a }
  | NEG f=formula                             { VYDRA.Neg f }
  | f=formula CONJ g=formula                  { VYDRA.Bin ((fun x y -> x && y), f, g) }
  | f=formula DISJ g=formula                  { VYDRA.Bin ((fun x y -> x || y), f, g) }
  | PREV i=interval f=formula                 { VYDRA.Prev (i, f) }
  | NEXT i=interval f=formula                 { VYDRA.Next (i, f) }
  | f=formula SINCE i=interval g=formula      { VYDRA.Since (f, i, g) }
  | f=formula UNTIL i=interval g=formula      { VYDRA.Until (f, i, g) }
  | ONCE i=interval f=formula                 { VYDRA.Since (VYDRA.Bool true, i, f) }
  | EVENTUALLY i=interval f=formula           { VYDRA.Until (VYDRA.Bool true, i, f) }
  | PAST_ALWAYS i=interval f=formula          { VYDRA.Neg (VYDRA.Since (VYDRA.Bool true, i, VYDRA.Neg f)) }
  | ALWAYS i=interval f=formula               { VYDRA.Neg (VYDRA.Until (VYDRA.Bool true, i, VYDRA.Neg f)) }
  | BACKWARD i=interval r=regex               { VYDRA.MatchP (i, if !mdlaerial then VYDRA.Times (r, VYDRA.Symbol (VYDRA.Bool true)) else r) } %prec BACKWARD
  | FORWARD i=interval r=regex                { VYDRA.MatchF (i, if !mdlaerial then VYDRA.Times (r, VYDRA.Symbol (VYDRA.Bool true)) else r) } %prec FORWARD
  | OPEN f=formula CLOSE                      { f }
