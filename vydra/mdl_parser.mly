%{
open Verified
%}

%token <string> ATOM
%token <Verified.VYDRA.enat Verified.VYDRA.i> INTERVAL
%token LOPEN ROPEN FORWARD BACKWARD
%token FALSE TRUE NEG CONJ DISJ PLUS IMP IFF EOF
%token WILDCARD QUESTION STAR
%token SINCE UNTIL
%token PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS

%nonassoc TRUE FALSE WILDCARD
%right IFF
%right IMP
%nonassoc BACKWARD FORWARD
%nonassoc PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS
%left SINCE UNTIL
%left DISJ
%left CONJ
%left PLUS
%left CONCAT
%nonassoc NEG
%nonassoc STAR
%nonassoc LOPEN
%nonassoc QUESTION
%nonassoc INTERVAL
%nonassoc ATOM

%type <(string, Verified.VYDRA.enat) Verified.VYDRA.formula> formula
%start formula

%%

formula:
| f=f EOF { f }

f:
| LOPEN f=f ROPEN                       { f }
| TRUE                                  { Verified.VYDRA.Bool true }
| FALSE                                 { Verified.VYDRA.Bool false }
| f=f CONJ g=f                          { Verified.VYDRA.Bin ((fun x y -> x && y), f, g) }
| f=f DISJ g=f                          { Verified.VYDRA.Bin ((fun x y -> x || y), f, g) }
| NEG f=f                               { Verified.VYDRA.Neg f }
| a=ATOM                                { Verified.VYDRA.Atom a }
| a=ATOM LOPEN ROPEN                    { Verified.VYDRA.Atom a }
| PREV i=INTERVAL f=f                   { Verified.VYDRA.Prev (i, f) }
| NEXT i=INTERVAL f=f                   { Verified.VYDRA.Next (i, f) }
| f=f SINCE i=INTERVAL g=f              { Verified.VYDRA.Since (f, i, g) }
| f=f UNTIL i=INTERVAL g=f              { Verified.VYDRA.Until (f, i, g) }
| FORWARD i=INTERVAL r=reF              { Verified.VYDRA.MatchF (i, r) } %prec FORWARD
| BACKWARD i=INTERVAL r=reP             { Verified.VYDRA.MatchP (i, r) } %prec BACKWARD

reF:
| LOPEN r=reF ROPEN     { r }
| WILDCARD              { Verified.VYDRA.Wild }
| f=f QUESTION          { Verified.VYDRA.Test f }
| r=reF PLUS s=reF      { Verified.VYDRA.Plus (r, s) }
| r=reF s=reF           { Verified.VYDRA.Times (r, s) } %prec CONCAT
| r=reF STAR            { Verified.VYDRA.Star r }

reP:
| LOPEN r=reP ROPEN     { r }
| WILDCARD              { Verified.VYDRA.Wild }
| f=f QUESTION          { Verified.VYDRA.Test f }
| r=reP PLUS s=reP      { Verified.VYDRA.Plus (r, s) }
| r=reP s=reP           { Verified.VYDRA.Times (r, s) } %prec CONCAT
| r=reP STAR            { Verified.VYDRA.Star r }
