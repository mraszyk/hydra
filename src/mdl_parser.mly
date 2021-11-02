%{
open Verified
let inf_in = VYDRA.interval_enat (VYDRA.Enat (VYDRA.nat_of_integer (Z.of_int 0))) VYDRA.Infinity_enat
%}

%token <string> ATOM
%token <Verified.VYDRA.enat Verified.VYDRA.i> INTERVAL
%token LOPEN ROPEN FORWARD BACKWARD
%token FALSE TRUE NEG CONJ DISJ PLUS EOF
%token WILDCARD QUESTION STAR
%token SINCE UNTIL
%token PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS

%nonassoc FALSE TRUE WILDCARD
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
| FALSE                                 { Verified.VYDRA.Bool false }
| TRUE                                  { Verified.VYDRA.Bool true }
| a=ATOM                                { Verified.VYDRA.Atom a }
| a=ATOM LOPEN ROPEN                    { Verified.VYDRA.Atom a }
| NEG f=f                               { Verified.VYDRA.Neg f }
| f=f CONJ g=f                          { Verified.VYDRA.Bin ((fun x y -> x && y), f, g) }
| f=f DISJ g=f                          { Verified.VYDRA.Bin ((fun x y -> x || y), f, g) }
| PREV i=INTERVAL f=f                   { Verified.VYDRA.Prev (i, f) }
| PREV            f=f                   { Verified.VYDRA.Prev (inf_in, f) }
| NEXT i=INTERVAL f=f                   { Verified.VYDRA.Next (i, f) }
| NEXT            f=f                   { Verified.VYDRA.Next (inf_in, f) }
| f=f SINCE i=INTERVAL g=f              { Verified.VYDRA.Since (f, i, g) }
| f=f SINCE            g=f              { Verified.VYDRA.Since (f, inf_in, g) }
| f=f UNTIL i=INTERVAL g=f              { Verified.VYDRA.Until (f, i, g) }
| f=f UNTIL            g=f              { Verified.VYDRA.Until (f, inf_in, g) }
| ONCE i=INTERVAL f=f                   { Verified.VYDRA.Since (Verified.VYDRA.Bool true, i, f) }
| ONCE            f=f                   { Verified.VYDRA.Since (Verified.VYDRA.Bool true, inf_in, f) }
| EVENTUALLY i=INTERVAL f=f             { Verified.VYDRA.Until (Verified.VYDRA.Bool true, i, f) }
| EVENTUALLY            f=f             { Verified.VYDRA.Until (Verified.VYDRA.Bool true, inf_in, f) }
| HISTORICALLY i=INTERVAL f=f           { Verified.VYDRA.Neg (Verified.VYDRA.Since (Verified.VYDRA.Bool true, i, Verified.VYDRA.Neg f)) }
| HISTORICALLY            f=f           { Verified.VYDRA.Neg (Verified.VYDRA.Since (Verified.VYDRA.Bool true, inf_in, Verified.VYDRA.Neg f)) }
| ALWAYS i=INTERVAL f=f                 { Verified.VYDRA.Neg (Verified.VYDRA.Until (Verified.VYDRA.Bool true, i, Verified.VYDRA.Neg f)) }
| ALWAYS            f=f                 { Verified.VYDRA.Neg (Verified.VYDRA.Until (Verified.VYDRA.Bool true, inf_in, Verified.VYDRA.Neg f)) }
| BACKWARD i=INTERVAL r=re              { Verified.VYDRA.MatchP (i, r) } %prec BACKWARD
| BACKWARD            r=re              { Verified.VYDRA.MatchP (inf_in, r) } %prec BACKWARD
| FORWARD i=INTERVAL r=re               { Verified.VYDRA.MatchF (i, r) } %prec FORWARD
| FORWARD            r=re               { Verified.VYDRA.MatchF (inf_in, r) } %prec FORWARD

re:
| LOPEN r=re ROPEN     { r }
| WILDCARD             { Verified.VYDRA.Wild }
| f=f QUESTION         { Verified.VYDRA.Test f }
| r=re PLUS s=re       { Verified.VYDRA.Plus (r, s) }
| r=re      s=re       { Verified.VYDRA.Times (r, s) } %prec CONCAT
| r=re STAR            { Verified.VYDRA.Star r }
