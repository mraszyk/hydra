{
open Mdl_parser
open Verified

(* lexing/parsing errors *)
open Lexing
exception ParsingError_ of position*position*string
exception ParsingError of string

let parsing_error i j fmt = Format.kasprintf (fun s -> raise (ParsingError_(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (lexeme_start_p lexbuf) (lexeme_end_p lexbuf) fmt
}

let num = ['0'-'9']*
let alpha = ['a'-'z''A'-'Z']
let alphanums = ['a'-'z''A'-'Z''0'-'9']*
let blank = [' ''\r''\n''\t']*

rule token = parse
  | blank                                         { token lexbuf }
  | "false"                                       { FALSE }
  | "true"                                        { TRUE }
  | "NOT"                                         { NEG }
  | "AND"                                         { CONJ }
  | "OR"                                          { DISJ }
  | "PREV"                                        { PREV }
  | "NEXT"                                        { NEXT }
  | "SINCE"                                       { SINCE }
  | "UNTIL"                                       { UNTIL }
  | "ONCE"                                        { ONCE }
  | "EVENTUALLY"                                  { EVENTUALLY }
  | "PAST_ALWAYS"                                 { PAST_ALWAYS }
  | "ALWAYS"                                      { ALWAYS }
  | "◁"                                           { BACKWARD }
  | "▷"                                           { FORWARD }
  | "?"                                           { QUESTION }
  | "."                                           { DOT }
  | "+"                                           { PLUS }
  | "*"                                           { STAR }
  | "INFINITY"                                    { INFINITY }
  | "("                                           { OPEN }
  | ")"                                           { CLOSE }

  | (alpha alphanums) as name "()"?               { ATOM name }
  | num as n                                      { NUMBER (VYDRA.nat_of_integer (Z.of_string n)) }
  | "["                                           { INTOPEN }
  | ","                                           { SEP }
  | "]"                                           { INTCLOSE }

  | eof                                           { EOF }
  | _ as c                                        { lexing_error lexbuf "unexpected character" c }
