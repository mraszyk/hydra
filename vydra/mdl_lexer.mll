{
open Mdl_parser
open Verified

(* lexing/parsing errors *)
open Lexing
exception ParsingError_ of position*position*string
exception ParsingError of string

let parsing_error i j fmt = Format.kasprintf (fun s -> raise (ParsingError_(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (lexeme_start_p lexbuf) (lexeme_end_p lexbuf) fmt

let lex_interval l r =
  let ls = (VYDRA.nat_of_integer (Z.of_string l)) in
  (match r with
    | "INFINITY" -> VYDRA.enat_interval (VYDRA.Enat ls) VYDRA.Infinity_enat
    | _ -> VYDRA.enat_interval (VYDRA.Enat ls) (VYDRA.Enat (VYDRA.nat_of_integer (Z.of_string r))))
}

let blank = [' ' '\t' ]+
let newline = ['\r' '\n' ] | "\r\n"
let num = ['0'-'9' ]+
let alpha = ['a'-'z' 'A'-'Z']
let alphanums = ['a'-'z' 'A'-'Z' '0'-'9' ]*

rule token = parse
  | newline                                       { Lexing.new_line lexbuf; token lexbuf }
  | blank                                         { token lexbuf }
  | "false"                                       { FALSE }
  | "true"                                        { TRUE }
  | "NOT"                                         { NEG }
  | "AND"                                         { CONJ }
  | "OR"                                          { DISJ }
  | "IMPLIES"                                     { IMP }
  | "EQUIV"                                       { IFF }
  | "SINCE"                                       { SINCE }
  | "UNTIL"                                       { UNTIL }
  | "PREV"                                        { PREV }
  | "NEXT"                                        { NEXT }
  | "ONCE"                                        { ONCE }
  | "EVENTUALLY"                                  { EVENTUALLY }
  | "HISTORICALLY"                                { HISTORICALLY }
  | "ALWAYS"                                      { ALWAYS }
  | "("                                           { LOPEN }
  | ")"                                           { ROPEN }
  | "▷"                                           { FORWARD }
  | "◁"                                           { BACKWARD }
  | "?"                                           { QUESTION }
  | "."                                           { WILDCARD }
  | "+"                                           { PLUS }
  | "*"                                           { STAR }
  | (alpha alphanums)  as name "()"?              { ATOM name }
  | '[' blank* (num as l) blank* "," blank* ((num | "INFINITY") as r) blank* ']'
                                                  { INTERVAL (lex_interval l r) }
  | eof                                           { EOF }
  | _ as c                                        { lexing_error lexbuf "unexpected character: `%c'" c }
