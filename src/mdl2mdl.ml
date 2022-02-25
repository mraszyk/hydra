open Verified.VYDRA

exception EXIT

let usage () = Format.printf "Usage: mdl2mdl MDLhydra MDLaerial MDLmonpoly\n"; raise EXIT

let check_and op = (op true true) && not (op true false) && not (op false true) && not (op false false)
let check_or op = (op true true) && (op true false) && (op false true) && not (op false false)

let nat_to_string n = Z.to_string (integer_of_nat n)

let print_int_aux print_enat i = match rep_interval_enat i with (l, (r, (b1, b2))) ->
  (if b1 then "[" else "(") ^
  print_enat l ^ ", " ^ print_enat r ^
  (if b2 then "]" else ")")

let rec print_mdl ctrue cfalse catom cinf =
  let print_enat = function
  | Enat n -> nat_to_string n
  | Infinity_enat -> cinf in
  let print_int = print_int_aux print_enat in
  let rec aux = function
  | Bool b -> if b then ctrue else cfalse
  | Atom a -> a ^ catom
  | Neg f -> "(NOT " ^ aux f ^ ")"
  | Bin (op, f, g) ->
    let opname = (if check_and op then " AND " else (assert (check_or op); " OR ")) in
    "(" ^ aux f ^ opname ^ aux g ^ ")"
  | Prev (i, f) -> "(PREV" ^ print_int i ^ " " ^ aux f ^ ")"
  | Next (i, f) -> "(NEXT" ^ print_int i ^ " " ^ aux f ^ ")"
  | Since (f, i, g) -> "(" ^ aux f ^ " SINCE" ^ print_int i ^ " " ^ aux g ^ ")"
  | Until (f, i, g) -> "(" ^ aux f ^ " UNTIL" ^ print_int i ^ " " ^ aux g ^ ")"
  | MatchP (i, r) -> "(◁ " ^ print_int i ^ " " ^ foo r ^ ")"
  | MatchF (i, r) -> "(▷ " ^ print_int i ^ " " ^ foo r ^ ")"
  and foo = function
  | Lookahead f -> "(" ^ aux f ^ "?)"
  | Symbol f -> aux f
  | Plus (r, s) -> "(" ^ foo r ^ " + " ^ foo s ^ ")"
  | Times (r, s) -> "(" ^ foo r ^ " " ^ foo s ^ ")"
  | Star r -> "(" ^ foo r ^ "*)"
  in aux

let print_mdl_hydra = print_mdl "true" "false" "" "INFINITY"

let rec print_mdl' ctrue cfalse catom cinf =
  let print_enat = function
  | Enat n -> nat_to_string n
  | Infinity_enat -> cinf in
  let print_int = print_int_aux print_enat in
  let rec aux = function
  | Boola b -> if b then ctrue else cfalse
  | Atoma a -> a ^ catom
  | Nega f -> "(NOT " ^ aux f ^ ")"
  | Bina (op, f, g) ->
    let opname = (if check_and op then " AND " else (assert (check_or op); " OR ")) in
    "(" ^ aux f ^ opname ^ aux g ^ ")"
  | Preva (i, f) -> "(PREV" ^ print_int i ^ " " ^ aux f ^ ")"
  | Nexta (i, f) -> "(NEXT" ^ print_int i ^ " " ^ aux f ^ ")"
  | Sincea (f, i, g) -> "(" ^ aux f ^ " SINCE" ^ print_int i ^ " " ^ aux g ^ ")"
  | Untila (f, i, g) -> "(" ^ aux f ^ " UNTIL" ^ print_int i ^ " " ^ aux g ^ ")"
  | MatchPa (i, r) -> "(◁ " ^ print_int i ^ " " ^ foo r ^ ")"
  | MatchFa (i, r) -> "(▷ " ^ print_int i ^ " " ^ foo r ^ ")"
  and foo = function
  | Test f -> "(" ^ aux f ^ "?)"
  | Wild -> "."
  | Plusa (r, s) -> "(" ^ foo r ^ " + " ^ foo s ^ ")"
  | Timesa (r, s) -> "(" ^ foo r ^ " " ^ foo s ^ ")"
  | Stara r -> "(" ^ foo r ^ "*)"
  in aux

let print_mdl_aerial = print_mdl' "true" "false" "" "INFINITY"
let print_mdl_monpoly = print_mdl' "TRUE" "FALSE" "()" "*"

let _ = try
    let args = List.tl (Array.to_list Sys.argv) in
    let _ = if List.length args <> 3 then usage () else () in
    let f =
        (let ch = open_in (List.nth args 0) in
        let f = Mdl_parser.input Mdl_lexer.token (Lexing.from_channel ch) in
        (close_in ch; f)) in
    let _ =
        (let ch = open_out (List.nth args 1) in
        let _ = Printf.fprintf ch "%s\n" (print_mdl_aerial (mdl2mdl_enat f)) in
        close_out ch) in
    let _ =
        (let ch = open_out (List.nth args 2) in
        let _ = Printf.fprintf ch "%s\n" (print_mdl_monpoly (mdl2mdl_enat f)) in
        close_out ch) in ()
    with Sys_error _ -> ()
