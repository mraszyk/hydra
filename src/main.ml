open Const
open Verified

exception EXIT

let usage () = Format.printf "Usage: vydra MDL LOG [-mdlaerial]\n"; raise EXIT

external init: string -> int = "caml_init"
external run: int -> (int * string * string list) option = "caml_run"
external close: unit -> unit = "caml_close"

let rec process_args = function
  | x :: xs ->
    let _ = if x = "-mdlaerial" then mdlaerial := true else () in
    process_args xs
  | [] -> ()

let _ =
    let args = List.tl (Array.to_list Sys.argv) in
    let _ = if List.length args < 2 then usage () else process_args (List.tl (List.tl args)) in
    let f =
        (let ch = open_in (List.nth args 0) in
        let f = Mdl_parser.input Mdl_lexer.token (Lexing.from_channel ch) in
        (close_in ch; f)) in
    let init_hd = init (List.nth args 1) in
    let enat_of_ts ts = VYDRA.Enat (VYDRA.nat_of_integer (Z.of_string ts)) in
    let run_hd e = match run e with
      | None -> None
      | Some (e', ts, es) -> Some (e', (enat_of_ts ts, VYDRA.mk_db es)) in
    let output_nat out t = Z.output out (VYDRA.integer_of_nat t) in
    let rec fly vydra (ts, tp) = match VYDRA.run_vydra_string_enat run_hd vydra with
      | None -> close ()
      | Some (vydra', (et, b)) ->
        let t = match et with
          | VYDRA.Enat t -> t in
        let tp' = match ts with
          | None -> tp
          | Some ts' -> if t = ts' then Z.succ tp else Z.zero in
        let _ = Printf.printf "%a:%a %B\n" output_nat t Z.output tp' b in
        fly vydra' (Some t, tp') in
    fly (VYDRA.init_vydra_string_enat init_hd run_hd f) (None, Z.zero)
