open Verified

exception EXIT

let fmla_ref = ref None
let log_ref = ref None

let usage () = Format.printf
"Usage: vydra -fmla test.mdl -log test.log
Arguments:
  -fmla
    <file> - MDL formula to be monitored\n
  -log
    <file> - log file\n"; raise EXIT

let process_args =
  let rec go = function
    | ("-fmla" :: fmlafile :: args) ->
        fmla_ref := Some fmlafile;
        go args
    | ("-log" :: logfile :: args) ->
        log_ref := Some logfile;
        go args
    | [] -> ()
    | _ -> usage () in
  go

external init: string -> int = "caml_init"
external close_log: unit -> unit = "caml_close"
external run_event: int -> (int * string * string list) option = "caml_run_event"

let _ =
    process_args (List.tl (Array.to_list Sys.argv));
    let f = match !fmla_ref with
      | None -> usage ()
      | Some fname ->
        let ch = open_in fname in
        let f = Mdl_parser.formula Mdl_lexer.token (Lexing.from_channel ch) in
        (close_in ch; f) in
    let init_event = match !log_ref with
      | None -> usage ()
      | Some fname ->
        init fname in
    let enat_of_ts ts = VYDRA.Enat (VYDRA.nat_of_integer (Z.of_string ts)) in
    let run_event e = match run_event e with
      | None -> None
      | Some (e', ts, es) -> Some (e', (enat_of_ts ts, VYDRA.mk_event es)) in
    let output_nat out t = Z.output out (VYDRA.integer_of_nat t) in
    let msz = VYDRA.msize_fmla_vydra f in
    let rec fly vydra (ts, tp) = match VYDRA.run_vydra run_event msz vydra with
      | None -> close_log ()
      | Some (vydra', (et, b)) ->
        let t = match et with
          | VYDRA.Enat t -> t in
        let tp' = match ts with
          | None -> tp
          | Some ts' -> if t = ts' then Z.succ tp else Z.zero in
        let _ = Printf.printf "%a:%a %B\n" output_nat t Z.output tp' b in
        fly vydra' (Some t, tp') in
    fly (VYDRA.sub_vydra init_event run_event msz f) (None, Z.zero)
