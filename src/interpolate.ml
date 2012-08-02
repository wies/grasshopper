open Form
open Stmnt
open Axioms
open Util
open Logging

let input_file = ref ""

type mode =
  | Interpolate
  | SlSat

let mode = ref Interpolate

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Axioms.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-alloc", Arg.Set Axioms.with_alloc_axioms, "Add axioms for alloc predicate");
   ("-nojoin", Arg.Clear Axioms.with_jp_axioms, "Do not add axioms for join functions");
   ("-sl", Arg.Unit (fun () -> mode := SlSat), "SL satisfiability")
  ]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input parse_fct =
  let ch = open_in !input_file in
  let path = 
    try 
      let lexbuf = Lexing.from_channel ch in
      parse_fct lexbuf
    with e -> close_in ch; raise e
  in
  close_in ch; path

let compute_interpolant () =
  let path = parse_input (fun lexbuf -> ParseStmnt.main LexStmnt.token lexbuf) in
  let pf_a, pf_b = path_form path in
  (* let _ = if !Debug.verbose then print_forms stdout [mk_and pf_a; mk_and pf_b] in *)
  let interpolant = Prover.interpolate pf_a pf_b in
  let _ = Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time in
  print_form stdout interpolant

let compute_sl_sat () =
  (*print_endline "parsing";*)
  let sl = parse_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) in
  let _ = Debug.msg ("parsed: " ^ (Sl.to_string sl) ^ "\n") in
  let sln = Sl.normalize sl in
  let _ = Debug.msg ("normalized: " ^ (Sl.to_string sln) ^ "\n") in
  let form = Sl.to_form sln in
  let _ = if !Debug.verbose then
    begin
      print_endline "converted: ";
      print_form stdout form
    end
  in
  (*print_endline "to prover";*)
  let res = Prover.satisfiable form in
    Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time;
    match res with
    | Some true -> print_endline "sat"
    | Some false -> print_endline "unsat"
    | None -> print_endline "unknown"

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = "" then cmd_line_error "input file missing" else
      begin
        match !mode with
        | Interpolate -> compute_interpolant ()
        | SlSat -> compute_sl_sat ()
      end
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> print_endline "parse error"
	
    
