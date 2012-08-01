open Form
open Stmnt
open Axioms
open Util
open Logging

let input_file = ref ""

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Axioms.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-alloc", Arg.Set Axioms.with_alloc_axioms, "Add axioms for alloc predicate");
   ("-nojoin", Arg.Clear Axioms.with_jp_axioms, "Do not add axioms for join functions")]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input () =
  let ch = open_in !input_file in
  let path = 
    try 
      let lexbuf = Lexing.from_channel ch in
      ParseStmnt.main LexStmnt.token lexbuf
    with e -> close_in ch; raise e
  in
  close_in ch; path

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = "" then cmd_line_error "input file missing" else
      let path = parse_input () in
      let pf_a, pf_b = path_form path
      in
      (* let _ = if !Debug.verbose then print_forms stdout [mk_and pf_a; mk_and pf_b] in *)
      let interpolant = Prover.interpolate pf_a pf_b
      in
      let _ = Printf.fprintf stdout "accumulated time: %.2fs\n"  !Util.measured_time in
      print_form stdout interpolant
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> print_endline "parse error"
	
    
