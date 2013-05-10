open Sl
open Util
open Logging

let input_file = ref ""

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noinst] <input file>\n"

let cmd_line_error msg =
  Arg.usage Config.cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input parse_fct file =
  let input = read_file file in
  ParseError.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  SplLexer.set_file_name lexbuf file; 
  parse_fct lexbuf

let vc_gen file =
  let cu = parse_input (fun lexbuf -> SplParser.main SplLexer.token lexbuf) file in
  let _ = Spl2ast.to_program [cu] in
  ()

let current_time () =
  let ptime = Unix.times () in
  ptime.Unix.tms_utime +. ptime.Unix.tms_cutime  

let print_stats start_time =
  if !Config.print_stats then
    let end_time = current_time () in
    let total_time = end_time -. start_time in
    print_endline "Statistics: ";
    Printf.printf "  running time for analysis: %.2fs\n" total_time;
    Printf.printf "  # VCs: %d\n" !SmtLib.num_of_sat_queries

let _ =
  let start_time = current_time () in
  try
    Arg.parse Config.cmd_options (fun s -> input_file := s) usage_message;
    SmtLib.select_solver (String.uppercase !Config.smtsolver);
    if !input_file = ""
    then cmd_line_error "input file missing"
    else (vc_gen !input_file; print_stats start_time)
  with  
  | Sys_error s -> output_string stderr (s ^ "\n"); exit 1
  | Failure s ->
      let bs = if !Debug.verbose then Printexc.get_backtrace () else "" in
        output_string stderr (s ^ "\n" ^ bs); exit 1
  | Parsing.Parse_error -> print_endline "parse error"; exit 1
  | ProgError.Prog_error _ as e -> print_endline (ProgError.to_string e)
	
