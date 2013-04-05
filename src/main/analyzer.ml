open SimpleLanguage
open VcGen
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
  parse_fct lexbuf

let vc_gen file =
  let procs = parse_input (fun lexbuf -> ParseSimple.main LexSimple.token lexbuf) file in
  let procMap = List.fold_left (fun acc m -> IdMap.add m.name m acc) IdMap.empty procs in
    List.iter (fun p -> check_procedure procMap p.name) procs

let _ =
  try
    Arg.parse Config.cmd_options (fun s -> input_file := s) usage_message;
    SmtLib.select_solver (String.uppercase !Config.smtsolver);
    if !input_file = ""
    then cmd_line_error "input file missing"
    else vc_gen !input_file
  with  
  | Sys_error s -> output_string stderr (s ^ "\n"); exit 1
  | Failure s ->
      let bs = if !Debug.verbose then Printexc.get_backtrace () else "" in
        output_string stderr (s ^ "\n" ^ bs); exit 1
  | Parsing.Parse_error -> print_endline "parse error"; exit 1
	
