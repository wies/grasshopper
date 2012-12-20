open SimpleLanguage
open Sl
open Util
open Logging

let input_file = ref ""

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-z3q", Arg.Clear Config.instantiate, "Let z3 deal with quantifiers.")
  ]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-z3q] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input parse_fct file =
  let input = read_file file in
  ParseStmntAux.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseStmntAux.buffer := Some lexbuf;
  parse_fct lexbuf

let vc_gen file =
  let procs = parse_input (fun lexbuf -> ParseSimple.main LexSimple.token lexbuf) file in
  let procMap = List.fold_left (fun acc m -> IdMap.add m.name m acc) IdMap.empty procs in
    List.iter (fun p -> check_procedure procMap p.name) procs


let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = ""
    then cmd_line_error "input file missing"
    else vc_gen !input_file
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> print_endline "parse error"
	
