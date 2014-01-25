open Sl
open Util
open Logging

let input_file = ref ""

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " <input file> [options]\n"

let cmd_line_error msg =
  Arg.usage Config.cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input file =
  let input = read_file file in
  ParseError.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  ParseError.parse_buf_exn ParseModel.main LexModel.token lexbuf

let vizmodel file =
  let model = parse_input file in
  let model_chan = open_out !Config.model_file in
  Model.print_model2 model;
  Model.output_graphviz model_chan model;
  close_out model_chan  

let _ =
  try
    Arg.parse Config.cmd_options (fun s -> input_file := s) usage_message;
    SmtLib.select_solver (String.uppercase !Config.smtsolver);
    if !input_file = ""
    then cmd_line_error "input file missing"
    else vizmodel !input_file
  with  
  | Sys_error s -> 
      output_string stderr (s ^ "\n"); 
      exit 1
  | Failure s ->
      let bs = if Debug.is_debug () then Printexc.get_backtrace () else "" in
      output_string stderr (s ^ "\n" ^ bs); exit 1
  | Parsing.Parse_error -> 
      print_endline "parse error"; 
      exit 1
  | ProgError.Prog_error _ as e ->
      output_string stderr (ProgError.to_string e ^ "\n");
      exit 1
	
