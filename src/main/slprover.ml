open Form
open FormUtil
open Axioms
open Util
open Logging

let input_file = ref []

type mode =
  | SlSat
  | SlEntails
  | SlFrame

let mode = ref SlSat

let cmd_options =
   ("-entails", Arg.Unit (fun () -> mode := SlEntails), "check entailment") ::
   ("-frame", Arg.Unit (fun () -> mode := SlFrame), "frame inference") ::
   Config.cmd_options

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [...] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_given_input parse_fct file =
  let input = read_file file in
  ParseError.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  parse_fct lexbuf

let parse_input parse_fct =
  let file = List.hd !input_file in
    parse_given_input parse_fct file

let heap = fresh_ident "D"

let compute_sl_sat () =
  (*print_endline "parsing";*)
  let sl = parse_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) in
  let _ = Debug.msg ("parsed: " ^ (Sl.string_of_form sl) ^ "\n") in
  let form = ToGrass.to_grass heap sl in
  let _ = if !Debug.verbose then
    begin
      print_endline "converted: ";
      print_form stdout form
    end
  in
  (*print_endline "to prover";*)
  let res = Prover.check_sat form in
    Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time;
    match res with
    | Some true -> print_endline "sat"
    | Some false -> print_endline "unsat"
    | None -> print_endline "unknown"

(* check that sp(pre, path) |= post *)
let compute_sl_entails () =
  let pre_sl  = parse_given_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) (List.nth !input_file 0) in
  let post_sl = parse_given_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) (List.nth !input_file 1) in
  let res = Entails.check_entailment pre_sl post_sl in
    Util.print_measures ();
    match res with
    | Some true -> print_endline "not entailed"
    | Some false -> print_endline "entailed"
    | None -> print_endline "unknown"

(* A |= B * frame *)
let compute_sl_frame () =
  let pre_sl  = parse_given_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) (List.nth !input_file 0) in
  let post_sl = parse_given_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) (List.nth !input_file 1) in
  let res = Frame.infer_frame pre_sl post_sl in
    Util.print_measures ();
    match res with
    | Some frames ->
      print_endline "frames:";
      List.iter (fun frame -> print_endline ("  " ^ (Sl.string_of_form frame))) frames
    | None -> print_endline "Error not entailed!"

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s :: !input_file) usage_message;
    input_file := List.rev !input_file;
    if !input_file = [] then cmd_line_error "input file missing" else
      begin
        Printexc.print (fun () ->
          match !mode with
          | SlSat -> compute_sl_sat ()
          | SlEntails -> compute_sl_entails ()
          | SlFrame -> compute_sl_frame ()
        ) ()
      end
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s ->
      let bs = if !Debug.verbose then Printexc.get_backtrace () else "" in
        output_string stderr (s ^ "\n" ^ bs)
  | Parsing.Parse_error -> print_endline "parse error"
	
    
