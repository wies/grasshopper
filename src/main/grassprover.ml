open Form
open FormUtil
open Axioms
open Util
open Logging

let input_file = ref None

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Config.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-alloc", Arg.Set Config.with_alloc_axioms, "Add axioms for alloc predicate");
   ("-z3q", Arg.Clear Config.instantiate, "Let z3 deal with quantifiers.")
  ]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

(*
let parse_input parse_fct file =
  ParseError.input := Some input_file;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  parse_fct lexbuf

let parse_input parse_fct =
  let file = List.hd !input_file in
    parse_given_input parse_fct file
*)

let process_input () =
  (*let sl = parse_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) in
  let _ = Debug.msg ("parsed: " ^ (Sl.to_string sl) ^ "\n") in*)
  let fld1 = mk_free_const ~srt:(Fld Loc) (fresh_ident "f") in
  let fld2 = mk_free_const ~srt:(Fld Loc) (fresh_ident "g") in
  let loc1 = mk_free_const ~srt:Loc (fresh_ident "x") in
  let loc2 = mk_free_const ~srt:Loc (fresh_ident "y") in
  let loc3 = mk_free_const ~srt:Loc (fresh_ident "z") in
  let form = 
    mk_and 
      [mk_eq (mk_write fld1 loc1 loc2) fld2;
       mk_eq (mk_read fld1 loc3) loc1;
       mk_reachwo fld1 loc1 loc2 loc3] 
  in
  let _ = if!Debug.verbose then
    print_forms stdout [form] 
  in
  (*print_endline "to prover";*)
  let res = Prover.check_sat form in
  (* Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time;*)
  match res with
  | Some true -> print_endline "sat"
  | Some false -> print_endline "unsat"
  | None -> print_endline "unknown"
  
let repl input_file =
  let input, ch = 
    match input_file with
    | None -> None, stdin
    | Some file_name -> Some (read_file file_name), open_in file_name
  in
  let lexbuf = Lexing.from_channel ch in 
  let rec loop context =
    print_endline "Parse command";
    ParseError.input := input;
    ParseError.buffer := Some lexbuf;
    let next_cmnd = ParseGrass.main LexGrass.token lexbuf in
    match next_cmnd with
    | Grass.Skip 
    | Grass.DeclareFun _ -> loop context
    | Grass.Exit -> ()
    | Grass.Assert f -> loop (f :: context)
    | Grass.CheckSat -> 
	let res = Prover.check_sat (smk_and (List.rev context)) in
	(match res with
	| Some true -> print_endline "sat"
	| Some false -> print_endline "unsat"
	| None -> print_endline "unknown");
	loop context
    | Grass.GetModel -> print_endline "get-model is currently unsupported. Command ignored."
  in loop []

	
let _ =
  let print_exception s =
    output_string stderr (s ^ "\n");
    if !Debug.verbose then
      Printexc.print_backtrace stderr
  in
  try
    Arg.parse cmd_options (fun s -> input_file := Some s) usage_message;
    repl !input_file
  with  
  | Sys_error s
  | Failure s -> print_exception s
  | Parsing.Parse_error -> print_exception "Parse error"
	
    
