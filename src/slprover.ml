open Form
open Stmnt
open Axioms
open Util
open Logging

let input_file = ref ""

type mode =
  | SlSat
  | SlEntails
  | SlFrame

let mode = ref SlSat

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Axioms.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-alloc", Arg.Set Axioms.with_alloc_axioms, "Add axioms for alloc predicate");
   ("-nojoin", Arg.Clear Axioms.with_jp_axioms, "Do not add axioms for join functions");
   ("-entails", Arg.Unit (fun () -> mode := SlEntails), "check entailment");
   ("-frame", Arg.Unit (fun () -> mode := SlFrame), "frame inference");
   ("-z3q", Arg.Clear Config.instantiate, "Let z3 deal with quantifiers.")
  ]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let parse_input parse_fct =
  let input = read_file !input_file in
  ParseStmntAux.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseStmntAux.buffer := Some lexbuf;
  parse_fct lexbuf

let compute_sl_sat () =
  let heap = mk_ident "h" in
  (*print_endline "parsing";*)
  let sl = parse_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) in
  let _ = Debug.msg ("parsed: " ^ (Sl.to_string sl) ^ "\n") in
  let sln = Sl.normalize sl in
  let _ = Debug.msg ("normalized: " ^ (Sl.to_string sln) ^ "\n") in
  let form = Sl.to_form_tight heap sln in
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

(* check that sp(pre, path) |= post *)
let compute_sl_entails () =
  let (pre_sl, path, post_sl) = parse_input (fun lexbuf -> ParseSl2.main LexSl2.token lexbuf) in
  let path_wo_label = List.filter (function Label _ -> false | _ -> true) path in
  let res = Entails.check_entailment pre_sl path_wo_label post_sl in
    Util.print_measures ();
    match res with
    | Some true -> print_endline "not entailed"
    | Some false -> print_endline "entailed"
    | None -> print_endline "unknown"

(* A |= B * frame *)
let compute_sl_frame () =
  let (pre_sl, path, post_sl) = parse_input (fun lexbuf -> ParseSl2.main LexSl2.token lexbuf) in
  let path_wo_label = List.filter (function Label _ -> false | _ -> true) path in
  let res = FrameInference.infer_frame pre_sl path_wo_label post_sl in
    Util.print_measures ();
    match res with
    | Some frames ->
      print_endline "frames:";
      List.iter (fun frame -> print_endline ("  " ^ (Sl.to_string frame))) frames
    | None -> print_endline "Error not entailed!"

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = "" then cmd_line_error "input file missing" else
      begin
        match !mode with
        | SlSat -> compute_sl_sat ()
        | SlEntails -> compute_sl_entails ()
        | SlFrame -> compute_sl_frame ()
      end
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> print_endline "parse error"
	
    
