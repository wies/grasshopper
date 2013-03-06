open Logger
open Form
open FormUtil
open ParseSmtLibAux

let logger = Logging.smtlib_log

(* Todo: add proper error handling *)

(** Solvers *)

type solver_version = 
    { number : int;
      subnumber : int;
      smt_options : (string * bool) list;
      args : string
    }

type solver = 
    { name : string;
      cmnd : string;
      version : solver_version
    }
      

let z3_v3 = { number = 3;
	      subnumber = 2;
	      smt_options = [":mbqi", true;
			 ":MODEL_V2", true;
			 ":MODEL_PARTIAL", true;
			 ":MODEL_HIDE_UNUSED_PARTITIONS", true];
	      args = "-smt2 -in"
	    }

let z3_v4 = { number = 4;
	      subnumber = 3;
	      smt_options = [":smt.mbqi", true;
			     ":model.v2", true;
			     ":model.partial", true];
	      args = "-smt2 -in"
	    }

let z3_versions = [z3_v4; z3_v3]

let z3 = 
  let cmnd = "z3" in
  let version = 
    try 
      let in_chan = Unix.open_process_in (cmnd ^ " -version") in
      let version_regexp = Str.regexp "^Z3[^0-9]*\\([0-9]*\\).\\([0-9]*\\)" in
      let version_string = input_line in_chan in
      ignore (Str.string_match version_regexp version_string 0);
      let number = int_of_string (Str.matched_group 1 version_string) in
      let subnumber = int_of_string (Str.matched_group 2 version_string) in
      let _ = Unix.close_process_in in_chan in
      List.find (fun v -> v.number < number || (v.number = number && v.subnumber <= subnumber)) z3_versions
    with _ -> log logger WARN (fun () -> "No supported version of Z3 found.", []);
      z3_v3	
  in 
  { name = "Z3";
    cmnd = cmnd;
    version = version }

let cvc4_v1 = {	number = 1;
		subnumber = 0;
		smt_options = [];
		args = "--lang=smt2";
	      } 

let cvc4 = 
  { name = "CVC4";
    cmnd = "cvc4";
    version = cvc4_v1 }

let mathsat_v5 = { number = 5;
		 subnumber = 1;
		 smt_options = [":produce-interpolants", true];
		 args = "-verbosity=0 -interpolation=true";
	       }

let mathsat = 
  { name = "MathSAT";
    cmnd = "mathsat";
    version = mathsat_v5
   }
 
let solvers = [z3; cvc4; mathsat]

let selected_solver = ref z3

let selected_interpolator = ref mathsat

let select_solver name = 
  try
    selected_solver := List.find (fun s -> s.name = name) solvers
  with Not_found -> failwith ("Unsupported SMT solver '" ^ name ^ "'")

(** SMT-LIB2 Sessions *)
   
type session = { name: string;
                 init: bool;
		 in_chan: in_channel;
		 out_chan: out_channel;
		 replay_chan: out_channel option;
		 mutable assert_count: int;
		 mutable sat_checked: bool;
		 stack_height: int
	       } 

exception SmtLib_error of session * string
    
let fail session msg = raise (SmtLib_error (session, "SmtLib: " ^ msg))
      
let write session cmd =
  output_string session.out_chan cmd;
  match session.replay_chan with
  | Some chan -> output_string chan cmd; flush chan
  | None -> ()	

let writefn session fn =
  fn session.out_chan;
  match session.replay_chan with
  | Some chan -> fn chan; flush chan
  | None -> ()

let writeln session cmd = 
  write session (cmd ^ "\n")  
   
let read session = 
  flush session.out_chan;
  let lexbuf = Lexing.from_channel session.in_chan in
  ParseSmtLib.main LexSmtLib.token lexbuf

let declare_sorts session =
  writeln session ("(declare-sort " ^ loc_sort_string ^ " 0)");
  writeln session ("(declare-sort " ^ set_sort_string ^ " 1)");
  if !Config.encode_fields_as_arrays then
    writeln session ("(define-sort " ^ fld_sort_string ^ " (X) (Array Loc X))")
  else 
    writeln session ("(declare-sort " ^ fld_sort_string ^ " 1)")

let start_with_solver = 
  let get_replay_chan name =
    if !Debug.verbose then
      (* these files should probably go into the tmp directory *)
      let with_version = fresh_ident name in
      let replay_file =  (str_of_ident with_version) ^ ".smt" in
      Some (open_out replay_file)
    else None
  in
  fun session_name solver produce_models produce_interpolants ->
  let smt_cmd = solver.cmnd ^ " " ^ solver.version.args in
  let in_chan, out_chan = Unix.open_process smt_cmd in
  let session = { name = session_name;
                  init = true; 
		  in_chan = in_chan; 
		  out_chan = out_chan;
		  replay_chan = get_replay_chan session_name;
		  assert_count = 0;
                  sat_checked = false;
		  stack_height = 0 }
  in
  writeln session "(set-option :print-success false)";
  if produce_models then begin
    writeln session "(set-option :produce-models true)";
    (*writeln session "(set-option :produce-unsat-cores true)"*)
  end;
  if produce_interpolants then writeln session "(set-option :produce-interpolants true)";
  List.iter 
    (fun (opt, b) -> writeln session (Printf.sprintf "(set-option %s %b)" opt b))
    solver.version.smt_options;
  (*
  if false && !Config.instantiate then
    writeln session "(set-logic QF_UF)"
  else
    begin
  *)
  if !Config.encode_fields_as_arrays
  then writeln session "(set-logic AUFLIA)"
  else writeln session "(set-logic UF)";
  (*end;*)
  declare_sorts session;
  session

let start session_name = start_with_solver session_name !selected_solver true false
    
let start_interpolation session_name = start_with_solver session_name !selected_interpolator false true
    
let quit session = 
  writeln session "(exit)";
  close_out session.out_chan;
  close_in session.in_chan;
  (match session.replay_chan with
  | Some chan -> close_out chan
  | None -> ());
  ignore (Unix.close_process (session.in_chan, session.out_chan));
  { session with init = false }
    
let pop session = 
  if session.stack_height <= 0 then fail session "pop on empty stack" else
  writeln session "(pop 1)";
  let new_session = { session with stack_height = session.stack_height - 1 } in
  new_session

let push session = 
  writeln session "(push 1)";
  let new_session = { session with stack_height = session.stack_height + 1 } in
  new_session

let declare session sign =
  let write_decl sym (arg_sorts, res_sort) = 
    match sym with
    (* Skip inbuilt symbols *)
    | Read 
    | Write when !Config.encode_fields_as_arrays -> () 
    | Eq -> ()
    | _ ->
	let arg_sorts_str = String.concat " " (List.map (fun srt -> string_of_sort srt) arg_sorts) in
	writeln session ("(declare-fun " ^ str_of_symbol sym ^ " (" ^ arg_sorts_str ^ ") " ^ string_of_sort res_sort ^ ")")
  in
  SymbolMap.iter write_decl sign;
  writeln session ""

let assert_form session f =
  session.assert_count <- session.assert_count + 1;
  session.sat_checked <- false;
    (* print_string "(assert ";
       print_smtlib_form stdout f;
       print_endline ")"; *)
  write session "(assert ";
  let cf = mk_comment ("_" ^ string_of_int session.assert_count) f in
  writefn session (fun chan -> 
    Format.fprintf (Format.formatter_of_out_channel chan) "@[<8>%a@]@?" pr_form cf);
  writeln session ")\n"
    
(*let assert_form session f = Util.measure (assert_form session) f*)
    
let assert_forms session fs =
  List.iter (fun f -> assert_form session f) fs

    
let is_sat session = 
  writeln session "(check-sat)";
  match read session with
  | SmtSat -> 
    session.sat_checked <- true;
    Some true
  | SmtUnsat -> Some false
  | SmtUnknown ->
    session.sat_checked <- true;
    None
  | SmtError e -> fail session e
  | _ -> fail session "unexpected response of prover"
	
let get_model session = 
  let gm () =
    writeln session "(get-model)";
    match read session with
    | SmtModel m -> Some m
    | SmtError e -> fail session e
    | _ -> None
  in
    if session.sat_checked then gm ()
    else
      match is_sat session with
      | Some true | None -> gm ()
      | Some false -> None
	  
let get_interpolant session groups =
  match is_sat session with
  | Some true | None -> None
  | Some false ->
      begin
	let a = String.concat " " (List.map string_of_int groups) in
	writeln session ("(get-interpolant (" ^ a ^ "))");
	match read session with
	| SmtError e -> fail session e
	| SmtForm f -> Some f
	| _ -> None
      end



  


