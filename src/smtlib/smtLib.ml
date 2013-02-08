open Form
open FormUtil
open ParseSmtLibAux

(* Todo: add proper error handling *)

type session = { init: bool;
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
  writeln session ("(define-sort " ^ fld_sort_string ^ " (X) (Array Loc X))")

let start smt_cmd replay_file produce_models produce_interpolants = 
  let in_chan, out_chan = Unix.open_process smt_cmd in
  let replay_chan = 
    match replay_file with
    | Some filename -> Some (open_out filename)
    | None -> None
  in
  let session = { init = true; 
		  in_chan = in_chan; 
		  out_chan = out_chan;
		  replay_chan = replay_chan;
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
  (*
  if false && !Config.instantiate then
    writeln session "(set-logic QF_UF)"
  else
    begin
  *)
  writeln session "(set-option :mbqi true)";
  writeln session "(set-logic AUFLIA)";
  (*end;*)
  declare_sorts session;
  session

let start_z3 =
  let cnt = ref 0 in
  let replay_file () =
    if !Debug.verbose then
      begin
        cnt := !cnt + 1;
        Some ("z3_" ^ (string_of_int !cnt) ^ ".in")
      end
    else None
  in
    (fun () -> start "z3 -smt2 -ini:z3.ini -in" (replay_file ()) true false)
    
(*let start_z3 replay_file = start "z3 -smt2 -ini:z3.ini -in" replay_file true false*)
      
let start_mathsat replay_file = start "mathsat -verbosity=0 -interpolation=true" replay_file false true
    
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
    | Select | Store | Eq -> ()
    | _ ->
	let arg_sorts_str = String.concat " " (List.map (fun srt -> string_of_sort srt) arg_sorts) in
	writeln session ("(declare-fun " ^ str_of_symbol sym ^ " (" ^ arg_sorts_str ^ ") " ^ string_of_sort res_sort ^ ")")
  in
  SymbolMap.iter write_decl sign

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
    
let assert_form session f = Util.measure (assert_form session) f
    
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



  


