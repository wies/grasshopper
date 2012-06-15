open Form

module SmtLib = struct
  open ParseSmtLibAux
  (* Todo: add proper error handline *)
    
  type session = { init: bool;
		   in_chan: in_channel;
		   out_chan: out_channel;
		   stack_height: int
		 } 

  exception SmtLib_error of session * string
      
  let fail session msg = raise (SmtLib_error (session, "SmtLib: " ^ msg))

  let smt_cmd = "z3 -smt2 -ini:z3.ini -in"

  let write session cmd = 
    (* print_endline cmd; *)
    output_string session.out_chan (cmd ^ "\n")
 
   
  let read session = 
    flush session.out_chan;
    let lexbuf = Lexing.from_channel session.in_chan in
    ParseSmtLib.main LexSmtLib.token lexbuf

  let start () = 
    let in_chan, out_chan = Unix.open_process smt_cmd in
    let session = { init = true; 
		    in_chan = in_chan; 
		    out_chan = out_chan;
		    stack_height = 0 }
    in
    write session "(set-option :print-success false)";
    write session "(set-logic QF_UF)";
    write session ("(declare-sort " ^ sort_str ^ ")");
    session

  let quit session = 
    write session "(exit)";
    close_out session.out_chan;
    close_in session.in_chan;
    ignore (Unix.close_process (session.in_chan, session.out_chan));
    { session with init = false }

  let pop session = 
    if session.stack_height <= 0 then fail session "pop on empty stack" else
    write session "(pop 1)";
    let new_session = { session with stack_height = session.stack_height - 1 } in
    new_session

  let push session = 
    write session "(push 1)";
    let new_session = { session with stack_height = session.stack_height + 1 } in
    new_session

  let declare session sign =
    let write_decl id decl = 
      let res_sort = if decl.is_pred then "bool" else sort_str in
      let arg_sorts = String.concat " " (Util.generate_list (fun _ -> sort_str) decl.arity) in
      write session ("(declare-fun " ^ str_of_ident id ^ " (" ^ arg_sorts ^ ") " ^ res_sort ^ ")")
    in
    IdMap.iter write_decl sign

  let assert_form session f =
    (* print_string "(assert ";
    print_smtlib_form stdout f;
    print_endline ")"; *)
    output_string session.out_chan "(assert ";
    print_smtlib_form session.out_chan f;
    output_string session.out_chan ")\n"
     
  let assert_forms session fs =
    List.iter (assert_form session) fs
    

  let is_sat session = 
    write session "(check-sat)";
    match read session with
    | SmtSat -> Some true
    | SmtUnsat -> Some false
    | SmtUnknown -> None
    | SmtError e -> fail session e
    | _ -> fail session "unexpected response of prover"

  let get_model session = 
    match is_sat session with
    | Some true | None ->
	begin
	  write session "(get-info model)";
	  match read session with
	  | SmtModel m -> Some (Axioms.simplify_model m)
	  | SmtError e -> fail session e
	  | _ -> None
	end
    | Some false -> None

end

let use_csisat = ref false

let csisat_interpolate_cmd = "csisat" 
let mathsat_interpolate_cmd outfile = "mathsat -input=foci -tsolver=euf -verbosity=0 -interpolate=" ^ outfile

let interp_file_prefix = "interpol"
let interp_file_name = interp_file_prefix ^ ".1.msat"

let get_model f =
  let session = SmtLib.start () in
  try 
    SmtLib.declare session (sign f);
    SmtLib.assert_form session f;
    let model = SmtLib.get_model session in 
    ignore (SmtLib.quit session); 
    model
  with SmtLib.SmtLib_error (session, e) -> 
    ignore (SmtLib.quit session); 
    failwith e

  
let get_interpolant_csisat a b = 
  let out_ch = Unix.open_process_out csisat_interpolate_cmd in
  print_forms out_ch [a; b];
  close_out out_ch;
  ignore (Unix.close_process_out out_ch);
  None

let get_interpolant_mathsat a b =
  let cmd = mathsat_interpolate_cmd interp_file_prefix in
  let in_ch, out_ch = Unix.open_process cmd in
  print_forms out_ch [a; b];
  close_out out_ch;
  let interpolant =
    if input_line in_ch = "unsat" then begin
      let interp_in = open_in interp_file_name in
      let lexbuf = Lexing.from_channel interp_in in
      let interpolant = ParseMSATForm.main LexMSATForm.token lexbuf in
      close_in interp_in;
      Unix.unlink interp_file_name;
      Some interpolant
    end 
    else None
  in
  close_in in_ch;
  ignore (Unix.close_process (in_ch, out_ch));
  interpolant

let get_interpolant a b =
  if !use_csisat then get_interpolant_csisat a b
  else get_interpolant_mathsat a b
  


