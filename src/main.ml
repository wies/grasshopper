open Form
open Stmnt
open Axioms
open Util
open Logging

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Axioms.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-nojoin", Arg.Clear Axioms.with_jp_axioms, "Do not add axioms for join functions")]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

let input_file = ref ""

let parse_input () =
  let ch = open_in !input_file in
  let path = 
    try 
      let lexbuf = Lexing.from_channel ch in
      ParseStmnt.main LexStmnt.token lexbuf
    with e -> close_in ch; raise e
  in
  close_in ch; path

let compare_forms =
  let cons_re = Str.regexp "rep" in
  let has_rep_consts a = 
    IdSet.exists 
      (fun (name, _) -> Str.string_match cons_re name 0)
      (funs a)
  in
  let has_unary_funs a =
    IdMap.fold
	(fun _ decl acc -> acc || not decl.is_pred && decl.arity = 1)
	(sign a) false
  in
  let comp a b =
    if has_rep_consts a then
      if has_rep_consts b then compare a b
      else 1
    else if has_rep_consts b then -1
    else compare a b
  in
  fun a b ->
  if has_unary_funs a then 
    if has_unary_funs b then comp a b
    else 1
  else if has_unary_funs b then -1
  else comp a b

let interpolate_with_model signature model session_b pf_b_inst =
  let session_b' = Prover.SmtLib.push session_b in
  let literals = 
    let cm = List.map List.hd (Model.to_clauses model) in
    List.sort compare_forms cm in
  let new_symbols =
    IdMap.fold (fun id decl acc -> 
      if IdMap.mem id signature then acc else IdMap.add id decl acc)
      (sign (mk_and literals)) IdMap.empty
  in
  Prover.SmtLib.declare session_b new_symbols;
  let rec loop acc fs = 
    match Prover.SmtLib.is_sat session_b with
    | Some true -> 
	begin
	  match fs with
	  | f :: fs1 ->
	      Prover.SmtLib.assert_form session_b f;
	      loop (f :: acc) fs1
	  | [] -> 
	      if !Debug.verbose then Model.print_model (unopt (Prover.SmtLib.get_model session_b));
	      failwith ("no interpolant")
	end
    | Some false -> acc
    | None -> failwith "failed due to incompleteness of prover"
  in
  let core_literals = loop [] literals in
  ignore (Prover.SmtLib.pop session_b');
  let interpolant = 
    match Prover.get_interpolant (mk_and core_literals) (mk_and pf_b_inst) with
    | Some f -> f
    | None -> failwith "wtf"
  in simplify interpolant

  
let interpolate pf_a_inst pf_b_inst =
  let signature = sign (mk_and (pf_a_inst @ pf_b_inst)) in
  (* start session for model enumeration for A *)
  let session_a = Prover.SmtLib.start () in
  Prover.SmtLib.declare session_a signature;
  Prover.SmtLib.assert_forms session_a pf_a_inst;
  (* start session for interpolation generation *)
  let session_b = Prover.SmtLib.start () in
  Prover.SmtLib.declare session_b signature;
  Prover.SmtLib.assert_forms session_b pf_b_inst;
  let rec loop acc =
    (* find next partial model for A and compute interpolant *)
    match Prover.SmtLib.get_model session_a with
    | Some model -> 
	let interpolant = interpolate_with_model signature model session_b pf_b_inst in
	Prover.SmtLib.assert_form session_a (mk_not interpolant);
	loop (interpolant :: acc)
    | None -> smk_or acc
  in 
  (* compute interpolant *)
  let interpolant = loop [] in
  ignore (Prover.SmtLib.quit session_a);
  interpolant

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = "" then cmd_line_error "input file missing" else
      let path = parse_input () in
      let pf_a, pf_b = 
	Logger.with_log main_log Logger.INFO (fun () -> "Computing path formula", []) 
	  (fun () -> path_form path) 
      in
      (* let _ = if !Debug.verbose then print_forms stdout [mk_and pf_a; mk_and pf_b] in *)
      let pf_a_inst, pf_b_inst = InstGen.instantiate pf_a pf_b in
      let interpolant = 
	Logger.with_log main_log Logger.INFO (fun () -> "Computing interpolant", []) 
	  (fun () -> interpolate pf_a_inst pf_b_inst) 
      in
      print_form stdout interpolant
      (*print_form stdout (mk_and (pf_a_inst @ pf_b_inst)) *)
      (*Debug.phase "Computing interpolant"
	(Prover.get_interpolant (mk_and pf_a_inst))
	(mk_and pf_b_inst)*)
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> print_endline "parse error"
	
    
(* ---- *)

  (* old code: (* compute abstracted model *)
  let model1 = 
    let cons_re = Str.regexp "rep" in
    Model.filter_defs (fun (name, _ as id) def -> 
      match def.Model.input with 
      | [] -> not (Str.string_match cons_re name 0) 
      | _ -> is_pred_id id || is_jp id) 
      model 
  in
  let fmodel = Model.form_of_model model in
  let amodel = Model.form_of_model model1 in
  let _ = Debug.msg ("\nAbstracted partial model\n");
    if !Debug.verbose then print_forms stdout (List.sort compare_forms (Model.to_clauses model))
  in
  let rec loop amodel =
    match Prover.get_interpolant amodel (mk_and pf_b_inst) with
    | Some f -> f
    | None ->
        (* refine amodel *) 
        Logger.log main_log INFO (fun () -> "\nAbstracted partial model too weak - refining partial model...", []);
        let bmodel = Prover.get_model (smk_and (amodel :: pf_b_inst)) (*Model.form_of_model model*) in
	let bmodel_form = Model.form_of_model (unopt bmodel) in
	match Prover.get_interpolant fmodel bmodel_form with
	| Some f -> loop (smk_and [f; amodel])
	| None -> failwith "no interpolant"
  in simplify (loop amodel) *)
