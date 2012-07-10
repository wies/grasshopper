open Form
open Stmnt
open Axioms
open Util
open Logging

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Axioms.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-alloc", Arg.Set Axioms.with_alloc_axioms, "Add axioms for alloc predicate");
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

let inst_num = ref 0

let interpolate_with_model signature model session_b pf_a_axioms count =
  let session_b = Prover.SmtLib.push session_b in
  (* let _ = Model.print_model model in *)
  (* let _ = Model.print_model2 model in *)
  let literals = 
    let cm = List.map List.hd (Model.to_clauses model) in
    List.sort compare_forms cm in
  (* let _ = print_endline "Literals:" in
  let _ = print_forms stdout literals in *)
  let new_symbols =
    IdMap.fold (fun id decl acc -> 
      if IdMap.mem id signature then acc else IdMap.add id decl acc)
      (sign (mk_and literals)) IdMap.empty
  in
  Prover.SmtLib.declare session_b new_symbols;
  let pf_a_inst = InstGen.instantiate (pf_a_axioms @ literals) in
  let partition_instances instances terms =
    List.partition (fun c -> TermSet.subset (ground_terms c) terms) instances
  in
  (*Prover.SmtLib.assert_forms ~igroup:(Some count) session_b pf_a_inst;*)
  let rec loop (acc, terms, unused_inst) fs = 
    match Prover.SmtLib.is_sat session_b with
    | Some true -> 
	begin
	  match fs with
	  | f :: fs1 ->
	      let terms = TermSet.union terms (ground_terms f) in
	      let new_inst, unused_inst = partition_instances unused_inst terms in
	      inst_num := !inst_num + List.length new_inst;
	      Prover.SmtLib.assert_forms ~igroup:(Some count) session_b (f :: new_inst);
	      loop (f :: acc, terms, unused_inst) fs1
	  | [] -> 
	      (* if !Debug.verbose then Model.print_model (unopt (Prover.SmtLib.get_model session_b)); *)
	      failwith "Failed to compute interpolant. Input might be satisfiable."
	end
    | Some false ->
	(match Prover.SmtLib.get_interpolant session_b [count] with
	| Some f -> f
	| None -> failwith "Failed to compute interpolant. Input might be satisfiable2.")
    | None -> failwith "Failed due to incompleteness of prover."
  in
  let interpolant = loop ([], TermSet.empty, pf_a_inst) literals in
  (*let _ = print_endline "Core literals:" in
  let _ = print_forms stdout core_literals in *)
  (* let _ = print_forms stdout core_literals in *)
  ignore (Prover.SmtLib.pop session_b);
  (*print_endline "Interpolant:"; print_form stdout interpolant;*)
  simplify interpolant

  
let interpolate pf_a pf_b =
  (* start session for model enumeration for A *)
  let session_a = Prover.SmtLib.start_z3 (Some "z3.in") in
  let pf_a_axioms, _ = extract_axioms pf_a in
  let pf_a_terms = ground_terms (mk_and pf_a) in
  (* let _ = print_endline "Instantiating A" in *)
  let pf_a_inst = InstGen.instantiate pf_a in
  (* let _ = print_endline "Instantiating B" in *)
  let pf_b_inst = InstGen.instantiate pf_b in
  let signature = sign (mk_and (pf_a_inst @ pf_b_inst)) in
  Prover.SmtLib.declare session_a signature;
  Prover.SmtLib.assert_forms session_a pf_a_inst;
  (* start session for interpolation generation *)
  let session_b = Prover.SmtLib.start_mathsat (Some "mathsat.in") in
  Prover.SmtLib.declare session_b signature;
  Prover.SmtLib.assert_forms session_b ~igroup:(Some 0) pf_b_inst;
  let rec loop acc count =
    (* find next partial model for A and compute interpolant *)
    match Prover.SmtLib.get_model session_a with
    | Some model1 -> 
	let model = Model.prune model1 pf_a_terms in
	let interpolant = interpolate_with_model signature model session_b pf_a_axioms count in
	Prover.SmtLib.assert_form session_a (mk_not interpolant);
	(* let _ = if count == 1 then exit 0 in*)
	loop (interpolant :: acc) (count + 1)
    | None -> smk_or acc, count - 1
  in 
  (* compute interpolant *)
  let interpolant, count = loop [] 1 in
  let _ = print_endline ("# iterations: " ^ (string_of_int count)) in
  let _ = print_endline ("# instances: " ^ (string_of_int (List.length pf_a_inst + List.length pf_b_inst))) in
  ignore (Prover.SmtLib.quit session_a);
  ignore (Prover.SmtLib.quit session_b);
  interpolant

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := s) usage_message;
    if !input_file = "" then cmd_line_error "input file missing" else
      let path = parse_input () in
      let pf_a, pf_b = path_form path
      in
      (* let _ = if !Debug.verbose then print_forms stdout [mk_and pf_a; mk_and pf_b] in *)
      let interpolant = interpolate pf_a pf_b
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
	
    
