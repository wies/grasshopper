open Form
open Util
open Axioms

let model_file = ref ""

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
  let session_b = SmtLib.push session_b in
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
  SmtLib.declare session_b new_symbols;
  let pf_a_inst = InstGen.instantiate (pf_a_axioms @ literals) in
  let partition_instances instances terms =
    List.partition (fun c -> TermSet.subset (ground_terms c) terms) instances
  in
  (*Prover.SmtLib.assert_forms ~igroup:(Some count) session_b pf_a_inst;*)
  let rec loop (acc, terms, unused_inst) fs = 
    match SmtLib.is_sat session_b with
    | Some true -> 
	begin
	  match fs with
	  | f :: fs1 ->
	      let terms = TermSet.union terms (ground_terms f) in
	      let new_inst, unused_inst = partition_instances unused_inst terms in
	      inst_num := !inst_num + List.length new_inst;
	      SmtLib.assert_forms ~igroup:(Some count) session_b (f :: new_inst);
	      loop (f :: acc, terms, unused_inst) fs1
	  | [] -> 
	      (* if !Debug.verbose then Model.print_model (unopt (Prover.SmtLib.get_model session_b)); *)
	      if !model_file <> "" then begin
		let model_chan = open_out !model_file in
		Model.print_model2 model;
		Model.output_graphviz model_chan model;
		close_out model_chan;
	      end;
	      failwith "Input might be satisfiable. Failed to compute interpolant."
	end
    | Some false ->
	(match SmtLib.get_interpolant session_b [count] with
	| Some f -> f
	| None -> failwith "Failed to compute interpolant. Input might be satisfiable2.")
    | None -> failwith "Failed due to incompleteness of prover."
  in
  let interpolant = loop ([], TermSet.empty, pf_a_inst) literals in
  (*let _ = print_endline "Core literals:" in
  let _ = print_forms stdout core_literals in *)
  (* let _ = print_forms stdout core_literals in *)
  ignore (SmtLib.pop session_b);
  (*print_endline "Interpolant:"; print_form stdout interpolant;*)
  simplify interpolant

  
let interpolate pf_a pf_b =
  (* start session for model enumeration for A *)
  let session_a = SmtLib.start_z3 (Some "z3.in") in
  let pf_a_axioms, _ = extract_axioms pf_a in
  let pf_a_terms = ground_terms (mk_and pf_a) in
  (* let _ = print_endline "Instantiating A" in *)
  let pf_a_inst = InstGen.instantiate pf_a in
  (* let _ = print_endline "Instantiating B" in *)
  let pf_b_inst = InstGen.instantiate pf_b in
  let signature = sign (mk_and (pf_a_inst @ pf_b_inst)) in
  SmtLib.declare session_a signature;
  SmtLib.assert_forms session_a pf_a_inst;
  (* start session for interpolation generation *)
  let session_b = SmtLib.start_mathsat (Some "mathsat.in") in
  SmtLib.declare session_b signature;
  SmtLib.assert_forms session_b ~igroup:(Some 0) pf_b_inst;
  let rec loop acc count =
    (* find next partial model for A and compute interpolant *)
    match SmtLib.get_model session_a with
    | Some model1 -> 
	let model = Model.prune model1 pf_a_terms in
	let interpolant = interpolate_with_model signature model session_b pf_a_axioms count in
	SmtLib.assert_form session_a (mk_not interpolant);
	(* let _ = if count == 1 then exit 0 in*)
	loop (interpolant :: acc) (count + 1)
    | None -> smk_or acc, count - 1
  in 
  (* compute interpolant *)
  let interpolant, count = loop [] 1 in
  let _ = print_endline ("# iterations: " ^ (string_of_int count)) in
  let _ = print_endline ("# instances: " ^ (string_of_int (List.length pf_a_inst + List.length pf_b_inst))) in
  ignore (SmtLib.quit session_a);
  ignore (SmtLib.quit session_b);
  interpolant
  

let satisfiable f =
  let session = SmtLib.start_z3 (Some "z3.in") in
  let f_inst = InstGen.instantiate [f] in
  let signature = sign (mk_and f_inst) in
  Debug.msg "sending to prover\n";
  SmtLib.declare session signature;
  Debug.msg "  signature done\n";
  SmtLib.assert_forms session f_inst;
  Debug.msg "  f_inst done\n";
  let result = SmtLib.is_sat session in
  Debug.msg "prover came back\n";
  ignore (SmtLib.quit session);
  result
