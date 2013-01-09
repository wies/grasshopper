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

let dump_model model =
  if !model_file <> "" then begin
    let model_chan = open_out !model_file in
    Model.print_model2 model;
    Model.output_graphviz model_chan model;
    close_out model_chan;
  end

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
	      dump_model model;
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
  
let mk_solver f = 
  let f_inst =
    if !Config.instantiate
    then Util.measure_call "instantiate" InstGen.instantiate [f]
    else
      begin
        let rec normalize acc = function
          | And fs :: gs -> normalize acc (fs @ gs)
          | f :: gs -> normalize (f :: acc) gs
          | [] -> List.rev acc
        in
        let normalized_fs = normalize [] [f] in
        let axioms_f, ground_f = extract_axioms normalized_fs in
          axioms_f @ ground_f
      end
  in
  let z3_in = if !Debug.verbose then Some "z3.in" else None in
  let session = SmtLib.start_z3 z3_in in
  let prove () =
    Debug.msg "sending to prover\n";

    let signature = sign (mk_and f_inst) in
    SmtLib.declare session signature;
    Debug.msg "  signature done\n";

    if not !Config.instantiate then
      begin
        let grounds = ground_terms (mk_and f_inst) in
        let axioms_f, ground_f = extract_axioms f_inst in
        let classes = InstGen.congr_classes ground_f grounds in 
        SmtLib.declare_gound session (List.map List.hd classes);
        Debug.msg "  ground terms done\n";
      end;

    SmtLib.assert_forms session f_inst;
    Debug.msg "  f_inst done\n";

    let result = SmtLib.is_sat session in
    Debug.msg "prover came back\n";
    result
  in
  let result = Util.measure_call "prove" prove () in
  (result, session)

let satisfiable f =
  let (result, session) = mk_solver f in
  (match result with
  | Some true ->
      if !model_file <> "" then
	let model = SmtLib.get_model session in
	dump_model (unopt model)
  | _ -> ());
  ignore (SmtLib.quit session);
  result

(* An incremental version for the frame inference.
 * we can assume that the first query contains all the ground terms.
 * further queries are only adding blocking clauses.
 * also at each step we need to return the model if sat, none if unsat, error otherwise.
 *)
module ModelGenerator =
  struct
    type t = SmtLib.session

    let get_eq_classes_raw session terms =
      let terms_idx, max =
        List.fold_left
          ( fun (acc, i) t -> (TermMap.add t i acc, i+1))
          (TermMap.empty, 0)
          terms
      in
      let rec process uf terms = match terms with
        | x :: xs ->
          let id1 = TermMap.find x terms_idx in
            List.fold_left
              (fun acc y ->
                let id2 = TermMap.find y terms_idx in
                  if Puf.find uf id1 = Puf.find uf id2 then uf
                  else
                    begin
                      let s2 = SmtLib.push session in
                      SmtLib.assert_form s2 (mk_not (mk_eq x y));
                      let res = match SmtLib.is_sat s2 with
                        | Some true -> uf
                        | Some false -> Puf.union uf id1 id2
                        | None ->
                          ignore (SmtLib.quit s2);
                          failwith "cannot solve ?! (get_eq_classes)"
                      in
                        ignore (SmtLib.pop s2);
                        res
                    end
              )
              uf
              xs
        | [] -> uf
      in
      let uf = process (Puf.create max) terms in
        (uf, terms_idx)

    let get_eq_classes session terms =
      let (uf, terms_idx) = get_eq_classes_raw session terms in
        (fun v -> Puf.find uf (TermMap.find v terms_idx) )
    
    let get_eq_classes_lst session terms =
      let (uf, terms_idx) = get_eq_classes_raw session terms in
      let max = TermMap.cardinal terms_idx in
      let classes = Array.make max [] in
        List.iter
          (fun (t, i) ->
            let c = Puf.find uf i in
              classes.(c) <- t :: classes.(c)
          )
          (TermMap.bindings terms_idx);
        List.filter (fun x -> x <> []) (Array.to_list classes)

    let try_get_model (result, generator) = 
      match result with
      | Some true ->
        let model = SmtLib.get_model generator in
        Some (generator, unopt model)
      | Some false ->
        ignore (SmtLib.quit generator);
        None
      | None ->
        ignore (SmtLib.quit generator);
        failwith "cannot solve ?!"

    let initial_query f = try_get_model (mk_solver f)

    let add_blocking_clause generator clause =
      (*TODO sanity checks: no qantifiers, ... *)
      SmtLib.assert_forms generator [(mk_not clause)];
      let result = SmtLib.is_sat generator in
        try_get_model (result, generator)

  end

