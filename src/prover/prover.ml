open Form
open FormUtil
open Util
open Axioms

let model_file = ref ""

let inst_num = ref 0

let dump_model model =
  if !model_file <> "" then begin
    let model_chan = open_out !model_file in
    Model.print_model2 model;
    Model.output_graphviz model_chan model;
    close_out model_chan;
  end


let mk_solver f = 
  let f_inst =
    if !Config.instantiate
    then Util.measure_call "instantiate" Reduction.reduce f 
    else
      begin
        let rec normalize acc = function
          | BoolOp(And, fs) :: gs -> normalize acc (fs @ gs)
          | f :: gs -> normalize (f :: acc) gs
          | [] -> List.rev acc
        in
        let normalized_fs = normalize [] [f] in
        let axioms_f, ground_f = extract_axioms normalized_fs in
          axioms_f @ ground_f
      end
  in
  let session = SmtLib.start_z3 () in
  let prove () =
    Debug.msg "sending to prover\n";

    let signature = sign (mk_and f_inst) in
    SmtLib.declare session signature;
    Debug.msg "  signature done\n";

    SmtLib.assert_forms session f_inst;
    Debug.msg "  f_inst done\n";

    let result = SmtLib.is_sat session in
    Debug.msg "prover came back\n";
    result
  in
  let result = Util.measure_call "prove" prove () in
  (result, session)

let check_sat f =
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
      let max = (*TermMap.cardinal terms_idx *)
	TermMap.fold (fun _ _ acc -> acc + 1) terms_idx 0
      in
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

