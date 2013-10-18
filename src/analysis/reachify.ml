open Form
open FormUtil
open AuxNames
open Prog

exception Compile_pred_failure of string

let dom_id = fresh_ident "Dom"
let dom_set = mk_loc_set dom_id

let compile_pred pred =
  match pred.pred_body.spec_form with
  | SL f ->
      (try 
        let dom_decl = mk_set_decl dom_id pred.pred_pos in
        let args = 
          List.map (fun id ->
            let decl = IdMap.find id pred.pred_locals in
            mk_free_const ~srt:decl.var_sort id) 
            pred.pred_formals
        in
        let formals = pred.pred_formals in
        let locals = IdMap.add dom_id dom_decl pred.pred_locals in
        let str_body, dom_body = 
          Symbols.pred_to_form pred.pred_name args dom_set in
        let pred_str =
          { pred_name = pred_struct pred.pred_name;
            pred_formals = formals @ [dom_id];
            pred_locals = locals;
            pred_returns = [];
            pred_body = { pred.pred_body with spec_form = FOL str_body };
            pred_pos = pred.pred_pos;
            pred_accesses = IdSet.empty;
          }
        in
        let pred_dom = 
          { pred_str with 
            pred_name = pred_domain pred.pred_name;
            pred_formals = pred.pred_formals;
            pred_returns = [dom_id];
            pred_body = { pred.pred_body with spec_form = FOL dom_body } 
          }
        in
          [pred_dom; pred_str]
     with Not_found -> 
       (*ProgError.error pred.pred_pos 
         ("Unable to translate predicate " ^ (str_of_ident pred.pred_name)))*)
       [])
  | FOL _ -> [pred]

let compile_pred_acc acc pred =
  List.fold_left
    (fun acc p -> IdMap.add p.pred_name p acc)
    acc
    (compile_pred pred)


(* split the SL def into a base case and an induction step. *)
let base_case_ind_step pred f =
  let recurse frm =
    let prds = SlUtil.preds frm in
      IdSet.mem pred.pred_name prds
  in
    match f with
    | Sl.Or [a;b] ->
      begin
        match (recurse a, recurse b) with
        | (true, true) -> raise (Compile_pred_failure "2 induction steps ?")
        | (true, false) -> b, a
        | (false, true) -> a, b
        | (false, false) -> raise (Compile_pred_failure "2 base cases ?")
      end
    | _ -> raise (Compile_pred_failure "cannot identify base case and induction step.")

let inductive_call pred f =
  let preds = SlUtil.preds_full f in
  let candidates =
    Sl.SlSet.filter
      (fun p -> match p with
        | Sl.Atom (Sl.Pred id, _) -> id = pred.pred_name
        | _ -> false )
      preds
  in
    if (Sl.SlSet.cardinal candidates = 0) then
      raise (Compile_pred_failure "induction steps: no candidates!!")
    else if (Sl.SlSet.cardinal candidates <> 1) then
      raise (Compile_pred_failure "induction steps: too many candidates")
    else
      Sl.SlSet.choose candidates


(* verify/prove the generalization is correct *)
let verify_generalization pred_sl pred_dom pred_str =
  if !Debug.verbose then
    begin
      print_endline "verifying the generalisation of inductive definition:";
      print_endline "  original def:";
      pr_pred Format.std_formatter pred_sl;
      print_endline "  domain:";
      pr_pred Format.std_formatter pred_dom;
      print_endline "  structure:";
      pr_pred Format.std_formatter pred_str
    end;
  (* specs *)
  let sl_spec = match pred_sl.pred_body.spec_form with
    | SL  f -> f    | _ -> assert false
  in
  let dom_spec = match pred_dom.pred_body.spec_form with
    | FOL f -> f    | _ -> assert false
  in
  let str_spec = match pred_str.pred_body.spec_form with
    | FOL f -> f    | _ -> assert false
  in
  let base, step = base_case_ind_step pred_sl sl_spec in
  let fol_pos = smk_and [dom_spec; str_spec] in
  let fol_neg = smk_and [dom_spec; mk_not str_spec] in
  (* SOUNDNESS: inductive def ⇒ generalization *)
  (* induction proof *)
  (* base case *)
  begin
    let sl_base = ToGrass.to_grass pred_to_form dom_set base in
    let base_query = smk_and [sl_base; fol_neg] in
    let base_res =
      Prover.check_sat
        ~session_name:("pred_gen_base_case_1_"^(str_of_ident pred_sl.pred_name))
        base_query
    in
    if base_res <> Some false then raise (Compile_pred_failure "pred_gen_base_1")
  end;
  (* induction step *)
  begin
    let sl_step = ToGrass.to_grass pred_to_form dom_set step in
    let step_query = smk_and [sl_step; fol_neg] in
    let step_res =
      Prover.check_sat
        ~session_name:("pred_gen_indc_step_1_"^(str_of_ident pred_sl.pred_name))
        step_query
    in
    if step_res <> Some false then raise (Compile_pred_failure "pred_gen_step_1")
  end;
  (* COMPLETENESS: generalization ⇒ inductive def *)
  (* induction proof *)
  (* base case *)
  begin
    let sl_base = ToGrass.to_grass_negated pred_to_form dom_set base in
    let emp = mk_eq dom_set (mk_empty (Some (Set Loc))) in
    let base_query = smk_and [emp; sl_base; fol_pos] in
    let base_res =
      Prover.check_sat
        ~session_name:("pred_gen_base_case_2_"^(str_of_ident pred_sl.pred_name))
        base_query
    in
    if base_res <> Some false then raise (Compile_pred_failure "pred_gen_base_2")
  end;
  (* induction step *)
  begin
    let sl_step = ToGrass.to_grass_negated pred_to_form dom_set step in
    let ind_hyp_1 = (* the rest is fine *)
      let dom1 = mk_loc_set (fresh_ident (name dom_id)) in
      let call = inductive_call pred_sl step in
      let sl = ToGrass.to_grass pred_to_form dom1 call in
      let args = match call with
        | Sl.Atom (Sl.Pred id, args) -> args
        | _ -> assert false
      in
      let map = List.fold_left2
        (fun acc a b -> IdMap.add a b acc)
          (IdMap.add dom_id dom1 IdMap.empty)
        pred_sl.pred_formals
        args
      in
      let fol = subst_consts map fol_pos in
    (*
    IdMap.iter (fun k v -> print_endline ((str_of_ident k)^" -> "^(string_of_term v))) map;
    print_smtlib_form stdout fol_pos;
    print_newline ();
    print_smtlib_form stdout fol;
    print_newline ();
    *)
        mk_and [sl;fol]
    in
    let ind_hyp_2 = (* exclude the base case *)
      ToGrass.to_grass_negated pred_to_form dom_set base
    in
    let step_query = smk_and [sl_step; fol_pos; ind_hyp_1; ind_hyp_2] in
    (*
    print_smtlib_form stdout ind_hyp_1;
    print_newline ();
    print_smtlib_form stdout step_query;
    print_newline ();
    *)
    let step_res =
      Prover.check_sat
        ~session_name:("pred_gen_indc_step_2_"^(str_of_ident pred_sl.pred_name))
        step_query
    in
    if step_res <> Some false then raise (Compile_pred_failure "pred_gen_step_2")
  end

let compile_pred_new pred = match pred.pred_body.spec_form with
  | SL f ->
    (try
      let base_case, induction_step = base_case_ind_step pred f in
      let ind_step_args =
        match inductive_call pred induction_step with
        | Sl.Atom (Sl.Pred id, args) -> args
        | _ -> assert false
      in
      (* field over which the induction is made *)
      let ind_fld, ind_var =
        let candidates =
          List.filter
            (fun t -> match t with
              | App (Read, [fld; x], _) -> sort_of fld = Some (Fld Loc)
              | _ -> false)
            ind_step_args
        in
          match candidates with
          | [App (Read, [fld; x], _)] -> fld, x
          | _ -> raise (Compile_pred_failure "...")
      in
      (* find the end of the segment *)
      let end_of_segment =
        (* TODO what about the rest ? *)
        let rec process f = match f with
          | Sl.And lst | Sl.SepStar lst | Sl.SepPlus lst -> Util.flat_map process lst
          | Sl.Pure (Atom (App (Eq, [x;y], _))) ->
            if x = ind_var then [y] 
            else if y = ind_var then [x]
            else []
          | _ -> []
        in
        let candidates = process base_case in
          match candidates with
          | x :: _ -> x
          | [] -> raise (Compile_pred_failure "could not find the end of the segment")
      in
      (* TODO additional constraints on data, etc *)
      let additional_cstr =
        []
      in
      (* make the body of the new preds *)
      let str_body =
        Axioms.mk_axiom
          ("str_of_"^(str_of_ident pred.pred_name))
          (mk_and ((mk_reach ind_fld ind_var end_of_segment) :: additional_cstr))
      in
      let dom_body =
        Axioms.mk_axiom
          ("dom_of_"^(str_of_ident pred.pred_name))
          (mk_iff (mk_and [(mk_btwn ind_fld ind_var Axioms.loc1 end_of_segment);
                           (mk_neq Axioms.loc1 end_of_segment)])
                  (mk_elem Axioms.loc1 dom_set))
      in
      (* package the new preds *)
      let dom_decl = mk_set_decl dom_id pred.pred_pos in
      let pred_str =
        { pred_name = pred_struct pred.pred_name;
          pred_formals = pred.pred_formals @ [dom_id];
          pred_locals = IdMap.add dom_id dom_decl pred.pred_locals;
          pred_returns = [];
          pred_body = { pred.pred_body with spec_form = FOL str_body };
          pred_pos = pred.pred_pos;
          pred_accesses = IdSet.empty;
        }
      in
      let pred_dom = 
        { pred_str with 
          pred_name = pred_domain pred.pred_name;
          pred_formals = pred.pred_formals;
          pred_returns = [dom_id];
          pred_body = { pred.pred_body with spec_form = FOL dom_body } 
        }
      in
        verify_generalization pred pred_dom pred_str;
        [pred_str; pred_dom]
    with Compile_pred_failure cause ->
      begin
        Debug.msg ("Compile_pred_failure: " ^ cause ^ "\n");
        Debug.msg "reverting to predefined predicates\n";
        compile_pred pred
      end)
  | FOL _ -> [pred]


let compile_pred_acc_new acc pred =
  List.fold_left
    (fun acc p -> IdMap.add p.pred_name p acc)
    acc
    (compile_pred_new pred)
