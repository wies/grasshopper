open Form
open FormUtil
open AuxNames
open Prog

exception Compile_pred_failure of string

let dom_id = mk_ident "Dom"
let dom_set = mk_free_const ~srt:(Set Loc) dom_id

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


let verify_generalization pred_sl pred_dom pred_str =
  if !Debug.verbose then
    begin
      print_endline "verifying the generalisation of inductive definition:";
      print_endline "  original def:";
      pr_pred Format.std_formatter pred_sl;
      print_endline "  domain:";
      pr_pred Format.std_formatter pred_dom;
      print_endline "  structure:";
      pr_pred Format.std_formatter pred_str;
    end;
    (* TODO
      - verify/prove the generalization is correct:
        - inductive def ⇒ generalization
        - generalization ⇒ inductive def
    *)
  false

let compile_pred_new pred = match pred.pred_body.spec_form with
  | SL f ->
    (try
      let recurse frm =
        let prds = SlUtil.preds frm in
        IdSet.mem pred.pred_name prds
      in
      let base_case, induction_step = match f with
        | Sl.Or [a;b] ->
          begin
            match (recurse a, recurse b) with
            | (true, true) -> raise (Compile_pred_failure "2 induction steps ?")
            | (true, false) -> b, a
            | (false, true) -> a, b
            | (false, false) -> raise (Compile_pred_failure "2 base cases ?")
          end
        | _ -> raise (Compile_pred_failure "cannot identify base case and induction step.")
      in
      (* the 'recursive call' *)
      let ind_step_args =
        let preds = SlUtil.preds_full induction_step in
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
            match Sl.SlSet.choose candidates with
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
          ("domain_of_"^(str_of_ident pred.pred_name))
          (mk_and ((mk_reach ind_fld ind_var end_of_segment) :: additional_cstr))
      in
      let dom_body =
        Axioms.mk_axiom
          ("domain_of_"^(str_of_ident pred.pred_name))
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
        if verify_generalization pred pred_dom pred_str then
          [pred_str; pred_dom]
        else
          raise (Compile_pred_failure "cannot prove generalization correct")
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
