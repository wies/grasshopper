open Form
open FormUtil
open AuxNames
open Prog

exception Compile_pred_failure of string

let dom_id = mk_ident "Dom"
let dom_set = mk_free_const ~srt:(Set Loc) dom_id

let compile_pred acc pred =
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
        IdMap.add pred_dom.pred_name pred_dom
          (IdMap.add pred_str.pred_name pred_str acc)
     with Not_found -> 
       (*ProgError.error pred.pred_pos 
         ("Unable to translate predicate " ^ (str_of_ident pred.pred_name)))*)
       acc)
  | FOL _ -> acc

let compile_pred_new pred = match pred.pred_body.spec_form with
  | SL f ->
    (try
      let recurse f = IdSet.mem pred.pred_name (SlUtil.preds f) in
      let base_case, induction_step = match f with
        | Sl.Or [a;b] ->
          if recurse a then
            begin
              assert (not (recurse b));
              b, a
            end
          else 
            begin
              assert (recurse b);
              a, b
            end
        | _ -> raise (Compile_pred_failure "cannot identify base case and induction step.")
      in
        failwith "TODO"
    (* TODO
    Generalize:
      - apply heuristics
        - identify rec field ...
        - ...
      - verify/prove the generalization is correct:
        - inductive def ⇒ generalization
        - generalization ⇒ inductive def

    type pred_decl = {
        pred_name : ident; (** predicate name *)
        pred_formals : ident list; (** formal parameter list *)
        pred_returns : ident list; (** return parameter list *)
        pred_locals : var_decl IdMap.t; (** local variables *)
        pred_body : spec; (** predicate body *)
        pred_pos : source_position; (** position of declaration *)
        pred_accesses : IdSet.t; (** accessed variables *)
      } 
    *)
    with Compile_pred_failure cause ->
      begin
        Debug.msg ("Compile_pred_failure: " ^ cause);
        []
      end)
  | FOL _ -> [pred]

