open Form
open FormUtil
open AuxNames
open Prog

exception Compile_pred_failure of string

let dom_id = fresh_ident "domain"
let dom_set = mk_loc_set dom_id

let get_cases pred = match pred.pred_body.spec_form with
  | SL (Sl.BoolOp (Or, cases, _)) -> cases
  | SL case -> [case]
  | FOL _ -> raise (Compile_pred_failure "expected SL")

type inductive_definition_case = {
    idc_pred: pred_decl;
    idc_switch: form;
    idc_pure: form list;
    idc_footprint: term list;
    idc_induction_term: (term list) option; (* just the args *)
    idc_other_term: (ident * (term list)) option;
    idc_other: Sl.form option
  }

(* methods to 'classify the cases' *)
let is_base_case c =
  c.idc_induction_term = None &&
  c.idc_other_term = None &&
  c.idc_other = None

let is_ind_step c = c.idc_induction_term <> None 

let is_aux_step c =
  c.idc_induction_term = None &&
  c.idc_other_term <> None

(*TODO this one does not make much sense*)
let use_other c =
  c.idc_induction_term = None &&
  ( c.idc_other_term <> None ||
    c.idc_other <> None )

(* TODO better structure of the cases (once again)
 * preprocessing:
 *   -flatten the expr
 *   -rewrite the SL part to make the footpring explicit as a set
 * generalization
 *   -idendify the cursor and express things in term of the cursor
 *   -switches involves the cursor and constant param
 *   -derived params as cursor+offset(+field)
 *   -sets are projection of the backbone + base
 * TODO this is an orthogonal view that focuses on the arguments rather than the cases itself
 *)

type role =
    (*cursor (traverse the backbone)*)
    Cursor of ident (*field*) * ident (*end*)
    (*nothing*)
  | Constant
    (*derived needs step and initial value*)
  | Derived of ident option (*init*) * int (*offset*) * (ident option) (*field*)
    (*set needs a base and a projection of the backbone*)
  | SetPart of term (* base *) * (ident option) (* field in projection *) * bool (*disjoint*)

type inductive_definition_parameter = ident * int (*position*) * role

(* When a pred call an other pred try to make the arguments matches and return the corresponding substitution
 * caller and callee are list of cases
 *)
let aux_substitution caller callee =
  let aux_step = Util.find_unique is_aux_step caller in
  let ind_step = Util.find_unique is_ind_step callee in
  let aux_args =
    let (id, args) = Util.Opt.get aux_step.idc_other_term in
      assert(id = aux_step.idc_pred.pred_name);
      args
  in
  let ind_args = Util.Opt.get ind_step.idc_induction_term in
  let rec get_diff (t1, t2) = match (t1, t2) with
    | (Var (i1, s1), Var (i2, s2))
    | (App (FreeSym i1, [], s1), App (FreeSym i2, [], s2)) ->
      if s1 <> s2 then raise (Compile_pred_failure "get_diff has different type");
      if (i1 = i2) then [] else [(i1,i2)]
    | (App (sym1,arg1,srt1), App (sym2,arg2,srt2)) ->
      if sym1 <> sym2 || srt1 <> srt2 then
        raise (Compile_pred_failure "get_diff: terms too far away");
      Util.flat_map get_diff (List.combine arg1 arg2)
    | _ -> raise (Compile_pred_failure "get_diff: terms too far away")
  in
  let subst_pair = Util.flat_map get_diff (List.combine aux_args ind_args) in
  let map =
    List.fold_left
      (fun acc (id1, id2) ->
        if IdMap.mem id1 acc then
          begin
            if IdMap.find id2 acc <> id1 then
              raise (Compile_pred_failure "unify_aux, substitution is not unique.")
            else acc
          end
        else IdMap.add id2 id1 acc
      )
      IdMap.empty
      subst_pair
  in
    map

(* TODO explicit FP
    no top level negation,
    partial sl to fol translation,
    remove the acc,
    add FP to the pred formals
 *)

(* TODO flattening -> easier to assign roles *)


(* better strucutre of the cases:
 * - there is a switch predicates (x=y, x≠y)
 * - footprint
 * - pure part
 * - inductive call
 * - call to other predicates
 * - TODO rest
 *)
let isolate_cases pred =
  let rec decompose case = match case with
    | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
      let lst = [f1; f2] in
      List.fold_left
        (fun (a1,b1,c1) (a2,b2,c2) -> (a1 @ a2, b1 @ b2, c1 @ c2) )
        ([],[],[])
        (List.map decompose lst)
    | Sl.BoolOp (And, lst, _) ->
      List.fold_left
        (fun (pure,sep,preds) (p,s,pr) ->
          if sep = [] && preds = [] then (p@pure,s@sep,pr@preds)
          else if s = [] && preds = [] then (p@pure,s@sep,pr@preds)
          else raise (Compile_pred_failure "partial support for Sl.And")
        )
        ([],[],[])
        (List.map decompose lst)
    | Sl.Pure (f, _) -> ([f],[],[])
    | Sl.Atom (Sl.Region, args, _) -> ([],args,[])
    | Sl.Atom (Sl.Emp, [], _) -> ([],[],[])
    | Sl.Atom (Sl.Pred p, args, _) -> ([],[],[(p, args)])
    | other -> raise (Compile_pred_failure ("do not support '"^(Sl.string_of_form other)^"' for the moment"))
  in
  let find_switches cases =
    (*simple version that works if every cases have the same switches*)
    let pures =
      List.map
        (fun (a,_,_) ->
          List.fold_left
            (fun acc t -> match t with
              | BoolOp (Not, [t]) -> FormSet.add t acc
              | t -> FormSet.add t acc
            )
            FormSet.empty
            a
        )
        cases
    in
    let common =
      List.fold_left
        FormSet.inter
        (List.hd pures)
        (List.tl pures)
    in
      common
  in
  let make_case switches (pures, footprint, preds) =
    let switch, pures =
      List.partition
        (fun f ->
          let f2 = match f with
            | BoolOp (Not, [t]) -> t
            | t -> t
          in
            FormSet.mem f2 switches
        )
        pures 
    in
    let ind_term, other_term = match preds with
      | [(id, args)] ->
        if id = pred.pred_name
        then (Some args, None)
        else (None, Some (id, args))
      | [] -> (None, None)
      | _ -> raise (Compile_pred_failure "nested data structure or tree-like structure or ... not yet supported.")
    in
      { idc_pred = pred;
        idc_switch = smk_and switch;
        idc_pure = pures;
        idc_footprint = footprint;
        idc_induction_term = ind_term;
        idc_other_term = other_term;
        idc_other = None (*TODO*) }
  in
  let cases = get_cases pred in
  let cases = List.map decompose cases in
  let switches = find_switches cases in
    List.map (make_case switches) cases


let has_inductive_call pred f =
  let prds = SlUtil.preds f in
    IdSet.mem pred.pred_name prds

(* split the SL def into a base case and an induction step. *)
let base_case_ind_step pred f = match f with
    | Sl.BoolOp (Or, [a;b], _) ->
      begin
        match (has_inductive_call pred a, has_inductive_call pred b) with
        | (true, true) -> raise (Compile_pred_failure "2 induction steps ?")
        | (true, false) -> b, a
        | (false, true) -> a, b
        | (false, false) -> raise (Compile_pred_failure "2 base cases ?")
      end
    | _ -> raise (Compile_pred_failure "more than 2 cases.")

let inductive_call pred f =
  let preds = SlUtil.preds_full f in
  let candidates =
    Sl.SlSet.filter
      (fun p -> match p with
        | Sl.Atom (Sl.Pred id, _, _) -> id = pred.pred_name
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
  if Debug.is_info () then
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
  (* TODO generalize to pred def using others preds
   * when doing the induction on the other:
   *  assuming the other is correct and base case is empty we only need to do the 'last step'
   *    the sanity checks should ensures that what the translation is always correct if the other pred is correct
   * when using only other:
   *  assuming the other are correct, then we are fine
   *)
  let base, step = base_case_ind_step pred_sl sl_spec in
  let fol_pos = smk_and [dom_spec; str_spec] in
  let fol_neg = smk_and [dom_spec; mk_not str_spec] in
  (* induction hyp *)
  let dom1 = mk_loc_set (fresh_ident (name dom_id)) in
  let mk_fol args =
    let map = List.fold_left2
      (fun acc a b -> IdMap.add a b acc)
        (IdMap.add dom_id dom1 IdMap.empty)
      pred_sl.pred_formals
      args
    in
      subst_consts map fol_pos 
  in
  let call = inductive_call pred_sl step in
  let induc_hyp_fol =
    let args = match call with
      | Sl.Atom (Sl.Pred id, args, _) -> args
      | _ -> assert false
    in
      mk_fol args
  in
  let induc_hyp_sl = ToGrass.to_grass pred_to_form dom1 call in
  (* SOUNDNESS: inductive def ⇒ generalization *)
  (* induction proof *)
  (* base case *)
  begin
    let sl_base = ToGrass.to_grass pred_to_form dom_set base in
    let base_query = smk_and [sl_base; fol_neg] in
    let base_res =
      Prover.check_sat
        ~session_name:("pred_gen_base_case_1_"^(string_of_ident pred_sl.pred_name))
        base_query
    in
    if base_res <> Some false then raise (Compile_pred_failure "pred_gen_base_1")
  end;
  (* induction step *)
  begin
    let sl_step = ToGrass.to_grass pred_to_form dom_set step in
    let step_query = smk_and [sl_step; induc_hyp_fol; fol_neg] in
    let step_res =
      Prover.check_sat
        ~session_name:("pred_gen_indc_step_1_"^(string_of_ident pred_sl.pred_name))
        step_query
    in
    if step_res <> Some false then raise (Compile_pred_failure "pred_gen_step_1")
  end;
  (* COMPLETENESS: generalization ⇒ inductive def *)
  (* induction proof *)
  (* base case *)
  begin
    let sl_base = ToGrass.to_grass_negated pred_to_form dom_set base in
    let emp = mk_eq dom_set (mk_empty (Set Loc)) in (* TODO DZ: most certainly not correct *)
    let base_query = smk_and [emp; sl_base; fol_pos] in
    let base_res =
      Prover.check_sat
        ~session_name:("pred_gen_base_case_2_"^(string_of_ident pred_sl.pred_name))
        base_query
    in
    if base_res <> Some false then raise (Compile_pred_failure "pred_gen_base_2")
  end;
  (* induction step *)
  begin
    let sl_step = ToGrass.to_grass_negated pred_to_form dom_set step in
    let ind_hyp_1 = (* the rest is fine *)
    (*
    IdMap.iter (fun k v -> print_endline ((string_of_ident k)^" -> "^(string_of_term v))) map;
    print_smtlib_form stdout fol_pos;
    print_newline ();
    print_smtlib_form stdout fol;
    print_newline ();
    *)
        mk_and [induc_hyp_sl;induc_hyp_fol]
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
        ~session_name:("pred_gen_indc_step_2_"^(string_of_ident pred_sl.pred_name))
        step_query
    in
    if step_res <> Some false then raise (Compile_pred_failure "pred_gen_step_2")
  end



(* fallback version that goes looking into the repository of predefined predicates *)
let compile_pred pred =
  match pred.pred_body.spec_form with
  | SL f ->
      (try 
        let dom_decl = mk_loc_set_decl dom_id pred.pred_pos in
        let formals = pred.pred_formals in
        let locals = IdMap.add dom_id dom_decl pred.pred_locals in
        let args = 
          (dom_id, Set Loc) ::
          (List.map (fun id ->
            let decl = IdMap.find id pred.pred_locals in
              id, decl.var_sort) 
            pred.pred_formals)
        in
        let str_body, outputs =
          Symbols.pred_to_form pred.pred_name args
        in
        let pred_str =
          { pred_name = Symbols.pred_struct pred.pred_name;
            pred_formals = dom_id :: formals;
            pred_locals = locals;
            pred_outputs = [];
            pred_body = { pred.pred_body with spec_form = FOL str_body };
            pred_pos = pred.pred_pos;
            pred_accesses = IdSet.empty;
            pred_is_free = false;
          }
        in
        let formals_output =
          List.filter
            (fun i -> List.for_all (fun (i2, _) -> i <> i2) outputs)
            (dom_id :: formals)
        in
        let pred_outputs =
          List.map
            (fun (id, form) ->
              { pred_str with 
                  pred_name = Symbols.pred_naming pred.pred_name id;
                  pred_formals = formals_output;
                  pred_outputs = [id];
                  pred_body = { pred.pred_body with spec_form = FOL form } 
              }
            )
            outputs
        in
          (*
          (try verify_generalization pred pred_dom pred_str
           with Compile_pred_failure why ->
             Debug.warn ( "cannot prove that predefined translation of '" ^
                          (string_of_ident pred.pred_name) ^
                          "' is correct: " ^ why ^ "\n"));
          *)
          pred_str :: pred_outputs
     with Not_found -> 
       ProgError.error pred.pred_pos 
         ("Unable to translate predicate " ^ (string_of_ident pred.pred_name)))
  | FOL _ -> [pred]

let compile_pred_acc acc pred =
  List.fold_left
    (fun acc p -> IdMap.add p.pred_name p acc)
    acc
    (compile_pred pred)



let compile_preds preds =
  (* additional 'output' parameters *)
  let preds_map =
    List.fold_left
      (fun acc p -> IdMap.add p.pred_name p acc)
      IdMap.empty preds
  in
  let already_fol, sl_spec =
    List.partition
      (fun p -> match p.pred_body.spec_form with
        | FOL _ -> true
        | _ -> false )
      preds
  in
  let cases_index =
    List.fold_left
      (fun acc pred -> match pred.pred_body.spec_form with
        | SL _ -> IdMap.add pred.pred_name (isolate_cases pred) acc
        | FOL _ -> acc )
      IdMap.empty
      sl_spec
  in
  (* ... *)
  let get_base_case id =
    let cases = IdMap.find id cases_index in
      try Util.find_unique is_base_case cases
      with _ -> raise (Compile_pred_failure "cannot identify base case.")
  in
  let get_ind_step id =
    let cases = IdMap.find id cases_index in
      try Util.find_unique is_ind_step cases
      with _ -> raise (Compile_pred_failure "cannot identify induction step.")
  in
  let get_aux_step id =
    let cases = IdMap.find id cases_index in
      try Util.find_unique is_aux_step cases
      with _ -> raise (Compile_pred_failure "cannot identify aux step.")
  in
  (* ... *)
  let simple_pred id = (* blseg *)
    let cases = IdMap.find id cases_index in
    let b = List.filter is_base_case cases in
    let i = List.filter is_ind_step cases in
      List.length cases = List.length (b @ i)
  in
  let use_aux_induction_pred id = (* slseg *)
    let cases = IdMap.find id cases_index in
    let b = List.filter is_base_case cases in
    let u = List.filter use_other cases in
      List.length cases = List.length (b @ u)
  in
  let only_aux id = (* lslseg *)
    let cases = IdMap.find id cases_index in
      List.for_all use_other cases
  in
  (* ... *)
  let compile_base_indct pred base_case induction_step aux_pred =
    let ind_step_args = match induction_step.idc_induction_term with
      | Some args -> args
      | None -> raise (Compile_pred_failure "cannot identify induction parameters.")
    in
    (* field over which the induction is made *)
    (* TODO the current  version forces progess because it follows the backbone pointer
     * a better way to ensure progress is to make sure that the pure part is not empty.
     *)
    let ind_fld, ind_var =
      let candidates =
        List.filter
          (fun t -> match t with
            | App (Read, [fld; x], _) -> sort_of fld = Fld Loc
            | _ -> false)
          ind_step_args
      in
        match candidates with
        | [App (Read, [fld; x], _)] -> fld, x
        | _ -> raise (Compile_pred_failure "...")
    in
    let ind_id =
      let set = (free_consts_term ind_var) in
        if IdSet.cardinal set <> 1 then
          raise (Compile_pred_failure "could not find id of the term used in the induction");
        IdSet.choose set
    in
    (* find the end of the segment *)
    let end_of_segment =
      if (base_case.idc_footprint <> []) then
        raise (Compile_pred_failure "base case has non-empty footprint.");
      let rec process f = match f with
      | Atom (App (Eq, [x;y], _), _) ->
          if x = ind_var then [y] 
          else if y = ind_var then [x]
          else []
      | _ -> []
      in
      let candidates =
        Util.flat_map
          process
          (base_case.idc_switch :: base_case.idc_pure)
      in
        match candidates with
        | x :: _ -> x
        | [] -> raise (Compile_pred_failure "can not find the end of the segment")
    in
    (* how arguments changes during the induction *)
    let base_args_call_args =
      let formals = match aux_pred with
        | Some p -> p.pred_formals
        | None -> pred.pred_formals
      in
        List.combine formals ind_step_args in
    let constant_args =
      List.filter
        (fun (id, term) -> match term with
          | App (FreeSym id2, [], _) -> id == id2
          | _ -> false )
        base_args_call_args
    in
    let lagging_args =
      List.filter
        (fun (id, term) -> match term with
          | App (FreeSym id2, [], _) -> id2 <> id
          | App (Read, [fld; App (FreeSym id2, [], _)], _) -> id2 = ind_id && fld <> ind_fld
          | _ -> false )
        base_args_call_args
    in
    (* unify the terms in the current pred and aux pred *)
    let aux_subst =
      match aux_pred with
      | Some p ->
        begin
          let rec process acc arg1 arg2 = match (arg1, arg2) with
            | (x::xs, y::ys) ->
              let srt1 = (IdMap.find x pred.pred_locals).var_sort in
              let srt2 = (IdMap.find y p.pred_locals).var_sort in
              let acc = IdMap.add y (mk_free_const srt1 x) acc in
                if srt1 <> srt2 then raise (Compile_pred_failure "aux arg mismatch");
                process acc xs ys
            | _ -> acc
          in
            process IdMap.empty pred.pred_formals p.pred_formals
        end
      | None -> IdMap.empty
    in
    (* additional interpreted predicates *)
    let unary_predicates =
      let allowed = 
        List.fold_left
          (fun acc id -> IdSet.add id acc)
          (IdSet.singleton ind_id)
          (fst (List.split constant_args))
      in
      let unary =
        List.filter
          (fun f ->
            let fc = free_consts f in
              IdSet.is_empty (IdSet.diff fc allowed))
          induction_step.idc_pure
      in
      let srt =
        let locals = match aux_pred with
          | Some p -> p.pred_locals
          | None -> pred.pred_locals
        in
          (IdMap.find ind_id locals).var_sort
      in
      if srt <> Loc then 
        raise (Compile_pred_failure "expected induction in type Loc");
      let var = mk_var srt ind_id in
        if unary = [] then []
        else
          let f = mk_implies (mk_elem var dom_set) (smk_and unary) in
            [mk_forall [(ind_id, srt)] (subst_consts (IdMap.add ind_id var aux_subst) f)]
    in
    (* binary preds
     * - reach(x, y, end_of_segment)
     * - pred(x.field_1, y.field_2)
     * - check monotonicity, how ?
     * - assuming monotonicity, the 1st value is turned into a unary pred
     *)
    let binary_predicates = match lagging_args with
      | [(id, prev)] ->
        begin
          let allowed = 
            List.fold_left
              (fun acc id -> IdSet.add id acc)
              (IdSet.add id (IdSet.singleton ind_id))
              (fst (List.split constant_args))
          in
          let with_id =
            List.filter
              (fun f ->
                let fc = free_consts f in
                  (IdSet.mem id fc) && (IdSet.is_empty (IdSet.diff fc allowed)))
              induction_step.idc_pure
          in
          (* match id to the lagging stuff *)
          let var1 = Axioms.loc1 in
          let var2 = Axioms.loc2 in
          let term_for_lagging = match prev with
            | App (FreeSym _, [], Loc) -> var1
            | App (Read, [fld; App (FreeSym _, [], Loc)], srt) -> App (Read, [fld; var1], srt)
            | _ -> raise (Compile_pred_failure "expected const or read of type Loc")
          in
            if with_id <> [] then
              begin
                let map1 = IdMap.add ind_id var2 aux_subst in
                let map2 = IdMap.add id term_for_lagging map1 in
                let guard1 = mk_and [mk_elem var2 dom_set] in
                let guard2 = mk_and [mk_btwn ind_fld var1 var2 end_of_segment;
                                    mk_elem var1 dom_set;
                                    mk_elem var2 dom_set] in
                let f1 = subst_consts map1 (mk_implies guard1 (smk_and with_id)) in
                let f2 = subst_consts map2 (mk_implies guard2 (smk_and with_id)) in
                  if aux_pred = None then
                    List.map Axioms.mk_axiom2 [f1; f2]
                  else
                    [Axioms.mk_axiom2 f2]
              end
            else []
        end
      | [] -> []
      | _ -> raise (Compile_pred_failure "too many lagging arguments");
    in
    let additional_cstr = unary_predicates @ binary_predicates in
    (* make the body of the new preds *)
    let str_body =
      Axioms.mk_axiom
        ("str_of_"^(string_of_ident pred.pred_name))
        (subst_consts
          aux_subst
          (mk_and ((mk_reach ind_fld ind_var end_of_segment) :: additional_cstr)))
    in
    let dom_body =
      Axioms.mk_axiom
        ("dom_of_"^(string_of_ident pred.pred_name))
        (subst_consts
          aux_subst
          (mk_iff (mk_and [(mk_btwn ind_fld ind_var Axioms.loc1 end_of_segment);
                           (mk_neq Axioms.loc1 end_of_segment)])
                  (mk_elem Axioms.loc1 dom_set)))
    in
    (* package the new preds *)
    let dom_decl = mk_loc_set_decl dom_id pred.pred_pos in
    let pred_str =
      { pred_name = Symbols.pred_struct pred.pred_name;
        pred_formals = dom_id :: pred.pred_formals;
        pred_locals = IdMap.add dom_id dom_decl pred.pred_locals;
        pred_outputs = [];
        pred_body = { pred.pred_body with spec_form = FOL str_body };
        pred_pos = pred.pred_pos;
        pred_accesses = IdSet.empty;
        pred_is_free = false;
      }
    in
    let pred_dom = 
      { pred_str with 
        pred_name = Symbols.pred_naming pred.pred_name dom_id;
        pred_formals = pred.pred_formals;
        pred_outputs = [dom_id];
        pred_body = { pred.pred_body with spec_form = FOL dom_body } 
      }
    in
      verify_generalization pred pred_dom pred_str;
      [pred_str; pred_dom]
  in
  let compile_simple_pred id =
    let pred = IdMap.find id preds_map in
    let base = get_base_case id in
    let step = get_ind_step id in
      compile_base_indct pred base step None
  in
  let compile_use_aux id =
    (* generalize to pred def using others preds: slseg → uslseg
     * -make sure the base case is the same
     * -comparing the induction step:
     *   -same footprint, same call parameters, unary pred
     *   -only difference is the binary pred (first step) -> get the other induct step but remove the 1st pred
     *)
    let pred = IdMap.find id preds_map in
    (* let base = get_base_case id in*)
    let step = get_aux_step id in
    let id_aux = match step.idc_other_term with
      | Some (id, _) -> id
      | _ -> raise (Compile_pred_failure "expected other predicate")
    in
    let _ = (* TODO sanitiy check to make sure we can apply the generalisation *)
      (* existing args in the call must be the same,
         new args must be derived
         same preds on common args
       *)
        "TODO"
    in
    let base_aux = get_base_case id_aux in
    let pred_aux = IdMap.find id_aux preds_map in
    let step_aux = get_ind_step id_aux in
      compile_base_indct pred base_aux step_aux (Some pred_aux)
  in
  let compile_only_other id =
    raise (Compile_pred_failure "TODO")
  in
  let predefined id =
    let pred = IdMap.find id preds_map in
      compile_pred pred
  in
  let compile id =
    Debug.info (fun () -> "  translating SL definition to GRASS: " ^ (string_of_ident id) ^ "\n");
    try
      if simple_pred id then compile_simple_pred id
      else if use_aux_induction_pred id then compile_use_aux id
      else if only_aux id then compile_only_other id
      else predefined id
    with Compile_pred_failure why ->
      begin
        Debug.notice (fun () -> "cannot translate '" ^ (string_of_ident id) ^ "': " ^ why ^ "\n");
        Debug.notice (fun () -> "reverting to predefined\n");
        predefined id
      end
  in
  (* ... *)
  let compiled = Util.flat_map (fun c -> compile c.pred_name) sl_spec in
    List.fold_left
      (fun acc p -> IdMap.add p.pred_name p acc)
      IdMap.empty
      (already_fol @
       compiled)
  
