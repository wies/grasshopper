(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Stdlib
open Printf
open Util 
open GrassUtil
open Grass
open SlUtil 
open SymbState
open Rules 
open SymbFunc
open SymbBranch
open Model
open Prog

(* todo filter out predicates in the program so we don't hit that problem. *)
let simplify proc prog =
  let info msg prog = Debug.info (fun () -> msg); prog in
  prog |>
  dump_if 0 |>
  info "Inferring accesses.\n" |>
  Analyzer.infer_accesses true |>
  (*filter_preds |>*)
  dump_if 1

(* Substitutes all constants in spec_form [sf] with other terms according to substution map [subst_map]. *) 
let subst_spec_form subst_map sf =
  match sf with
  | SL slf -> SL (SlUtil.subst_consts subst_map slf)
  | FOL f -> FOL (GrassUtil.subst_consts subst_map f)

let subst_spec_list subst_map sl =
  List.map (fun s -> 
    {s with spec_form=subst_spec_form subst_map s.spec_form}) sl

let pr_spec_form_list sfl =
  sfl
  |> List.map (fun v -> (string_of_format pr_spec_form v))
  |> String.concat ", "
  |> sprintf "[%s]"


(* Extract the formal output parameters identifiers of a procedure foo in program prog *)
let return_ids_of foo prog =
  let foo_contr =(find_proc prog foo).proc_contract in 
  foo_contr.contr_returns

let subst_spec_list_formals state sl proc args =
  let sm = 
    List.combine (formal_ids_of proc state.prog) args
    |> List.fold_left (fun sm (f, a) -> IdMap.add f a sm) IdMap.empty 
  in
  subst_spec_list sm sl

let postcond_of foo prog =
  (find_proc prog foo).proc_contract.contr_postcond

(* Collect the formal return terms of a procedure foo in program prog *)
let formal_return_terms foo prog =
  let returns = return_ids_of foo prog in
  let locs = (find_proc prog foo).proc_contract.contr_locals in 
    List.fold_left
      (fun acc var ->
        let srt = Grass.IdMap.find var locs in
        Grass.Var (var, srt.var_sort) :: acc)
      [] (returns)

let fold_spec_form_sl f acc specs =
  let folded = List.fold_left (fun facc a ->
    match a with
    | SL slf -> mk_sep_star slf facc
    | FOL f -> mk_sep_star (mk_pure f) facc)
    acc (List.map (fun s -> s.spec_form) specs)
  in
  folded

let declare_contract proc contract = 
  {proc with proc_contract=contract}

let subst_precond_formals foo prog args =
  let sm = 
    List.combine (formal_ids_of foo prog) args
    |> List.fold_left (fun sm (f, a) -> IdMap.add f a sm) IdMap.empty 
  in
  subst_spec_list sm (precond_of foo prog) 

let subst_spec_list_return_ids state postcond foo lhs_ids =
  let sm_lhs =
    let lhs_ts =
      Debug.debug(fun () -> sprintf "find %s\n" (string_of_ident foo));
      List.fold_left (fun acc id ->
        (find_symb_val state.store id) :: acc)
      [] lhs_ids
    in
    List.combine (return_ids_of foo state.prog) (List.rev lhs_ts)
    |> List.fold_left (fun sm (id, t) ->
        IdMap.add id t sm) IdMap.empty 
  in
  subst_spec_list sm_lhs postcond

let loop_target_terms state comm = 
  let loop_modified = modifies_cmd comm in
  let locals = state.contract.contr_locals in
  List.fold_left (fun ts id ->
    match IdMap.find_opt id locals with
    | Some x -> (Var (x.var_name, x.var_sort)) :: ts
    | None -> ts)
  [] (IdSet.elements loop_modified)

let rec exec state comm (fc: symb_state -> vresult) =
  Debug.debug(fun () -> sprintf "NO PROG\n");
  match comm with
  | Basic (Assign {assign_lhs=[field];
                    assign_rhs=[App (Write, [map; t1; t2], srt)]}, pp) ->
     Debug.debug (fun () -> 
      sprintf "%sExecuting Assign Write: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    consume_sl_form state state.heap (mk_field_region t1 map) (fun state2' h snp ->
      let r = (App (Read, [map; t1], range_sort_of_map map)) in
      let f = mk_sep_star (mk_field_region t1 map) (mk_pure (GrassUtil.mk_eq r t2)) in
      Debug.debug(fun() -> sprintf "CONSUME CONTINUE heap %s\n" (string_of_heap h));
      let state3 = {state2' with heap=h} in
      produce_sl_form state3 f (fresh_snap_tree ()) fc) 
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, pp) ->
    Debug.debug (fun () -> 
      sprintf "%sExecuting Assign: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    eval_terms state ts (fun state' ts' ->
      let st = List.combine ids ts'
      |> List.fold_left (fun macc (id, t') ->
          {macc with store = IdMap.add id t' macc.store}
      ) state'
      in
      fc st)
  | Seq (comms, pp) ->
      Debug.debug (fun () -> 
        sprintf "%sExecuting Seq: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
      );
      execs state comms (fun state' -> fc state')
  | Basic (Assert spec, pp) ->
    Debug.debug (fun () ->
      sprintf "%sExecuting Assert: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    (match spec.spec_form with
    | SL slf ->
      (*todo figure out continuation heap and snap arent used*)
      consume_sl_form state state.heap slf (fun state' h' snap ->
        fc state)
    | FOL f->
      consume_form state state.heap f (fun state' h' snp ->
        fc state'))
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, pp) -> 
      Debug.debug (fun () -> 
        sprintf "%sExecuting Procedure Call: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
      );
      eval_terms state (List.map (fun arg -> unoldify_term arg) args) (fun state' args' ->
        let precond' = fold_spec_list mk_sep_star (mk_atom Emp []) (precond_of foo state'.prog) in
        let precond_sf' = 
          subst_spec_list_formals state precond' foo args'
        in
        Debug.debug(fun () -> sprintf "\nPrecond[x -> e'] = %s\n" (pr_spec_form_list precond_sf'));
        consumes state' precond_sf' (fun state2' _ ->
          let proc_contr = (IdMap.find foo state.prog.prog_procs).proc_contract in
          let store' =
            List.combine proc_contr.contr_returns lhs
            |> List.fold_left (fun st (formal_id, id) ->
              let srt = (IdMap.find formal_id proc_contr.contr_locals).var_sort in  
              havoc_id st id srt)
            state2'.store
          in
            
          Debug.debug(fun () -> sprintf "state %s\n" (string_of_state state2'));
          let state3' = {state2' with store = store'} in

          (* fold multiple postcondition specs into 1 for the callee *)
          let postcond' = fold_spec_list mk_sep_star (mk_atom Emp []) (postcond_of foo state'.prog)in
          let post_sf' =
            let p =
              subst_spec_list_formals state3' postcond' foo args'
            in
            subst_spec_list_return_ids state3' p foo lhs
          in
          Debug.debug(fun () -> sprintf "\nPostcond[x -> e'][y->z] = %s\n" (pr_spec_form_list post_sf'));
          produces state3' post_sf' (fresh_snap_tree ()) (fun state4' -> fc state4')))
  | Basic (Havoc {havoc_args=vars}, pp) -> 
    let vars_terms =
      let locs = state.contract.contr_locals in
      List.fold_left
        (fun acc var ->
          let srt = Grass.IdMap.find var locs in
          Grass.Var (var, srt.var_sort) :: acc)
        [] (vars)
    in
    fc {state with store = (havoc state.store vars_terms)} 
  | Basic (Assume {spec_form=f; }, pp) -> 
    Debug.debug (fun () -> 
      sprintf "%sExecuting Assume: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    produce state f (fresh_snap_tree ()) (fun state' -> fc state')
  | Choice (comms, pp) ->
      branch_simple state comms exec (fun state' -> fc state')
  | Basic (Return {return_args=xs}, pp) -> 
    Debug.debug (fun () -> 
      sprintf "%sExecuting return: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    let locs = state.contract.contr_returns in
    exec state (Basic (Assign {assign_lhs=locs; assign_rhs=xs}, pp)) (fun state' ->
      fc state')
  | Basic (Split spec, pp) -> 
    Debug.debug (fun () -> 
      sprintf "%sExecuting split: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    todo "exec 10"
  | Basic (New {new_lhs=id; new_sort=srt; new_args=ts}, pp) ->
    Debug.debug (fun () -> 
      sprintf "%sExecuting new: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    let tnew = (Var (id, srt)) in
    let st2 = {state with store=(havoc state.store [tnew])} in 
    let loc_srt = strip_loc srt in
    let field_regions = IdMap.fold (fun _ v regions ->
      match v.var_sort with
      | Map ([Loc l], field_sort) when l = loc_srt ->
          mk_field_region tnew (mk_free_app field_sort v.var_name []) :: regions 
      | _ -> regions) state.prog.prog_vars [] in
    let snaps = List.map (fun _ -> (fresh_snap_tree ())) field_regions in
    produce_sl_forms st2 field_regions snaps fc 
  | Basic (Dispose d, pp) -> 
      Debug.debug (fun () ->
        sprintf "%sExecuting Dispose: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
      );
      eval_term state d.dispose_arg (fun state' t' ->
        let loc_srt = sort_of t' in
        let field_regions = IdMap.fold (fun _ v regions ->
          match v.var_sort with
          | Map ([Loc l], field_sort) when l = loc_srt ->
              mk_field_region t' (mk_free_app field_sort v.var_name []) :: regions 
          | _ -> regions) state.prog.prog_vars [] in

          consumes_sl_form state' state'.heap field_regions (fun state'' h'' snap ->
            fc state''))
  | Loop (l, pp) ->
      Debug.debug (fun () -> 
        sprintf "%sExecuting loop: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
      );
      let new_gamma = havoc state.store (loop_target_terms state comm) in
      let state1 = {state with store=new_gamma} in
      exec state1 l.loop_prebody (fun state2 ->
        let invar = fold_spec_form_sl mk_sep_star (mk_atom Emp []) l.loop_inv in
        let test_inv_form = 
            mk_sep_star invar (mk_pure l.loop_test)
          in
          Result.Ok (Opt.get (Result.to_option (produce_sl_form state2 test_inv_form (fresh_snap_tree ()) (fun state3 ->
            exec state3 l.loop_postbody (fun state4 ->
              consume_sl_form state4 state.heap invar (fun _ _ _ -> Result.Ok (Forms [])))))
          |> Opt.lazy_or_else (fun () ->
            Result.to_option (consume_sl_form state state.heap invar (fun state1' h s ->
              let state2' = {state1' with store=new_gamma} in
              exec state2' l.loop_prebody (fun state3' ->
                let slf = mk_sep_star invar (mk_pure (GrassUtil.mk_not l.loop_test)) in
                produce_sl_form state2' slf (fresh_snap_tree ()) fc)))))))
  | Basic (Unfold pc, pp) -> 
    Debug.debug (fun () -> 
        sprintf "%sExecuting unfold: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
    );
    eval_terms state pc.pred_args (fun state' args' ->
      Debug.debug (fun () -> sprintf "unfold terms (%s)\n" (string_of_term_list args'));
      let body = (IdMap.find pc.pred_name state'.prog.prog_preds).pred_body in
      match body with
      | Some b ->
        Debug.debug (fun () -> sprintf "body (%s)\n" (string_of_format pr_spec_form b));
        let ids = (IdMap.find pc.pred_name state.prog.prog_preds).pred_contract.contr_formals in 
        Debug.debug (fun () -> sprintf "ids (%s)\n" (string_of_ident_list ids));
        Debug.debug (fun () -> sprintf "terms (%s)\n" (string_of_term_list args'));
        let sm =
          List.combine ids args' 
          |> List.fold_left (fun sm (id, a) -> IdMap.add id a sm) IdMap.empty 
        in
        let body' = subst_spec_form sm b.spec_form in
        Debug.debug (fun () -> sprintf "body[x -> e] (%s)\n" (string_of_format pr_sspec_form body'));
        consume_sl_form state' state'.heap (SlUtil.mk_pred pc.pred_name pc.pred_args) (fun state2 heap' snap ->

          Debug.debug( fun() -> sprintf "state2 in produce symb sf %s\n" (string_of_state state2));
          produce state2 body' snap (fun state3 ->
            Debug.debug( fun() -> sprintf "state in produce symb sf %s\n" (string_of_state state3));
            fc state3))
      | None ->
        Debug.debug (fun () -> sprintf "no body\n");
        fc state'
    )
  | Basic (Fold pc, pp) ->
    Debug.debug (fun () -> 
        sprintf "%sExecuting fold: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
    );
    eval_terms state pc.pred_args (fun state' args' ->
      Debug.debug (fun () -> sprintf "fold terms (%s)\n" (string_of_term_list args'));
      let body = (IdMap.find pc.pred_name state.prog.prog_preds).pred_body in
      match body with
      | Some b ->
        Debug.debug (fun () -> sprintf "body (%s)\n" (string_of_format pr_spec_form b));
        let ids = (IdMap.find pc.pred_name state.prog.prog_preds).pred_contract.contr_formals in 
        let sm =
          List.combine ids args' 
          |> List.fold_left (fun sm (id, a) -> IdMap.add id a sm) IdMap.empty 
        in
        let body' = subst_spec_form sm b.spec_form in
        Debug.debug (fun () -> sprintf "body[x -> e] (%s)\n" (string_of_format pr_sspec_form body'));
        consume state' state'.heap body' (fun state2 heap' snap ->
          produce_sl_form state2 (SlUtil.mk_pred pc.pred_name pc.pred_args) snap (fun state3 -> fc state3))
      | None ->
        Debug.debug (fun () -> sprintf "no body\n");
        fc state')

and execs state comms (fc: symb_state -> vresult) =
  match comms with
  | [] -> fc state
  | comm :: comms' ->
      exec state comm (fun state' ->
        execs state' comms' fc)

(* verifies that predicates are well-formed *)
let verify_pred spl_prog prog aux_axioms pred =
  let name = Prog.name_of_pred pred in
  Debug.info (fun () ->
    "Checking predicate " ^ Grass.string_of_ident name ^ "...\n");

  (** Extract formal params; havoc them into a fresh store as a *)
  let formals = Prog.formals_of_pred pred in

  let formal_terms =
    let locs = Prog.locals_of_pred pred in
    List.fold_left
      (fun acc var ->
        let srt = Grass.IdMap.find var locs in
        Grass.Var (var, srt.var_sort) :: acc)
      [] (formals)
  in

  let init_state = mk_symb_state
    (havoc empty_store formal_terms) prog pred.pred_contract in

  let body = (IdMap.find name prog.prog_preds).pred_body |> Opt.get in
  let result = produce init_state body.spec_form (fresh_snap_tree ()) (fun _ -> Result.Ok (Forms [])) in
  match result with
  | Result.Error err -> 
      Debug.debug (fun () -> sprintf "err (%s)\n" (err));
      aux_axioms, [({sp_file = ""; sp_start_line=0; sp_start_col=0; sp_end_line=0; sp_end_col=0}, err, Model.empty)]
  | Result.Ok (Forms axioms) -> 
      Debug.debug (fun () -> sprintf "VERIFY pred\n");
      let _ = List.iter (fun f -> Printf.printf "**** axioms (%s)\n" (string_of_form f)) axioms in
      axioms @ aux_axioms, []
  | Result.Ok (PCList _) -> failwith "verification of predicates never produces pc chunks" 

 
let verify_function spl_prog prog aux_axioms func =
  (* again functions are represented as predicates with a single return value *)
  (* func has info about pred_accesses which is critical for term gen, probably need to plumb this through into fun_axioms, start with empty IdSet and this should work with double, then do the recursive cases.*)
  let name = Prog.name_of_pred func in
  Debug.info (fun () ->
    "Checking function " ^ Grass.string_of_ident name ^ "...\n");
  
  (** Extract formal params; havoc them into a fresh store as a *)
  let formals_of_func = Prog.formals_of_pred in
  let returns_of_func = Prog.returns_of_pred in
  let formals = formals_of_func func in
  let returns = returns_of_func func in
  let locals = Prog.locals_of_pred func in
  let formal_terms =
    List.fold_left
      (fun acc var ->
        let srt = Grass.IdMap.find var locals in
        Grass.Var (var, srt.var_sort) :: acc)
      [] (formals)
  in
  let return_term =
      let var = List.hd returns in
        let srt = Grass.IdMap.find var (Prog.locals_of_pred func) in
         Grass.Var (var, srt.var_sort) 
  in

  let precond = 
    fold_spec_list
      mk_sep_star (mk_atom Emp []) (Prog.precond_of_pred func)
  in

  Debug.debug(fun () -> sprintf "precond XXXXX (%s)\n" (pr_spec_form_list precond));
  let postcond = 
    fold_spec_list
      mk_sep_star (mk_atom Emp []) (Prog.postcond_of_pred func)
  in

  let init_state = mk_symb_state
    (havoc empty_store formal_terms) prog func.pred_contract in

  let body = (IdMap.find name prog.prog_preds).pred_body |> Opt.get in

  (* change this to be an either type *)
  let result = produces init_state precond (fresh_snap_tree ()) (fun st ->
    let st2 = {st with store = havoc st.store [return_term]} in
    Debug.debug(fun () -> "verify_function produce body");
    produce_symb st2 body.spec_form (fresh_snap_tree ()) (fun st3 ->
        let precond_form = 
           match st.pc with
             | [] -> Option.None
             | s -> Option.Some (List.hd (remove_at 0 (get_pc_stack (List.hd s))))
        in
        let axioms = fun_axiom name formals (sort_of return_term) precond_form st3 in
        let sfs = List.map (fun f -> (mk_free_spec_form (FOL f) "" None dummy_position)) [axioms] in 
        (* need to put the formulas from the precondition on the stack and the formula we need is
         * forall x, y, z :: precond |-> f() = body try mk_sequent *)
        let prog' = {st3.prog with prog_axioms = sfs @ st3.prog.prog_axioms} in
        let st3' = {st3 with prog = prog'} in
        Debug.debug (fun () -> sprintf "VERIFY FUNCTION axiom (%s)\n" (string_of_form axioms));
        let _ = print_prog stdout prog' in
        consumes st3' postcond (fun st4 snap -> 
          (* fun_axiom can use mk_sequent to build the right axiom. *)
          Debug.debug(fun () -> sprintf "State of prod precond into st4 (%s)\n" (string_of_state st4));
          Debug.debug(fun () -> sprintf "State of prod precond into st (%s)\n" (string_of_state st));
         Result.Ok (Forms [axioms])
    )))
  in
  match result with
  | Result.Error err -> 
      Debug.debug (fun () -> sprintf "err (%s)\n" (err));
      aux_axioms, [({sp_file = ""; sp_start_line=0; sp_start_col=0; sp_end_line=0; sp_end_col=0}, err, Model.empty)]
  | Result.Ok (Forms axioms) -> 
      Debug.debug (fun () -> sprintf "VERIFY FUNCTION \n");
      let _ = List.iter (fun f -> Printf.printf "**** axioms (%s)\n" (string_of_form f)) axioms in
      axioms @ aux_axioms, []
  | Result.Ok (PCList (_, _)) -> failwith "function verification never produces pc chunks"

(** verify checks procedures are well-formed specs and the postcondition can be met by executing the body under the precondition *)
let verify spl_prog prog aux_axioms proc = 
  Debug.info (fun () ->
      "Checking procedure " ^ Grass.string_of_ident (Prog.name_of_proc proc) ^ "...\n");

  (** Extract formal params, returns; havoc them into a fresh store as a 
   * pre-processing phase *)
  let formals = Prog.formals_of_proc proc in
  Debug.debug (fun () -> sprintf "\nformals = (%s)\n" (string_of_format pr_ident_list formals));
  let returns = Prog.returns_of_proc proc in
  Debug.debug (fun () -> sprintf "\nreturns = (%s)\n" (string_of_format pr_ident_list returns));
  let formal_return_terms =
    let locs = Prog.locals_of_proc proc in
    List.fold_left
      (fun acc var ->
        let srt = Grass.IdMap.find var locs in
        Grass.Var (var, srt.var_sort) :: acc)
      [] (formals @ returns)
  in
  let precond = 
    fold_spec_list
      mk_sep_star (mk_atom Emp []) (Prog.precond_of_proc proc)
  in
  let postcond =
    fold_spec_list
      mk_sep_star (mk_atom Emp []) (Prog.postcond_of_proc proc)
  in
  let contr' = {
    proc.proc_contract with 
    contr_precond=precond;
    contr_postcond=postcond;
    } in
  let init_state = mk_symb_state
    (havoc empty_store formal_return_terms) (declare_proc prog proc) contr' in

  Debug.debug(fun() ->
      sprintf "%sInitial State:\n{%s\n}\n\n"
      lineSep (string_of_state init_state)
  );
  let result = produces init_state precond (fresh_snap_tree ())
    (fun st ->
      let st2 = { st with heap=[]; old_heap=st.heap} in
      Debug.debug(fun()-> sprintf "St2 = %s\n" (string_of_state st2));
      produces st2 postcond (fresh_snap_tree ()) (fun _ ->
           (match proc.proc_body with
           | Some body ->
              Debug.debug (fun () -> "EXEC BODY\n");
              exec st body (fun st3 ->
                let st3 = {st3 with old_heap=st.heap} in
                consumes st3 postcond (fun _ _ -> Result.Ok (Forms [])))
           | None -> Result.Ok (Forms []))
      ))
  in 
  match result with
  | Result.Error err -> 
      Debug.debug (fun () -> sprintf "err (%s)\n" (err));
      aux_axioms, [({sp_file = ""; sp_start_line=0; sp_start_col=0; sp_end_line=0; sp_end_col=0}, err, Model.empty)]
  | Result.Ok _ -> 
      aux_axioms, []
