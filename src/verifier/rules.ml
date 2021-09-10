open GrassUtil
open Grass
open Printf
open Prog
open SymbBranch
open SymbState
open SlUtil
open Util

let produce_symb_form state f snp (fc: symb_state -> vresult) =
  let s2 = { state with pc = pc_add_path_cond state.pc f} in
  let s3 = {s2 with pc = pc_add_path_cond s2.pc 
    (GrassUtil.mk_atom Grass.Eq [snp; emp_snap])}
  in
  fc s3

let check_symb_forms (state: symb_state) heap fs (fc: symb_state -> symb_heap -> term -> vresult) =
  let fset =
    List.fold_left (fun acc f ->
      GrassUtil.FormSet.add f acc)
    GrassUtil.FormSet.empty fs
  in
  let pc = infer_diseq state.heap state.pc in
  let result = check pc state.prog (GrassUtil.smk_and (GrassUtil.FormSet.elements fset)) in
  match result with
  | Result.Error err as e -> e  
  | Result.Ok _ -> fc state heap (emp_snap) 

(* maximum depth recursive predicates will be unfolded *)
let rec_unfolding_limit = 1

(* Extract the formal input parameter identifiers of a procedure foo in program prog *)
let formal_ids_of foo prog =
  let foo_contr =(find_proc prog foo).proc_contract in 
  foo_contr.contr_formals

let formal_ids_of_pred foo pred =
  let foo_contr =(find_pred pred foo).pred_contract in 
  foo_contr.contr_formals

let precond_of foo prog =
  (find_proc prog foo).proc_contract.contr_precond

let subst_spec_form subst_map sf =
  match sf with
  | SL slf -> SL (SlUtil.subst_consts subst_map slf)
  | FOL f -> FOL (GrassUtil.subst_consts subst_map f)

let subst_spec_form subst_map sf =
  match sf with
  | SL slf -> SL (SlUtil.subst_consts subst_map slf)
  | FOL f -> FOL (GrassUtil.subst_consts subst_map f)

let pr_sspec_form_list sfl =
  sfl
  |> List.map (fun v -> (string_of_format pr_sspec_form v))
  |> String.concat ", "
  |> sprintf "[%s]"

(* Substitutes identifiers of a spec list with other terms according to substitution map [subst_map]. *)
let subst_spec_list subst_map sl =
  List.map (fun s -> subst_spec_form subst_map s.spec_form) sl

let fold_spec_list f acc specs =
  let folded =List.fold_left (fun facc a ->
    match a with
    | SL slf -> mk_sep_star facc  slf
    | FOL f -> mk_sep_star facc (mk_pure f))
    acc (List.map (fun s -> s.spec_form) specs)
  in
  match specs with 
  | [] -> []
  | _ -> [{(List.hd (List.rev specs)) with spec_form=SL folded}]

let subst_spec_list_formals state sl pred args =
  let sm = 
    List.combine (formal_ids_of_pred pred state.prog) args
    |> List.fold_left (fun sm (f, a) -> IdMap.add f a sm) IdMap.empty 
  in
  subst_spec_list sm sl

(* Production rules that inhale formulas assertions into symbolic state *)
let rec produce_symb_forms state fs snp (fc: symb_state -> vresult) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_symb_form state hd snp (fun state' ->
        produce_symb_forms state' fs' snp fc)

and produce_form state (f: Grass.form) snp (fc: symb_state -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sProduce Form: %s\n Current State:\n{%s\n}\n\n"
    lineSep (string_of_form f) (string_of_state state));
  eval_form state f (fun state' f' -> 
    produce_symb_form state' f' snp fc)

and produce_sl_forms state (fs: Sl.form list) snps (fc: symb_state -> vresult) =
  match fs, snps with
  | [], [] -> fc state
  | hd :: fs', s :: snps' ->
      produce_sl_form state hd s (fun state' ->
        produce_sl_forms state' fs' snps' fc)

and produce_sl_form state (f: Sl.form) snp (fc: symb_state -> vresult) =
   Debug.debug(fun() ->
      sprintf "%sProduce SL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug(fun () -> sprintf "PURE \n");
   produce_form state p snp fc
  | Sl.Atom (Sl.Region, [obj; App (FreeSym id, _, _)], a) ->
     Debug.debug(fun() -> sprintf "Region snap %s\n" (string_of_term snp));
     eval_term state obj (fun state' obj' ->
       let hc = mk_heap_chunk_obj id obj' snp in 
        let h, stack = heap_add state'.heap state'.pc hc in
        fc {state' with heap=h; pc = stack})
  | Sl.Atom (Sl.Region, ts, a) -> 
      Debug.debug (fun () -> sprintf "region ts (%s)\n" (string_of_term_list ts));
      todo "region terms ts"
  | Sl.Atom (Sl.Emp, [], _) ->
      fc state
  | Sl.Atom (Sl.Emp, ts, _) -> todo "Atom emp ts"
  | Sl.Atom (Sl.Pred id, ts, _) -> 
      eval_terms state ts (fun state' ts' ->
        let pred_chunk = mk_heap_chunk_obj_pred id ts' snp in
        let h, stack = heap_add state'.heap state'.pc pred_chunk in
        fc {state' with heap=h; pc = stack})
  | Sl.SepOp (op, f1, f2, _) ->
     produce_sl_form state f1 (snap_first snp) (fun state' ->
       produce_sl_form state' f2 (snap_second snp) fc)
  | Sl.BoolOp (op, fs, p) ->
        let snaps = List.map (fun _ -> (fresh_snap_tree ())) fs in
        produce_sl_forms state fs snaps fc
  | Sl.Binder (b, [], f, _) ->
      produce_sl_form state f snp fc
  | Sl.Binder (b, ts, f, _) -> todo "Binder"

and produce_sl_symb_forms state (fs: Sl.form list) snp (fc: symb_state -> vresult) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_sl_symb_form state hd snp (fun state' ->
        produce_sl_symb_forms state' fs' snp fc)

and produce_sl_symb_form state (f: Sl.form) snp (fc: symb_state -> vresult) =
   Debug.debug(fun() ->
      sprintf "%sProduce SYMB SL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug(fun () -> sprintf "PURE \n");
   produce_symb_form state p snp fc
  | Sl.Atom (Sl.Region, ts, a) -> 
      Debug.debug (fun () -> sprintf "region ts (%s)\n" (string_of_term_list ts));
      todo "SL symb region"
  | Sl.Binder (b, [], f, _) ->
      produce_sl_symb_form state f snp fc
  | Sl.SepOp (op, f1, f2, _) ->
     produce_sl_symb_form state f1 (snap_first snp) (fun state' ->
       produce_sl_symb_form state' f2 (snap_second snp) fc)
  | Sl.BoolOp (op, fs, p) ->
        produce_sl_symb_forms state fs snp fc
  | _ -> todo "add cases for produce_sl_symb_form"

and produce state sf snp (fc: symb_state -> vresult) =
  match sf with
  | Prog.FOL fol -> produce_form state fol snp fc
  | Prog.SL slf -> produce_sl_form state slf snp fc

and produce_symb state sf snp (fc: symb_state -> vresult) : vresult =
  match sf with
  | Prog.FOL fol -> produce_form state fol snp fc
  | Prog.SL slf -> produce_sl_symb_form state slf snp fc

(** produce_specs is the entry point for producing an assertion list (spec list),
    this function iterates over the assns calling produce_spec_form on each spec. *)
and produces state (assns: Prog.spec list) snp fc : vresult =
  match assns with
  | [] -> fc state
  | hd :: assns' -> produce state hd.spec_form snp (fun state' -> produces state' assns' snp fc) 

(* Consume pure [f] this is heap independent so we pass a Unit snap to fc
 * TODO consume SL.form list*)
and consumes_pure state heap fs (fc: symb_state -> symb_heap -> term -> vresult) =
  eval_forms state fs (fun state' fs' -> check_symb_forms state' heap fs' fc)

and consume_form state heap (f: Grass.form) (fc: symb_state -> symb_heap -> term -> vresult) =
  eval_form state f (fun state' f' -> 
    check_symb_forms state' heap [f'] fc)

and consume_sl_symb_form state heap (f: Sl.form) (fc: symb_state -> symb_heap -> term -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sConsume SL Symb Form: %s\n State:\n{%s\n}\n\n"
    lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   check_symb_forms state heap [p] fc
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap (emp_snap) 
  | Sl.Atom (Sl.Region, [r], _) -> 
      eval_term state r (fun state' t' ->
        let (chunk, h') = heap_remove_by_term state.pc state.heap t' in
        fc state h' (emp_snap))
  | Sl.Atom (Sl.Region, [obj; App (FreeSym id, _, _)], _) -> 
     eval_term state obj (fun state' obj' ->
       let hc = heap_find_by_field_id state'.pc state'.heap state'.prog obj' id in
        Debug.debug(fun () -> sprintf "found heap chunk (%s)\n" (string_of_hc hc)); 
        let h' = heap_remove state'.heap state'.pc hc in 
        fc {state' with heap=h'} h' (get_heap_chunk_snap hc))
  | Sl.Atom (Sl.Region, ts, _) -> todo "region ts" 
  | Sl.Atom (Sl.Pred id, ts, _) -> 
      Debug.debug(fun () -> "Atom Pred\n");
      eval_terms state ts (fun state' ts' ->
        let pred_chunk = heap_find_pred_chunk state'.pc state'.heap id ts' in
        let h' = heap_remove state'.heap state'.pc pred_chunk in 
        fc {state' with heap=h'} h' (get_heap_chunk_snap pred_chunk))
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n");
    consume_sl_symb_form state heap f1 (fun st2 h2 s1 ->
      consume_sl_symb_form st2 h2 f2 (fun st3 h3 s2 ->
        fc st3 h3 (snap_pair s1 s2)))
  | Sl.SepOp (Sl.SepIncl, _, _, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n");
     fc state heap (emp_snap)
  | Sl.SepOp (Sl.SepPlus, _, _, _) ->
     fc state heap (emp_snap)
  | Sl.BoolOp (Grass.And, fs, _) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
     fc state heap (emp_snap)
  | Sl.BoolOp (Grass.Or, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
     fc state heap (emp_snap)
  | Sl.BoolOp (Grass.Not, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
     fc state heap (emp_snap)
  | Sl.Binder (Grass.Forall, ts, f, _) -> fc state heap (emp_snap)
  | Sl.Binder (Grass.Exists, ts, f, _) -> fc state heap (emp_snap)

and consume_sl_form state heap (f: Sl.form) (fc: symb_state -> symb_heap -> term -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sConsume SL Form: %s\n State:\n{%s\n}\n\n"
    lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug(fun () -> "Pure\n");
   consume_form state heap p fc 
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap (emp_snap) 
  | Sl.Atom (Sl.Region, [obj; App (FreeSym id, _, _)], _) -> 
      eval_term state obj (fun state' t' ->
        let chunk = heap_find_by_field_id state.pc state.heap state.prog t' id in
        let h' = heap_remove state.heap state.pc chunk in
        fc state h' (get_heap_chunk_snap chunk))
  | Sl.Atom (Sl.Region, ts, _) -> fc state heap (emp_snap)
  | Sl.Atom (Sl.Pred id, ts, _) -> 
     Debug.debug(fun () -> "Pred\n");
     eval_terms state ts (fun state' ts' ->
        let pred_chunk = heap_find_pred_chunk state'.pc state'.heap id ts' in
        let h' = heap_remove state'.heap state'.pc pred_chunk in 
        fc {state' with heap=h'} h' (get_heap_chunk_snap pred_chunk))
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n");
     consume_sl_form state heap f1 (fun st2 h2 s1 ->
       consume_sl_form st2 h2 f2 (fun st3 h3 s2 ->
         fc st3 h3 (snap_pair s1 s2)))
  | Sl.SepOp (Sl.SepIncl, _, _, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n");
     fc state heap (emp_snap)
  | Sl.SepOp (Sl.SepPlus, _, _, _) ->
     fc state heap (emp_snap)
  | Sl.BoolOp (Grass.And, fs, _) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
     fc state heap (emp_snap)
  | Sl.BoolOp (Grass.Or, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
     fc state heap (emp_snap)
  | Sl.BoolOp (Grass.Not, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
     fc state heap (emp_snap)
  | Sl.Binder (Grass.Forall, ts, f, _) -> fc state heap (emp_snap)
  | Sl.Binder (Grass.Exists, ts, f, _) -> fc state heap (emp_snap)

and consume state heap (sf: Prog.spec_form) (fc: symb_state -> symb_heap -> term -> vresult) =
  match sf with
  | Prog.FOL fol -> consume_form state heap fol fc
  | Prog.SL slf -> consume_sl_form state heap slf fc

and consume_symb state heap (sf: Prog.spec_form) (fc: symb_state -> symb_heap -> term -> vresult) =
  match sf with
  | Prog.FOL fol -> consume_form state heap fol fc
  | Prog.SL slf -> consume_sl_symb_form state heap slf fc

and consumes_sf state heap (sf: Prog.spec_form list) (fc: symb_state -> symb_heap -> term -> vresult) =
  match sf with
  | [] -> fc state heap (emp_snap)
  | [hd] -> consume_symb state state.heap hd (fun state' h' snap' -> fc state' h' snap')
  | hd :: sfs' -> 
      consume_symb state state.heap hd (fun state' h' snap' ->
        consumes_sf state state.heap sfs' (fun state'' h'' snap'' -> fc state'' h'' (snap_pair snap' snap'')))

and consumes_symb state (assns: Prog.spec list) fc =
  match assns with
  | [] -> fc state (emp_snap)
  | hd :: assns' -> 
      consume_symb state state.heap hd.spec_form (fun state' h' snap' ->
        consumes_symb state assns' fc)

and consumes_sl_form state heap (forms: Sl.form list) fc =
  match forms with
  | [] -> fc state heap (emp_snap)
  | hd :: forms' -> 
      consume_sl_form state state.heap hd (fun state' h' snap' ->
        consumes_sl_form state state.heap forms' fc)

and consumes state (assns: Prog.spec list) fc =
  match assns with
  | [] -> fc state (emp_snap)
  | hd :: assns' -> 
      consume state state.heap hd.spec_form (fun state' h' snap' ->
        consumes state assns' fc)

(** eval_terms evaluates a term list element-wise using the eval
  functions below, accumulating the resulting symbolic terms into the symb_ts list. *)
and eval_terms state (ts: term list) (fc: symb_state -> term list -> vresult) =
  let rec eeval state tts ts fc =
    match tts with
    | [] -> fc state (List.rev ts) (* reverse due to the cons op below *)
    | hd :: ts' ->
        eval_term state hd (fun state' t ->
          eeval state' ts' (t :: ts) fc)
  in
  eeval state ts [] fc

and eval_term state t (fc: symb_state -> term -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sEval Term: %s\n State:\n{%s\n}\n\n"
    lineSep (string_of_term t) (string_of_state state));
  match t with
  | Var (id1, srt1) as t->
    Debug.debug(fun() -> sprintf "Var Term\n");
    fc state (maybe_find_symb_val state.store t)
  | App (Value i, [], srt) -> todo "eval Value"
  | App (Union, [], srt) -> todo "eval Union"
  | App (Inter, [], srt) -> todo "eval Inter"
  | App (Read, [map; t], srt) ->
      Debug.debug(fun () -> sprintf "field read sort (%s)\n" (string_of_sort srt));
      (match map with
      | (App (FreeSym id, [], srt1) | Var (id, srt1)) ->
          eval_term state t (fun state' t' ->
            let hc = heap_find_by_field_id state.pc state.heap state.prog t' id in
            Debug.debug(fun () -> sprintf "found heap chunk (%s)\n" (string_of_hc hc)); 
            let v = get_heap_chunk_snap hc in 
            fc state' (mk_f_snap (get_map_range_sort srt1) v))
      | _ -> todo "map catch all")
  | App (Read, map :: t :: ts, srt) -> todo "eval read"
  | App (Write, [map; t1; t2], srt) -> todo "eval write"
  | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq 
          | SubsetEq | LtEq | GtEq | Lt | Gt | Elem | AndTerm | OrTerm as sym), [t1; t2], srt) ->
      eval_term state t1 (fun state1 t3 ->
        eval_term state1 t2 (fun state2 t4 ->
          fc state2 (App (sym, [t3; t4], srt))))
  | App (Length, [t], srt) -> todo "eval Length"
  | App (ArrayCells, [t], srt) -> todo "eval ArrayCells"
  | App (SetEnum, [t], srt) ->
    eval_term state t (fun state' t' -> fc state' (mk_f_snap srt t'))
  | App (SetEnum, ts, srt) -> todo "set enum non-singleton"
  | App (Destructor d, [t], srt) -> todo "eval Destructor"
  | App (FreeSym id1, [], srt1) -> 
      Debug.debug(fun() -> sprintf "FreeSym [] srt: %s\n" (string_of_sort srt1));
    (match find_symb_val state.store id1 with
    | Var (id2, srt2) as tt -> 
        Debug.debug(fun () -> sprintf "term (%s)\n" (string_of_term tt));
        if srt1 = srt2
        then fc state tt
        else Error (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | App (IntConst n, ts, Int) as tt ->
        Debug.debug( fun () -> sprintf "IntConst (%s)\n" (string_of_term tt));
        fc state tt
    | _ as tt -> fc state tt)
  | App (FreeSym id, [t], srt) ->
      Debug.debug(fun() -> sprintf "FreeSym ts snp\n");
      fc state t
  | App (FreeSym id, ts, srt1) ->
      Debug.debug(fun() -> sprintf "FreeSym ts (%s) srt: %s\n" (string_of_term_list ts) (string_of_sort srt1));
      eval_terms state ts (fun st' ts' ->
        let precond = 
          fold_spec_list
            mk_sep_star (mk_atom Emp []) (Prog.precond_of_pred (IdMap.find id state.prog.prog_preds))
        in
        let precond_sf' = 
          subst_spec_list_formals st' precond id ts'
        in
        consumes_sf st' st'.heap precond_sf' (fun state2' heap snap -> 
          fc {state2' with heap = st'.heap} (App (FreeSym id, ts' @ [snap], srt1))))
  | App (IntConst n, [], srt) as i -> 
        Debug.debug (fun () -> sprintf "IntConst (%s)\n" (string_of_term i));
        fc state i
  | App (Null, [], srt) as t -> fc state t
  | App (Old, [ts], srt) ->
      (* TODO: move f_snap inj func application to consume where we 
       * pull the snapshot from the hc*)
     let state2 = {state with heap=state.old_heap} in
     eval_term state2 ts (fun state2' ts' ->
       fc {state2' with heap=state.heap} ts')
  | App (BoolConst b, ts, srt) as f -> fc state f
  | App (Ite, [cond; e1; e2], srt) ->
      eval_term state cond (fun state2 cond' ->
        join state2 (fun state3 q_join ->
          branch state3 (Atom (cond', [])) 
            (fun state3' -> eval_term state3' e1 q_join)
            (fun state3' -> eval_term state3' e2 q_join))
        (fun state3 v -> 
          match v with
          | [([Atom (e1', _)], e2'); ([_], e3')] ->
          (* look at what form e1' and see if it's singleton term Bool. *)
            fc state3 (App (Ite, [e1'; e2'; e3'], srt))
          | ll ->
              let _ = List.map (fun (fs, ts) ->
              Debug.debug(fun () -> sprintf "(fs: %s, ts: %s)\n" (string_of_forms fs) (string_of_term ts))) ll
              in
            failwith "die"))
  | App (Unfolding, [App(FreeSym id, args, Bool); in_term], srt) -> 
      let state1 = incr_pred_cycle state id in
      if count_cycles state < rec_unfolding_limit then
        let pred = IdMap.find id state1.prog.prog_preds in
        let formals = formals_of_pred pred in
        let formal_terms =
          let locs = Prog.locals_of_pred pred in
          List.fold_left
            (fun acc var ->
              let srt = Grass.IdMap.find var locs in
              Grass.Var (var, srt.var_sort) :: acc)
            [] (formals)
        in
        let _ = List.map (fun t -> Debug.debug(fun () -> sprintf "Formal term %s" (string_of_term t))) formal_terms in
        let _ = List.map (fun t -> Debug.debug(fun () -> sprintf "Arg term %s" (string_of_term t))) args in
        eval_terms state1 args (fun state2 ts' ->
          (* body[xs -> ts']*)
          let sm = 
            List.combine formals ts'
            |> List.fold_left (fun sm (id, t) -> IdMap.add id t sm) IdMap.empty 
          in
          (* use subst_spec in prog.ml  on the body.*)
          let bdy = match pred.pred_body with
            | Some b -> subst_spec sm b
            | None -> failwith "Unfolding on empty preds not allowed"
          in
         (* let acc_pred = mk_heap_chunk_obj_pred id ts' (fresh_snap) in*) 
          consume state2 state2.heap bdy.spec_form (fun state3 _ snap ->
            join_prime state3 (fun state4 q_join -> 
                produce state4 bdy.spec_form snap (fun state5 ->
                  eval_term state5 in_term (fun state6 in_term' ->
                    let state6' = {state6 with heap=state2.heap} in
                    q_join state6' in_term'))) fc))
      else
        let id = fresh_ident "recunf" in
        let recunf = mk_free_app (sort_of in_term) id state1.qvs in
        fc state1 recunf 
  | App (symb, ts, srt) -> todo "eval_term catch all"

(** eval_forms evaluates a formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
and eval_forms state (fs: form list) (fc: symb_state -> form list -> vresult) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_form state f (fc: symb_state -> form -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sEval Form: %s\n State:\n{%s\n}\n\n"
    lineSep (string_of_form f) (string_of_state state));
  match f with
  | Atom (t, a) -> 
    Debug.debug(fun () ->
      sprintf "***** Atom \n");
      eval_term state t (fun state' t' ->
        fc state' (Atom (t', a)))
  | BoolOp (op, fs) ->
    Debug.debug(fun () ->
      sprintf "***** BoolOp\n");
    eval_forms state fs (fun state' fs' ->
      fc state' (BoolOp (op, fs')))
  | Binder (binder, [], f, a) -> 
      Debug.debug(fun() -> "*** BINDER\n");
      eval_form state f (fun state' f' ->
        fc state (Binder (binder, [], f', a)))
  | Binder (binder, ts, f, _) -> todo "eval binder catch all"

(** eval_sl_forms evaluates a sl formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
and eval_sl_forms state (fs: Sl.form list) (fc: symb_state -> Sl.form list -> vresult) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_sl_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_sl_form state f (fc: symb_state -> Sl.form -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sEval SL Form: %s\n State:\n{%s\n}\n\n"
    lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (ff, pos) ->
      eval_form state ff (fun state' ff' ->
        fc state' (Sl.Pure (ff', pos)))
  | Sl.Atom (symb, ts, pos) -> 
      eval_terms state ts (fun state' ts' ->
        fc state' (Sl.Atom (symb, ts', pos)))
  | Sl.SepOp (sop, f1, f2, pos) ->
      eval_sl_form state f1 (fun state2 f3 ->
        eval_sl_form state2 f2 (fun state3 f4 ->
          fc state3 (Sl.SepOp (sop, f3, f4, pos))))
  | Sl.BoolOp (op, slfs, pos) ->
    eval_sl_forms state slfs (fun state' slfs' ->
      fc state' (Sl.BoolOp (op, slfs', pos)))
  | Sl.Binder (b, ids, slf, pos) -> todo "sl binder eval"

and eval_spec_form state sf (fc: symb_state -> form -> vresult) =
  match sf with
  | Prog.FOL fol -> eval_form state fol fc
  | Prog.SL slf -> failwith "cannot call eval_spec_form on an sl formula"
