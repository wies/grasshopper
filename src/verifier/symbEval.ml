(** {5 Symbolic evaluation of terms and formulas inspired by Viper's Silicon} *)

open Printf
open Util
open GrassUtil
open Grass
open Prog
open SymbState
open SymbConsume
open SlUtil 

(* Extract the formal input parameter identifiers of a procedure foo in program prog *)
let formal_ids_of foo prog =
  let foo_contr =(find_proc prog foo).proc_contract in 
  foo_contr.contr_formals

let precond_of foo prog =
  (find_proc prog foo).proc_contract.contr_precond

let subst_spec_form subst_map sf =
  match sf with
  | SL slf -> SlUtil.subst_consts subst_map slf
  | FOL f -> GrassUtil.subst_consts subst_map f

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
  [{(List.hd (List.rev specs)) with spec_form=SL folded}]

let subst_spec_list_formals state sl proc args =
  let sm = 
    List.combine (formal_ids_of proc state.prog) args
    |> List.fold_left (fun sm (f, a) -> IdMap.add f a sm) IdMap.empty 
  in
  subst_spec_list sm sl

(** eval rules *)
let string_of_idset s =
  IdSet.elements s
  |> List.map (fun e -> string_of_ident e)
  |> String.concat ", "
  |> sprintf "[%s]"

let eval_term state (t: term) (fc: symb_state -> term -> 'a option) =
  fc state t

let rec eval_terms state (ts: term list) (fc: symb_state -> term list -> 'a option) =
  let rec eeval state tts ts fc =
    match tts with
    | [] -> fc state (List.rev ts) (* reverse due to the cons op below *)
    | hd :: tts' ->
        eval_term state hd (fun state' t ->
          eeval state' tts' (t :: ts) fc)
  in
  eeval state ts [] fc

and consumes_sf state (assns: spec list) fc =
  consumes_sf_impl state assns eval_terms eval_term fc

and consume_symb_sf state heap (sf: symb_spec_form) (fc: symb_state -> symb_heap -> term -> 'a option) =
  consume_symb_sf_impl state heap sf eval_terms eval_term fc

and consume_symb_sl_form state heap (f: symb_sl_form) (fc: symb_state -> symb_heap -> term -> 'a option) =
  consume_symb_sl_form_impl state heap f eval_terms eval_term fc

(** eval_terms evaluates a term list element-wise using the eval
  functions below, accumulating the resulting symbolic terms into the symb_ts list. *)
let rec eval_terms state (ts: term list) (fc: symb_state -> term list -> 'a option) =
  let rec eeval state tts ts fc =
    match tts with
    | [] -> fc state (List.rev ts) (* reverse due to the cons op below *)
    | hd :: ts' ->
        eval_term state hd (fun state' t ->
          eeval state' ts' (t :: ts) fc)
  in
  eeval state ts [] fc

and eval_term state t (fc: symb_state -> term -> 'a option) =
  Debug.debug(fun() ->
    sprintf "%sEval Term: %s\n State:\n{%s\n}\n\n"
    lineSep (string_of_term t) (string_of_state state));
  match t with
  | Var (id1, srt1) ->
    Debug.debug(fun() -> sprintf "Var Term\n");
    (match find_symb_val state.store id1 with
    | Var (id2, srt2) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | _ -> raise_err "unreachable found symbval that isn't a Var")
  | App (Value i, [], srt) -> todo "eval Value"
  | App (Union, [], srt) -> todo "eval Union"
  | App (Inter, [], srt) -> todo "eval Inter"
  | App (Read, [map; t], srt) ->
      (match map with
      | (App (FreeSym id, [], srt1) | Var (id, srt1)) ->
          eval_term state t (fun state' t' ->
            let hc = heap_find_by_symb_term state.pc state.heap t' in
            let h' = heap_remove state.heap state.pc hc in
            let v = 
              (match maybe_find_symb_val (get_field_store hc) id with
              | Some y -> y 
              | None -> mk_free_app srt1 (fresh_ident "v") [])
            in
            let v_map = 
              match v with
              | App (FreeSym vfield, _, _) -> vfield
              | _ -> raise_err "unexpected symb term in eval read"
            in
            let hc_updated = add_to_heap_chunk_map hc id v in
            let h_new, stack = heap_add h' state.pc hc_updated in
            fc {state with heap=h_new; pc=stack} (App (FreeSym v_map, [t'], srt)))
      | _ -> todo "map catch all")
  | App (Read, map :: t :: ts, srt) -> todo "eval read"
  | App (Write, [map; t1; t2], srt) -> todo "eval write"

  | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq | SubsetEq | LtEq | GtEq | Lt | Gt | Elem | AndTerm | OrTerm as sym), [t1; t2], srt) ->
      eval_term state t1 (fun state1 t3 ->
        eval_term state1 t2 (fun state2 t4 ->
          fc state2 (App (sym, [t3; t4], srt))))
  | App (Length, [t], srt) -> todo "eval Length"
  | App (ArrayCells, [t], srt) -> todo "eval ArrayCells"
  | App (SetEnum, [t], srt) ->
    eval_term state t (fun state' t' -> fc state' t')
  | App (SetEnum, ts, srt) -> todo "set enum non-singleton"
  | App (Destructor d, [t], srt) -> todo "eval Destructor"
  | App (FreeSym id1, [], srt1) -> 
      Debug.debug(fun() -> sprintf "FreeSym [] srt: %s\n" (string_of_sort srt1));
    (match find_symb_val state.store id1 with
    | Var (id2, srt2) as tt -> 
        if srt1 = srt2
        then fc state tt
        else raise_err (sprintf "sorts are not equal (%s) != (%s), this should never happen!"
          (string_of_sort srt1) (string_of_sort srt2))
    | App (IntConst n, ts, Int) as tt ->
        Debug.debug( fun () -> sprintf "IntConst (%s)\n" (string_of_term tt));
        fc state tt
    | _ as tt -> fc state tt)
  | App (FreeSym id, ts, srt1) -> 
      Debug.debug(fun() -> sprintf "FreeSym ts (%s) srt: %s\n" (string_of_terms ts) (string_of_sort srt1));
      eval_terms state ts (fun state' ts' ->
        let precond' = fold_spec_list mk_sep_star (mk_atom Emp []) (precond_of id state'.prog) in
        let precond_symb_sf' = 
          subst_spec_list_formals state precond' id ts' 
        in
        fc state' (App (Old, ts', srt1)))

        consumes_symb_sf state' precond_symb_sf' (fun state2' _ ->
          let proc_contr = (IdMap.find id state.prog.prog_procs).proc_contract in
            
          Debug.debug(fun () -> sprintf "state %s\n" (string_of_state state2'));
          let state3' = {state2' with store = store'} in

          (* fold multiple postcondition specs into 1 for the callee *)
          let postcond' = fold_spec_list mk_sep_star (mk_atom Emp []) (postcond_of id state'.prog)in
          let post_symbf' =
            let p =
              subst_spec_list_formals state3' postcond' id ts'
            in
            subst_spec_list_return_ids state3' p id lhs
          in
          Debug.debug(fun () -> sprintf "\nPostcond[x -> e'][y->z] = %s\n" (string_of_symb_spec_list post_symbf'));
          produces_symb_sf state4' post_symbf' (fresh_snap_tree ()) (fun state4' -> fc state4'))
  | App (IntConst n, [], srt) as i -> 
        Debug.debug (fun () -> sprintf "IntConst (%s)\n" (string_of_term i));
        fc state i
  | App (Null, [], srt) as t-> fc state (Symbt t)
  | App (Old, ts, srt) ->
     let state2 = {state with store=state.old_store} in
     eval_terms state2 ts (fun state2' ts' ->
       fc state2' (App (Old, ts', srt)))
  | App (BoolConst b, ts, srt) as f -> fc state f
  | App (symb, ts, srt) -> todo "eval_term catch all"

(** eval_forms evaluates a formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_forms state (fs: form list) (fc: symb_state -> symb_form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_form state hd (fun state' f ->
          eeval state' ffs' (form_of f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_form state f (fc: symb_state -> symb_form -> 'a option) =
  Debug.debug(fun() ->
    sprintf "%sEval Form: %s\n State:\n{%s\n}\n\n"
    lineSep (string_of_form f) (string_of_state state));
  match f with
  | Atom (t, a) -> 
      eval_term state t (fun state' t' ->
        fc state' (Atom (term_of t', a)))
  | BoolOp (op, fs) ->
    eval_forms state fs (fun state' fs' ->
      fc state' (BoolOp (op, fs')))
  | Binder (binder, [], f, a) -> fc state (Symbf (Binder (binder, [], f, a)))
  | Binder (binder, ts, f, _) -> todo "eval binder catch all"

(* Handles a cyclical dependency *)
and consumes state (assns: Prog.spec list) fc =
  consumes_impl state assns eval_form eval_terms eval_term fc

and consume_sl_form state heap (f: Sl.form) (fc: symb_state -> symb_heap -> term -> 'a option) =
  consume_sl_form_impl state heap f eval_form eval_terms eval_term fc

and consume_form state heap (f: Grass.form) (fc: symb_state -> symb_heap -> term -> 'a option) = 
  consume_form_impl state heap f eval_form fc

(** eval_sl_forms evaluates a sl formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_sl_forms state (fs: Sl.form list) (fc: symb_state -> sl_form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_sl_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_sl_form state f (fc: symb_state -> sl_form -> 'a option) =
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
