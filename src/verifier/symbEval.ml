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
  | SL slf -> SL (SlUtil.subst_consts subst_map slf)
  | FOL f -> FOL (GrassUtil.subst_consts subst_map f)

let subst_spec_form subst_map sf =
  match sf with
  | SL slf -> SL (SlUtil.subst_consts subst_map slf)
  | FOL f -> FOL (GrassUtil.subst_consts subst_map f)


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
            Debug.debug(fun () -> sprintf "tprime (%s)\n" (string_of_term t'));
            Debug.debug(fun () -> sprintf "tprime srt (%s)\n" (string_of_sort (sort_of t'))); 
            Debug.debug(fun () -> sprintf "srt1 (%s)\n" (string_of_sort srt1)); 
            let hc = heap_find_by_field_id state.pc state.heap state.prog t' id in
            Debug.debug(fun () -> sprintf "found heap chunk (%s)\n" (string_of_hc hc)); 
            let v = get_heap_chunk_snap hc in 
            fc state' (mk_f_snap (get_map_range_sort srt1) v))
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
    eval_term state t (fun state' t' -> fc state' (mk_f_snap srt t'))
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
  | App (FreeSym id, [t], srt1) -> 
      Debug.debug(fun() -> sprintf "FreeSym ts (%s) srt: %s\n" (string_of_term t) (string_of_sort srt1));
      fc state t
  | App (FreeSym id, ts, srt1) ->
      todo "FreeSym"
  | App (IntConst n, [], srt) as i -> 
        Debug.debug (fun () -> sprintf "IntConst (%s)\n" (string_of_term i));
        fc state i
  | App (Null, [], srt) as t -> fc state t
  | App (Old, ts, srt) ->
     let state2 = {state with store=state.old_store} in
     eval_terms state2 ts (fun state2' ts' ->
       fc state2' (mk_f_snap srt (App (Old, ts', srt))))
  | App (BoolConst b, ts, srt) as f -> fc state f
  | App (symb, ts, srt) -> todo "eval_term catch all"

(** eval_forms evaluates a formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_forms state (fs: form list) (fc: symb_state -> form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_form state f (fc: symb_state -> form -> 'a option) =
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
  | Binder (binder, [], f, a) -> fc state (Binder (binder, [], f, a))
  | Binder (binder, ts, f, _) -> todo "eval binder catch all"

(* Handles a cyclical dependency *)
and consume state heap (sf: Prog.spec_form) fc =
  consume_impl state heap sf eval_form eval_terms eval_term fc

and consume_symb state heap (sf: Prog.spec_form) fc =
  consume_symb_impl state heap sf eval_form eval_terms eval_term fc

and consumes state (assns: Prog.spec list) fc =
  consumes_impl state assns eval_form eval_terms eval_term fc

and consumes_symb state (assns: Prog.spec list) fc =
  consumes_symb_impl state assns eval_form eval_terms eval_term fc

and consume_sl_form state heap (f: Sl.form) (fc: symb_state -> symb_heap -> term -> 'a option) =
  consume_sl_form_impl state heap f eval_form eval_terms eval_term fc

and consumes_sl_form state heap (fs: Sl.form list) (fc: symb_state -> symb_heap -> term -> 'a option) =
  consumes_sl_form_impl state heap fs eval_form eval_terms eval_term fc

and consume_form state heap (f: Grass.form) (fc: symb_state -> symb_heap -> term -> 'a option) = 
  consume_form_impl state heap f eval_form fc

(** eval_sl_forms evaluates a sl formula list fs element-wise using the eval
  function below, accumulating the resulting formulas carrying symbolic values *)
let rec eval_sl_forms state (fs: Sl.form list) (fc: symb_state -> Sl.form list -> 'a option) =
  let rec eeval state ffs symb_fs fc =
    match ffs with
    | [] -> fc state (List.rev symb_fs) (* reverse due to the cons op below *)
    | hd :: ffs' ->
        eval_sl_form state hd (fun state' f ->
          eeval state' ffs' (f :: symb_fs) fc)
  in
  eeval state fs [] fc

and eval_sl_form state f (fc: symb_state -> Sl.form -> 'a option) =
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
