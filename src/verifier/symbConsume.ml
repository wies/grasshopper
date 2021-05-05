(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open SymbState
open GrassUtil
open Grass
open Prog 

let check_symb_forms (state: symb_state) heap fs (fc: symb_state -> symb_heap -> term -> vresult) =
  let fset =
    List.fold_left (fun acc f ->
      GrassUtil.FormSet.add f acc)
    GrassUtil.FormSet.empty fs
  in
  let result = check state.pc state.prog (GrassUtil.smk_and (GrassUtil.FormSet.elements fset)) in
  match result with
  | Result.Error err as e -> e  
  | Result.Ok _ -> fc state heap (emp_snap) 

(* Consume pure [f] this is heap independent so we pass a Unit snap to fc
 * TODO consume SL.form list*)
let rec consumes_pure_impl state heap fs f_eval_forms (fc: symb_state -> symb_heap -> term -> vresult) =
  f_eval_forms state fs (fun state' fs' -> check_symb_forms state' heap fs' fc)

let rec consume_form_impl state heap (f: Grass.form) f_eval_form (fc: symb_state -> symb_heap -> term -> vresult) =
  f_eval_form state f (fun state' f' -> 
    check_symb_forms state' heap [f'] fc)

let rec consume_sl_symb_form_impl state heap (f: Sl.form) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sConsume SL Symb Form: %s\n State:\n{%s\n}\n\n"
    lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   check_symb_forms state heap [p] fc
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap (emp_snap) 
  | Sl.Atom (Sl.Region, [r], _) -> 
      f_eval_term state r (fun state' t' ->
        let (chunk, h') = heap_remove_by_term state.pc state.heap t' in
        fc state h' (emp_snap))
  | Sl.Atom (Sl.Region, [obj; App (FreeSym id, _, _)], _) -> 
     
     f_eval_term state obj (fun state' obj' ->
       let hc = heap_find_by_field_id state'.pc state'.heap state'.prog obj' id in
        Debug.debug(fun () -> sprintf "found heap chunk (%s)\n" (string_of_hc hc)); 
        let h' = heap_remove state'.heap state'.pc hc in 

        fc {state' with heap=h'} h' (get_heap_chunk_snap hc))
  | Sl.Atom (Sl.Region, ts, _) -> todo "region ts" 
  | Sl.Atom (Sl.Pred id, ts, _) -> 
     f_eval_terms state ts (fun state' ts' ->
        let pred_chunk = heap_find_pred_chunk state'.pc state'.heap id ts' in
        let h' = heap_remove state'.heap state'.pc pred_chunk in 

        fc {state' with heap=h'} h' (get_heap_chunk_snap pred_chunk))
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n");
    consume_sl_symb_form_impl state heap f1 f_eval_form f_eval_terms f_eval_term (fun st2 h2 s1 ->
      consume_sl_symb_form_impl st2 h2 f2 f_eval_form f_eval_terms f_eval_term (fun st3 h3 s2 ->
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

let rec consume_sl_form_impl state heap (f: Sl.form) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sConsume SL Form: %s\n State:\n{%s\n}\n\n"
    lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug(fun () -> "Pure\n");
   consume_form_impl state heap p f_eval_form fc 
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap (emp_snap) 
  | Sl.Atom (Sl.Region, [obj; App (FreeSym id, _, _)], _) -> 
      f_eval_term state obj (fun state' t' ->
        let chunk = heap_find_by_field_id state.pc state.heap state.prog t' id in
        let h' = heap_remove state.heap state.pc chunk in
        fc state h' (get_heap_chunk_snap chunk))
  | Sl.Atom (Sl.Region, ts, _) -> fc state heap (emp_snap)
  | Sl.Atom (Sl.Pred id, ts, _) -> 
     f_eval_terms state ts (fun state' ts' ->
        let pred_chunk = heap_find_pred_chunk state'.pc state'.heap id ts' in
        let h' = heap_remove state'.heap state'.pc pred_chunk in 
        fc {state' with heap=h'} h' (get_heap_chunk_snap pred_chunk))
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n");
     consume_sl_form_impl state heap f1 f_eval_form f_eval_terms f_eval_term (fun st2 h2 s1 ->
       consume_sl_form_impl st2 h2 f2 f_eval_form f_eval_terms f_eval_term (fun st3 h3 s2 ->
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

let consume_impl state heap (sf: Prog.spec_form) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> vresult) =
  match sf with
  | Prog.FOL fol -> consume_form_impl state heap fol f_eval_form fc
  | Prog.SL slf -> consume_sl_form_impl state heap slf f_eval_form f_eval_terms f_eval_term fc

let consume_symb_impl state heap (sf: Prog.spec_form) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> vresult) =
  match sf with
  | Prog.FOL fol -> consume_form_impl state heap fol f_eval_form fc
  | Prog.SL slf -> consume_sl_symb_form_impl state heap slf f_eval_form f_eval_terms f_eval_term fc

let rec consumes_sf_impl state heap (sf: Prog.spec_form list) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> vresult) =
  match sf with
  | [] -> fc state heap (emp_snap)
  | [hd] -> consume_symb_impl state state.heap hd f_eval_form f_eval_terms f_eval_term (fun state' h' snap' -> fc state' h' snap')
  | hd :: sfs' -> 
      consume_symb_impl state state.heap hd f_eval_form f_eval_terms f_eval_term (fun state' h' snap' ->
        consumes_sf_impl state state.heap sfs' f_eval_form f_eval_terms f_eval_term (fun state'' h'' snap'' -> fc state'' h'' (snap_pair snap' snap'')))

let rec consumes_symb_impl state (assns: Prog.spec list) f_eval_form f_eval_terms f_eval_term fc =
  match assns with
  | [] -> fc state (emp_snap)
  | hd :: assns' -> 
      consume_symb_impl state state.heap hd.spec_form f_eval_form f_eval_terms f_eval_term (fun state' h' snap' ->
        consumes_symb_impl state assns' f_eval_form f_eval_terms f_eval_term fc)

let rec consumes_sl_form_impl state heap (forms: Sl.form list) f_eval_form f_eval_terms f_eval_term fc =
  match forms with
  | [] -> fc state heap (emp_snap)
  | hd :: forms' -> 
      consume_sl_form_impl state state.heap hd f_eval_form f_eval_terms f_eval_term (fun state' h' snap' ->
        consumes_sl_form_impl state state.heap forms' f_eval_form f_eval_terms f_eval_term fc)

let rec consumes_impl state (assns: Prog.spec list) f_eval_form f_eval_terms f_eval_term fc =
  match assns with
  | [] -> fc state (emp_snap)
  | hd :: assns' -> 
      consume_impl state state.heap hd.spec_form f_eval_form f_eval_terms f_eval_term (fun state' h' snap' ->
        consumes_impl state assns' f_eval_form f_eval_terms f_eval_term fc)
