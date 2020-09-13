(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open SymbState
open GrassUtil
open Grass

let check_symb_forms (state: symb_state) heap fs (fc: symb_state -> symb_heap -> term -> 'a option) =
  let fset =
    List.fold_left (fun acc f ->
      GrassUtil.FormSet.add f acc)
    GrassUtil.FormSet.empty fs
  in
  let _ = check state.pc state.prog (GrassUtil.smk_and (GrassUtil.FormSet.elements fset)) in
  fc state heap (emp_snap) 

(* Consume pure [f] this is heap independent so we pass a Unit snap to fc
 * TODO consume SL.form list*)
let rec consumes_pure_impl state heap fs f_eval_forms (fc: symb_state -> symb_heap -> term -> 'a option) =
  f_eval_forms state fs (fun state' fs' ->
    check_symb_forms state' heap (List.map (fun f -> form_of f) fs') fc)

let rec consume_form_impl state heap (f: Grass.form) f_eval_form (fc: symb_state -> symb_heap -> term -> 'a option) =
  f_eval_form state f (fun state' f' -> 
    check_symb_forms state' heap [form_of f'] fc)

let rec consume_symb_form state heap (f: symb_form) (fc: symb_state -> symb_heap -> term -> 'a option) =
    check_symb_forms state heap [form_of f] fc

let rec consume_sl_form_impl state heap (f: Sl.form) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> 'a option) =
  Debug.debug(fun() ->
    sprintf "%sConsume SL Form: %s\n State:\n{%s\n}\n\n"
    lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   consume_form_impl state heap p f_eval_form fc 
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap (emp_snap) 
  | Sl.Atom (Sl.Region, [r], _) -> 
      f_eval_term state r (fun state' t' ->
        let (chunk, h') = heap_remove_by_term state.pc state.heap (term_of t') in
        fc state h' (emp_snap))
  | Sl.Atom (Sl.Region, ts, _) -> fc state heap (emp_snap)
  | Sl.Atom (Sl.Pred id, ts, _) -> 
     f_eval_terms state ts (fun state' ts' ->
        let pred_chunk = heap_find_pred_chunk state'.pc state'.heap id ts' in
        let h' = heap_remove state'.heap state'.pc pred_chunk in 
        fc {state' with heap=h'} h' (get_pred_chunk_snap pred_chunk))
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n");
     fc state heap (emp_snap)
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

let rec consume_symb_sl_form_impl state heap (f: symb_sl_form) f_eval_symb_terms f_eval_symb_term (fc: symb_state -> symb_heap -> term -> 'a option) =
  Debug.debug(fun() ->
    sprintf "%sConsume Symbolic SL Form: %s\n State:\n{%s\n}\n\n"
    lineSep (string_of_symb_sl_form f) (string_of_state state));
  match (f) with
  | Symbslf (Sl.Pure (p, _)) ->
   consume_symb_form state heap (Symbf p) fc
  | Symbslf (Sl.Atom (Sl.Emp, ts, _)) -> fc state heap (emp_snap)
  | Symbslf (Sl.Atom (Sl.Region, [App (SetEnum, [t], srt)], _)) ->
      (* TODO: implement a symb_form type? *)
      f_eval_symb_term state (mk_symb_term t) (fun state' t' ->
        let (_, h') = heap_remove_by_term state.pc state.heap (term_of t') in
        fc state h' (emp_snap))
  | Symbslf (Sl.Atom (Sl.Region, ts, _)) -> fc state heap (emp_snap)
  | Symbslf (Sl.Atom (Sl.Pred id, ts, _)) ->
     f_eval_symb_terms state (List.map (fun t -> Symbt t) ts) (fun state' ts' ->
        let pred_chunk = heap_find_pred_chunk state.pc state'.heap id ts' in
        let h' = heap_remove state'.heap state'.pc pred_chunk in
        fc {state' with heap=h'} h' (get_pred_chunk_snap pred_chunk))
  | Symbslf (Sl.SepOp (Sl.SepStar, f1, f2, _)) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n");
     fc state heap (emp_snap)
  | Symbslf (Sl.SepOp (Sl.SepIncl, _, _, _)) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n");
     fc state heap (emp_snap)
  | Symbslf (Sl.SepOp (Sl.SepPlus, _, _, _)) ->
     fc state heap (emp_snap)
  | Symbslf (Sl.BoolOp (Grass.And, fs, _)) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
     fc state heap (emp_snap)
  | Symbslf (Sl.BoolOp (Grass.Or, fs, _)) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
     fc state heap (emp_snap)
  | Symbslf (Sl.BoolOp (Grass.Not, fs, _)) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
     fc state heap (emp_snap)
  | Symbslf (Sl.Binder (b, [], f, _)) ->
      consume_symb_sl_form_impl state heap (Symbslf f) f_eval_symb_terms f_eval_symb_term fc
  | Symbslf (Sl.Binder (Grass.Forall, ts, f, _)) -> fc state heap (emp_snap)
  | Symbslf (Sl.Binder (Grass.Exists, ts, f, _)) -> fc state heap (emp_snap)

let consume_impl state heap (sf: Prog.spec_form) f_eval_form f_eval_terms f_eval_term (fc: symb_state -> symb_heap -> term -> 'a option) =
  match sf with
  | Prog.FOL fol -> consume_form_impl state heap fol f_eval_form fc
  | Prog.SL slf -> consume_sl_form_impl state heap slf f_eval_form f_eval_terms f_eval_term fc

let rec consumes_impl state (assns: Prog.spec list) f_eval_form f_eval_terms f_eval_term fc =
  match assns with
  | [] -> fc state (emp_snap)
  | hd :: assns' -> 
      consume_impl state state.heap hd.spec_form f_eval_form f_eval_terms f_eval_term (fun state' h' snap' ->
        consumes_impl state assns' f_eval_form f_eval_terms f_eval_term fc)

(* this is to break a cicrular dependency in SymbEval *)
let consume_symb_sf_impl state heap (sf: symb_spec_form) f_eval_symb_terms f_eval_symb_term (fc: symb_state -> symb_heap -> term -> 'a option)  =
  match sf with
  | SymbFOL fol ->
      consume_symb_form state heap fol fc
  | SymbSL slf -> consume_symb_sl_form_impl state heap slf f_eval_symb_terms f_eval_symb_term fc 

let rec consumes_symb_sf_impl state (assns: symb_spec list) f_eval_symb_terms f_eval_symb_term fc =
  match assns with
  | [] -> fc state (emp_snap)
  | hd :: assns' -> 
      consume_symb_sf_impl state state.heap hd.symb_spec_form f_eval_symb_terms f_eval_symb_term (fun state' h' snap' ->
        consumes_symb_sf_impl state' assns' f_eval_symb_terms f_eval_symb_term fc) 