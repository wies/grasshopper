(** {5 Symbolic execution inspired by Viper's Silicon} *)
open Printf
open Prog
open SymbEval
open SymbState
open GrassUtil
open Grass
open Printf
open Util

let produce_symb_form state f snp (fc: symb_state -> vresult) =
  let s2 = { state with pc = pc_add_path_cond state.pc f} in
  let s3 = {s2 with pc = pc_add_path_cond s2.pc 
    (mk_atom Eq [snp; emp_snap])}
  in
  fc s3

let rec produce_symb_forms state fs snp (fc: symb_state -> vresult) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_symb_form state hd snp (fun state' ->
        produce_symb_forms state' fs' snp fc)

let produce_form state (f: Grass.form) snp (fc: symb_state -> vresult) =
  Debug.debug(fun() ->
    sprintf "%sProduce Form: %s\n Current State:\n{%s\n}\n\n"
    lineSep (string_of_form f) (string_of_state state));
  eval_form state f (fun state' f' -> 
    produce_symb_form state' f' snp fc)

let rec produce_sl_forms state (fs: Sl.form list) snp (fc: symb_state -> vresult) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_sl_form state hd snp (fun state' ->
        produce_sl_forms state' fs' snp fc)

and produce_sl_form state (f: Sl.form) snp (fc: symb_state -> vresult) =
   Debug.debug(fun() ->
      sprintf "%sProduce SL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug(fun () -> sprintf "PURE \n");
   produce_form state p snp fc
  | Sl.Atom (Sl.Region, [obj; App (FreeSym id, _, _)], a) ->
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
        produce_sl_forms state fs snp fc
  | Sl.Binder (b, [], f, _) ->
      produce_sl_form state f snp fc
  | Sl.Binder (b, ts, f, _) -> todo "Binder"

let rec produce_sl_symb_forms state (fs: Sl.form list) snp (fc: symb_state -> vresult) =
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

let produce state sf snp (fc: symb_state -> vresult) =
  match sf with
  | Prog.FOL fol -> produce_form state fol snp fc
  | Prog.SL slf -> produce_sl_form state slf snp fc

let produce_symb state sf snp (fc: symb_state -> vresult) : vresult =
  match sf with
  | Prog.FOL fol -> produce_form state fol snp fc
  | Prog.SL slf -> produce_sl_symb_form state slf snp fc

(** produce_specs is the entry point for producing an assertion list (spec list),
    this function iterates over the assns calling produce_spec_form on each spec. *)
let rec produces state (assns: Prog.spec list) snp fc : vresult =
  match assns with
  | [] -> fc state
  | hd :: assns' -> produce state hd.spec_form snp (fun state' -> produces state' assns' snp fc) 
