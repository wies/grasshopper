(** {5 Symbolic execution inspired by Viper's Silicon} *)
open Printf
open Prog
open SymbEval
open SymbState
open GrassUtil
open Grass
open Printf
open Util

let produce_symb_form state f snp (fc: symb_state -> 'a option) =
  let s2 = { state with pc = pc_add_path_cond state.pc f} in
  let s3 = {s2 with pc = pc_add_path_cond s2.pc 
    (mk_atom Eq [snp; emp_snap])}
  in
  fc s3

let rec produce_symb_forms state fs snp (fc: symb_state -> 'a option) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_symb_form state hd snp (fun state' ->
        produce_symb_forms state' fs' snp fc)

let produce_form state (f: Grass.form) snp (fc: symb_state -> 'a option) =
  Debug.debug(fun() ->
    sprintf "%sProduce Form: %s\n Current State:\n{%s\n}\n\n"
    lineSep (string_of_form f) (string_of_state state));
  eval_form state f (fun state' f' -> 
    produce_symb_form state' (form_of f') snp fc)

let rec produce_sl_forms state (fs: Sl.form list) snp (fc: symb_state -> 'a option) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_sl_form state hd snp (fun state' ->
        produce_sl_forms state' fs' snp fc)

and produce_sl_form state (f: Sl.form) snp (fc: symb_state -> 'a option) =
   Debug.debug(fun() ->
      sprintf "%sProduce SL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (Sl.string_of_form f) (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   produce_form state p snp fc
  | Sl.Atom (Sl.Region, [t], a) ->
     eval_term state t (fun state' t' ->
       let hc = mk_heap_chunk_obj t' snp empty_store in 
        let h, stack = heap_add state'.heap state'.pc hc in
        fc {state' with heap=h; pc = stack})
  | Sl.Atom (Sl.Region, ts, a) -> todo "region terms"
  | Sl.Atom (Sl.Emp, [], _) ->
      Debug.debug(fun () -> sprintf "atom emp");
      fc state
  | Sl.Atom (Sl.Emp, ts, _) -> todo "Atom emp ts"
  | Sl.Atom (Sl.Pred id, ts, _) -> 
      eval_terms state ts (fun state' ts' ->
        let pred_chunk = mk_heap_chunk_obj_pred id snp ts' in
        let h, stack = heap_add state'.heap state'.pc pred_chunk in
        fc {state' with heap=h; pc = stack})
  | Sl.SepOp (op, f1, f2, _) ->
     produce_sl_form state f1 (snap_first snp) (fun state' ->
       produce_sl_form state' f2 (snap_second snp) fc)
  | Sl.BoolOp (op, fs, p) ->
        produce_sl_forms state fs snp fc
  | Sl.Binder (b, ts, f, _) -> todo "Binder"

and produce_symb_sl_form state (f: symb_sl_form) snp (fc: symb_state -> 'a option) =
   Debug.debug(fun() ->
      sprintf "%sProduce Symb SL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (string_of_symb_sl_form f) (string_of_state state));
  match f with
  | Symbslf (Sl.Pure (p, _)) ->
    produce_symb_form state p snp fc
  | Symbslf (Sl.Atom (Sl.Region, [App (SetEnum, [t], srt)], a)) -> 
      let hc = mk_heap_chunk_obj (Symbt t) snp empty_store in 
      let h, stack = heap_add state.heap state.pc hc in
      fc {state with heap=h; pc=stack}
  | Symbslf (Sl.Atom (Sl.Region, ts, a)) -> todo "symb region terms"
  | Symbslf (Sl.Atom (Sl.Emp, ts, _)) -> fc state
  | Symbslf (Sl.Atom (Sl.Pred id, ts, _)) ->
    eval_symb_terms state (List.map (fun t -> Symbt t) ts) (fun state' ts' ->
        let pred_chunk = mk_heap_chunk_obj_pred id snp ts' in
        let h, stack = heap_add state'.heap state'.pc pred_chunk in
        fc {state' with heap=h; pc = stack})
  | Symbslf (Sl.SepOp (op, f1, f2, _)) ->
    produce_symb_sl_form state (Symbslf f1) (snap_first snp) (fun state' ->
       produce_symb_sl_form state' (Symbslf f2) (snap_second snp) fc)
  | Symbslf (Sl.BoolOp (op, fs, _)) -> todo "Symb produce BoolOp"
  | Symbslf (Sl.Binder (b, [], f, _)) ->
      produce_symb_sl_form state (Symbslf f) snp (fun state' ->
        fc state') 
  | Symbslf (Sl.Binder (b, ts, f, _)) -> todo "Binder"

let produce state sf snp (fc: symb_state -> 'a option) =
  match sf with
  | Prog.FOL fol -> produce_form state fol snp fc
  | Prog.SL slf -> produce_sl_form state slf snp fc

(** produce_specs is the entry point for producing an assertion list (spec list),
    this function iterates over the assns calling produce_spec_form on each spec. *)
let rec produces state (assns: Prog.spec list) snp fc =
  match assns with
  | [] -> None 
  | hd :: assns' -> 
    (match produce state hd.spec_form snp fc with
    | Some err -> Some err
    | None -> produces state assns' snp fc)

let produce_symb_sf state sf snp (fc: symb_state -> 'a option) =
  match sf with
  | SymbFOL fol -> 
   Debug.debug(fun() ->
      sprintf "%sProduce Symb FOL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (string_of_symb_spec_form sf) (string_of_state state));
      produce_symb_form state (form_of fol) snp fc
  | SymbSL slf -> 
   Debug.debug(fun() ->
      sprintf "%sProduce Symb SL Form: %s\n Current State:\n{%s\n}\n\n"
      lineSep (string_of_symb_spec_form sf) (string_of_state state));
      produce_symb_sl_form state slf snp fc

let rec produces_symb_sf state (assns: symb_spec list) snp fc =
  match assns with
  | [] -> None 
  | hd :: assns' -> 
    produce_symb_sf state hd.symb_spec_form snp fc
    |> Opt.lazy_or_else (fun () -> produces_symb_sf state assns' snp fc)
