(** {5 Symbolic execution inspired by Viper's Silicon} *)
open SymbEval
open SymbState
open GrassUtil
open Printf

let produce_symb_form state f snp (fc: symb_state -> 'a option) =
  let s2 = { state with pc = pc_add_path_cond state.pc f} in
  let s3 = {s2 with pc = pc_add_path_cond s2.pc 
    (mk_atom Eq [term_of_snap snp; term_of_snap Unit])}
  in
  fc s3

let rec produce_symb_forms state fs snp (fc: symb_state -> 'a option) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_symb_form state hd snp (fun state' ->
        produce_symb_forms state' fs' snp fc)

let produce_form state (f: Grass.form) snp (fc: symb_state -> 'a option) =
  eval_form state f (fun state' f' -> 
    produce_symb_form state' f' snp fc)

let rec produce_sl_forms state (fs: Sl.form list) snp (fc: symb_state -> 'a option) =
  match fs with
  | [] -> fc state
  | hd :: fs' ->
      produce_sl_form state hd snp (fun state' ->
        produce_sl_forms state' fs' snp fc)

and produce_sl_form state (f: Sl.form) snp (fc: symb_state -> 'a option) =
   Debug.debug(fun() ->
      sprintf "%sProduce SL form in Current State:\n{%s\n}\n\n"
      lineSep (string_of_state state));
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() -> sprintf "pure Atom = %s\n" (Grass.string_of_form p));
   produce_form state p snp fc
  | Sl.Atom (Sl.Region, [t], a) -> 
     Debug.debug( fun() -> sprintf "SL atom = %s\n" (Sl.string_of_form f)); 
     eval_term state t (fun state' t' ->
       let hc = mk_heap_chunk_obj t' Unit empty_store in 
        let h, stack = heap_add state'.heap state'.pc hc in
        fc {state' with heap=h; pc = stack})
  | Sl.Atom (Sl.Region, ts, a) -> todo "region terms"
  | Sl.Atom (Sl.Emp, ts, _) -> todo "Atom emp"
  | Sl.Atom (Sl.Pred _, ts, _) -> todo "Atom Pred"
  | Sl.SepOp (op, f1, f2, _) ->
     produce_sl_form state f1 (snap_first snp) (fun state' ->
       produce_sl_form state' f2 (snap_second snp) fc)
  | Sl.BoolOp (op, fs, _) -> 
        produce_sl_forms state fs snp fc
  | Sl.Binder (b, ts, f, _) -> todo "Binder"

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
