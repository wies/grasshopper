(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open SymbState
open SymbEval
open GrassUtil

let check_symb_forms (state: symb_state) heap fs (fc: symb_state -> symb_heap -> snap -> 'a option) =
  Debug.debug( fun() ->
    sprintf "Consume Symb expr State: %s\n" 
    (string_of_state state)
  );
  let fset =
    List.fold_left (fun acc f ->
      GrassUtil.FormSet.add f acc)
    GrassUtil.FormSet.empty fs
  in
  let _ = check state.pc state.prog (GrassUtil.smk_and (GrassUtil.FormSet.elements fset)) in
  fc state heap Unit

(* Consume pure [f] this is heap independent so we pass a Unit snap to fc
 * TODO consume SL.form list*)
let rec consumes state heap fs (fc: symb_state -> symb_heap -> snap -> 'a option) =
  eval_forms state fs (fun state' fs' ->
    check_symb_forms state' heap (List.map (fun f -> form_of f) fs') fc)

let rec consume_form state heap (f: Grass.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  eval_form state f (fun state' f' -> 
    check_symb_forms state' heap [form_of f'] fc)

let rec consume_symb_form state heap (f: symb_form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
    check_symb_forms state heap [form_of f] fc

let rec consume_sl_form state heap (f: Sl.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() ->
     sprintf "%sConsuming sl pure Atom Var %s\n"
     lineSep (Grass.string_of_form p)
   );
   consume_form state heap p fc 
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap Unit
  | Sl.Atom (Sl.Region, [r], _) -> 
      eval_term state r (fun state' t' ->
        let h' = heap_remove_by_term state.heap (mk_setenum [term_of t']) in
        fc state h' Unit)
  | Sl.Atom (Sl.Region, ts, _) -> fc state heap Unit
  | Sl.Atom (Sl.Pred p, ts, _) -> fc state heap Unit
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n"); 
     fc state heap Unit 
  | Sl.SepOp (Sl.SepIncl, _, _, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n"); 
     fc state heap Unit 
  | Sl.SepOp (Sl.SepPlus, _, _, _) ->
     fc state heap Unit 
  | Sl.BoolOp (Grass.And, fs, _) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
     fc state heap Unit 
  | Sl.BoolOp (Grass.Or, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
     fc state heap Unit 
  | Sl.BoolOp (Grass.Not, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
     fc state heap Unit 
  | Sl.Binder (Grass.Forall, ts, f, _) -> fc state heap Unit
  | Sl.Binder (Grass.Exists, ts, f, _) -> fc state heap Unit

let rec consume_symb_sl_form state heap (f: symb_sl_form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match (slform_of f) with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() ->
     sprintf "%sConsuming SYMB sl pure Atom Var %s\n"
     lineSep (Grass.string_of_form p)
   );
   consume_symb_form state heap (Symbf p) fc 
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap Unit
  | Sl.Atom (Sl.Region, [r], _) -> 
      eval_term state r (fun state' t' ->
        let h' = heap_remove_by_term state.heap (mk_setenum [term_of t']) in
        fc state h' Unit)
  | Sl.Atom (Sl.Region, ts, _) -> fc state heap Unit
  | Sl.Atom (Sl.Pred p, ts, _) -> fc state heap Unit
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar \n"); 
     fc state heap Unit 
  | Sl.SepOp (Sl.SepIncl, _, _, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n"); 
     fc state heap Unit 
  | Sl.SepOp (Sl.SepPlus, _, _, _) ->
     fc state heap Unit 
  | Sl.BoolOp (Grass.And, fs, _) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
     fc state heap Unit 
  | Sl.BoolOp (Grass.Or, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
     fc state heap Unit 
  | Sl.BoolOp (Grass.Not, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
     fc state heap Unit 
  | Sl.Binder (Grass.Forall, ts, f, _) -> fc state heap Unit
  | Sl.Binder (Grass.Exists, ts, f, _) -> fc state heap Unit


let consume state heap (sf: Prog.spec_form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match sf with
  | Prog.FOL fol -> consume_form state heap fol fc
  | Prog.SL slf -> consume_sl_form state heap slf fc

let rec consumes state (assns: Prog.spec list) fc =
  match assns with
  | [] -> fc state Unit
  | hd :: assns' -> 
      consume state state.heap hd.spec_form (fun state' h' snap' ->
        consumes state assns' fc)

let consume_symb_sf state heap (sf: symb_spec_form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match sf with
  | SymbFOL fol -> consume_symb_form state heap fol fc
  | SymbSL slf -> consume_symb_sl_form state heap slf fc

let rec consumes_symb_sf state (assns: symb_spec list) fc =
  match assns with
  | [] -> fc state Unit
  | hd :: assns' -> 
      consume_symb_sf state state.heap hd.symb_spec_form (fun state' h' snap' ->
        consumes_symb_sf state assns' fc)
