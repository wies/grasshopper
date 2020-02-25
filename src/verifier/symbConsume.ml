(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open SymbState
open SymbEval

let consume_symb_vals (state: symb_state) heap vs (fc: symb_state -> symb_heap -> snap -> 'a option) =
  Debug.debug( fun() ->
    sprintf "Consume Symb expr State: %s\n" 
    (string_of_state state)
  );
  let fset =
    List.fold_left (fun acc v ->
      GrassUtil.FormSet.add (symb_val_to_form v) acc)
    GrassUtil.FormSet.empty vs
  in
  let _ = check state.pc state.prog (GrassUtil.smk_and (GrassUtil.FormSet.elements fset)) in
  fc state heap Unit

(* Consume pure [f] this is heap independent so we pass a Unit snap to fc
 * TODO consume SL.form list*)
let rec consumes state heap fs (fc: symb_state -> symb_heap -> snap -> 'a option) =
  evals state fs (fun state' vs' ->
    consume_symb_vals state' heap vs' fc)

let rec consume_fol state heap (f: Grass.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match f with
     | Grass.Atom (t, _) as a -> 
       Debug.debug(fun() -> sprintf "Producing fol Atom (%s) \n"
         (Grass.string_of_term t)
       );
       eval state a (fun state' v -> 
         consume_symb_vals state' heap [v] fc )
     | Grass.BoolOp (Grass.And, fs) -> 
       Debug.debug( fun() ->
         sprintf "Producing fol BoolOp AND \n"
       );
       consumes state heap fs fc
     | Grass.BoolOp (Grass.Or, fs) -> todo()
     | Grass.BoolOp (Grass.Not, fs) -> todo()
     | Grass.Binder (Grass.Forall, ts, f, ats) -> todo()
     | Grass.Binder (Grass.Exists, ts, f, ats) -> todo()

let rec consume_sl state heap (f: Sl.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() ->
     sprintf "%sProducing sl pure Atom Var %s\n"
     lineSep (Grass.string_of_form p)
   );
   consume_fol state heap p fc 
  | Sl.Atom (Sl.Emp, ts, _) -> fc state heap Unit
  | Sl.Atom (Sl.Region, [r], _) -> fc state heap Unit
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

let consume_spec_form state heap (sf: Prog.spec_form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match sf with
  | Prog.FOL fol -> consume_fol state heap fol fc
  | Prog.SL slf -> consume_sl state heap slf fc

let rec consume_specs state (assns: Prog.spec list) fc =
  match assns with
  | [] -> fc state Unit
  | hd :: assns' -> 
      Debug.debug(fun () -> sprintf "Produces calling produce on hd\n");
      consume_spec_form state state.heap hd.spec_form (fun state' h' snap' ->
        consume_specs state assns' fc)
