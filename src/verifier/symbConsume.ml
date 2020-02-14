(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open SymbState
open SymbEval
open SymbUtil

(*
and consumes_fol state heap (fs: Grass.form list) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match fs with
  | [] -> fc state heap Unit
  | hd :: fs' -> consume_fol state heap hd (fun state' heap2 snap1 -> 
      consumes_fol state' heap2 fs' (fun state2 heap2 snap2 ->
        fc state2 heap2 (snap_pair snap1 snap2))) 

let consume_fol state heap (f: Grass.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match f with
     | Grass.Atom (t, _) as a -> 
       Debug.debug(fun() -> sprintf "Consuming fol Atom (%s) \n"
         (Grass.string_of_term t)
       );
       eval state a (fun state' v -> 
         consumes_symb_expr state' heap v fc)
     | Grass.BoolOp (Grass.And, fs) -> 
       Debug.debug( fun() ->
         sprintf "Consuming fol BoolOp AND \n"
       );
       consumes_fol state heap fs fc
     | Grass.BoolOp (Grass.Or, fs) -> todo()
     | Grass.BoolOp (Grass.Not, fs) -> todo()
     | Grass.Binder (Grass.Forall, ts, f, ats) -> todo()
     | Grass.Binder (Grass.Exists, ts, f, ats) -> todo()

(* consume' S -> H -> A -> (S -> H -> Snap -> R) -> R *)
(* viper uses the same type signature here for pure formulas but since
 * pure formulas are heap invaiant we still carry through snap but when
 * we bottom-out in the recursion, we pass snap as Unit to the continuation *)
let consume_spec_form state heap sf (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match sf with
  | Prog.FOL fol ->
    Debug.debug( fun() -> sprintf "consume spec form FOL match\n"); 
    consume_fol state heap fol fc 
  | Prog.SL slf ->
    consume_sl state heap slf (fun st h s ->
      (* saving the complete heap prevents acc(x.f) &*& x.f == 0 from failing *)
      let st2 = {st with heap=h} in
      fc st2 s)

(* Consume S -> A -> (S -> Snap) -> R *)
let rec consumes_spec_forms state heap (sfs: Prog.spec_form list) symb_fs fc =
  match sfs with 
  | [] -> fc state (List.rev symb_fs)
  | hd :: sfs' -> consume_spec_form state heap hd (fun state' v' snap ->
      Debug.debug(
        fun () ->
          sprintf "eval resolved form into %s\n"
          (string_of_symb_val v)
      );
      consumes_spec_forms state' sfs' (v :: symb_fs) fc)

(* consumes consumes top level formulas *)
let consumes state heap (sfs: Prog.spec_form list) fc =
  consumes spec_forms state heap sfs [] fc
*)

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

let rec consumes_sl state heap (fs: Sl.form list) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match fs with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() ->
     sprintf "%sConsuming sl pure Atom Var %s\n"
     lineSep (Grass.string_of_form p)
   );
   todo()
  | Sl.Atom (Sl.Emp, ts, _) -> todo()
  | Sl.Atom (Sl.Region, [r], _) -> todo()
  | Sl.Atom (Sl.Region, ts, _) -> todo()
  | Sl.Atom (Sl.Pred p, ts, _) -> todo() 
  | Sl.SepOp (Sl.SepStar, f1, f2, _) -> todo()
  | Sl.SepOp (Sl.SepIncl, _, _, _) -> todo()
  | Sl.SepOp (Sl.SepPlus, _, _, _) -> todo()
  | Sl.BoolOp (Grass.And, fs, _) -> Debug.debug( fun() -> sprintf "SL BoolOp And\n");
   consumes state heap fs (fun st' h' snap' ->
     let st2 = {st' with heap=st'.heap} in
     fc st2 snap')
  | Sl.BoolOp (Grass.Or, fs, _) -> todo()
  | Sl.BoolOp (Grass.Not, fs, _) -> todo()
  | Sl.Binder (Grass.Forall, ts, f, _) -> todo() 
  | Sl.Binder (Grass.Exists, ts, f, _) -> todo()
