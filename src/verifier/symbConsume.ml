(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open SymbState
open SymbEval
open SymbUtil

(** consume(s) removes permissions from a symbolic state and continues 
    the remaining symbolic execution using fc *)
let consume_symb_expr (state: symb_state) heap v (fc: symb_state -> symb_heap -> snap -> 'a option) =
  Debug.debug( fun() ->
    sprintf "State: %s\n" 
    (string_of_state state)
  );
  let _ = check state.pc state.prog (symb_val_to_form v) in
  fc state heap Unit

let rec consume_fol state heap (f: Grass.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match f with
     | Grass.Atom (t, _) as a -> 
       Debug.debug(fun() -> sprintf "Consuming fol Atom (%s) \n"
         (Grass.string_of_term t)
       );
       eval state a (fun state' v -> 
         consume_symb_expr state' heap v fc)
     | Grass.BoolOp (Grass.And, fs) -> 
       Debug.debug( fun() ->
         sprintf "Consuming fol BoolOp AND \n"
       );
       consumes_fol state heap fs fc
     | Grass.BoolOp (Grass.Or, fs) -> todo()
     | Grass.BoolOp (Grass.Not, fs) -> todo()
     | Grass.Binder (Grass.Forall, ts, f, ats) -> todo()
     | Grass.Binder (Grass.Exists, ts, f, ats) -> todo()

and consumes_fol state heap (fs: Grass.form list) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match fs with
  | [] -> fc state heap Unit
  | hd :: fs' -> consume_fol state heap hd (fun state' heap2 snap1 -> 
      consumes_fol state' heap2 fs' (fun state2 heap2 snap2 ->
        fc state2 heap2 (snap_pair snap1 snap2))) 

let rec consume_sl state heap (f: Sl.form) (fc: symb_state -> symb_heap -> snap -> 'a option) =
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() ->
     sprintf "%sConsuming sl pure Atom Var %s\n"
     lineSep (Grass.string_of_form p)
   );
   consume_fol state heap p fc
  | Sl.Atom (Sl.Emp, ts, _) -> todo()
  | Sl.Atom (Sl.Region, [r], _) -> todo()
  | Sl.Atom (Sl.Region, ts, _) -> todo()
  | Sl.Atom (Sl.Pred p, ts, _) -> todo() 
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar\n"); 
     consume_sl state heap f1 (fun (st2: symb_state) h2 snp1 ->
       consume_sl st2 h2 f2 (fun (st3: symb_state) h3 snp2 ->
        fc st3 h3 (snap_pair snp1 snp2)))
  | Sl.SepOp (Sl.SepIncl, _, _, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n"); 
     todo()
  | Sl.SepOp (Sl.SepPlus, _, _, _) ->
     todo()
  | Sl.BoolOp (Grass.And, fs, _) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
     todo()
  | Sl.BoolOp (Grass.Or, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
     todo()
  | Sl.BoolOp (Grass.Not, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
     todo()
  | Sl.Binder (Grass.Forall, ts, f, _) -> todo() 
  | Sl.Binder (Grass.Exists, ts, f, _) -> todo()

let consume_spec_form state heap sf (fc: symb_state -> snap -> 'a option) =
  match sf with
  | Prog.FOL fol ->
    Debug.debug( fun() -> sprintf "consume spec form FOL match\n"); 
    consume_fol state heap fol (fun st h snp ->
      let st2 = {st with heap=h} in
      fc st2 snp
    )
  | Prog.SL slf ->
    Debug.debug( fun() -> sprintf "consume spec form SL match\n"); 
    consume_sl state heap slf (fun st h s ->
      let st2 = {st with heap=h} in
      fc st2 s
    )

(** consume_specs is the entry point for producing an assertion list (spec list),
    this function iterates over the assns calling consume_spec_form on each spec.

    Consume(sig1, a, Q) in the Silicon thesis.
    *)
let rec consume_specs state (assns: Prog.spec list) fc =
  match assns with
  | [] ->
      Debug.debug(fun () -> sprintf "Consume empty assn\n");
      None 
  | hd :: assns' -> 
      Debug.debug(fun () -> sprintf "Consumes calling consume on hd\n");
      (match consume_spec_form state state.heap hd.spec_form fc with
      | Some err -> Some err
      | None -> consume_specs state assns' fc)
