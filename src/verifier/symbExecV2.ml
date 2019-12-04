(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open GrassUtil
open SymbEval
open SymbState

(** SMT solver calls *)
let check pc_stack v =
  let _ = pc_collect_constr pc_stack in
  true

(* Returns None if the entailment holds, otherwise Some (list of error messages, model) *)
(** carry over from Sid's SymbExec *)
let check_entail st prog p1 p2 =
  if p1 = p2 || p2 = mk_true then None
  else (* Dump it to an SMT solver *)
    (** TODO: collect program axioms and add to symbolic state *)
    let p2 = Verifier.annotate_aux_msg "Related location" p2 in
    (* Close the formulas: assuming all free variables are existential *)
    let close f = smk_exists (Grass.IdSrtSet.elements (sorted_free_vars f)) f in
    let labels, f =
      smk_and [p1; mk_not p2] |> close |> nnf |> Verifier.finalize_form prog
      (* Add definitions of all referenced predicates and functions *)
      |> fun f -> f :: Verifier.pred_axioms prog
      (** TODO: Add axioms *)
      |> (fun fs -> smk_and fs)
      (* Add labels *)
      |> Verifier.add_labels
    in
    let name = fresh_ident "form" |> Grass.string_of_ident in
    Debug.debug (fun () ->
      sprintf "\n\nCalling prover with name %s\n" name);
    match Prover.get_model ~session_name:name f with
    | None -> None
    | Some model -> Some (Verifier.get_err_msg_from_labels model labels, model)

let assert_constr pc_stack v =
  (** TODO add pred_axioms to pc_stack before passing in *)
  if check pc_stack v then None else None

(** consume removes permissions from a symbolic state and then
    executes the remaining symbolic execution using fc *)
let consume state assrtn fc = todo()

(** branch implements branching and executes each path using f1 where symbv
  holds, otherwise f2 is executed *)
let branch state smybv f1 f2 = todo()

let produce_symb_expr state v snp (fc: symb_state -> 'a option) =
  let s2 = { state with pc = pc_add_path_cond (pc_add_path_cond state.pc v)
    (Term (App (Eq, [term_of_snap snp; term_of_snap Unit], Bool))) }
  in
  Debug.debug( fun() ->
    sprintf "%sState: %s\n" 
    lineSep (string_of_state s2)
  );
  fc s2

let rec produce_fol state (f: Grass.form) snp (fc: symb_state -> 'a option) =
  match f with
     | Grass.Atom (t, _) as a -> 
       Debug.debug(fun() -> sprintf "Producing fol Atom (%s) \n"
         (Grass.string_of_term t)
       );
       eval state a (fun state' v -> 
         produce_symb_expr state' v snp fc )
     | Grass.BoolOp (Grass.And, fs) -> 
       Debug.debug( fun() ->
         sprintf "Producing fol BoolOp AND \n"
       );
       produces_fol state fs snp fc
     | Grass.BoolOp (Grass.Or, fs) -> todo()
     | Grass.BoolOp (Grass.Not, fs) -> todo()
     | Grass.Binder (Grass.Forall, ts, f, ats) -> todo()
     | Grass.Binder (Grass.Exists, ts, f, ats) -> todo()

and produces_fol state (fs: Grass.form list) snp (fc: symb_state -> 'a option) =
  match fs with
  | [] -> fc state
  | hd :: fs' -> produce_fol state hd (snap_first snp) (fun state' -> 
      produces_fol state' fs' (snap_second snp) fc) 

let rec produce_sl state (f: Sl.form) snp (fc: symb_state -> 'a option) =
  match f with
  | Sl.Pure (p, _) ->
   Debug.debug( fun() ->
     sprintf "%sProducing sl pure Atom Var %s\n"
     lineSep (Grass.string_of_form p)
   );
   produce_fol state p snp fc
  | Sl.Atom (Sl.Emp, ts, _) -> fc state 
  | Sl.Atom (Sl.Region, [r], _) -> fc state 
  | Sl.Atom (Sl.Region, ts, _) -> fc state 
  | Sl.Atom (Sl.Pred p, ts, _) -> fc state 
  | Sl.SepOp (Sl.SepStar, f1, f2, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepStar\n"); 
     fc state 
  | Sl.SepOp (Sl.SepIncl, _, _, _) ->
     Debug.debug( fun() -> sprintf "SL SepOp SepIncl\n"); 
     fc state 
  | Sl.SepOp (Sl.SepPlus, _, _, _) ->
     fc state 
  | Sl.BoolOp (Grass.And, fs, _) ->
   Debug.debug( fun() -> sprintf "SL BoolOp And\n");
   fc state
  | Sl.BoolOp (Grass.Or, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Or");
    fc state 
  | Sl.BoolOp (Grass.Not, fs, _) ->
    Debug.debug( fun() -> sprintf "SL BoolOp Not\n");
    fc state 
  | Sl.Binder (Grass.Forall, ts, f, _) -> fc state 
  | Sl.Binder (Grass.Exists, ts, f, _) -> fc state

let produce_spec_form state sf snp (fc: symb_state -> 'a option) =
  match sf with
  | Prog.FOL fol ->
    Debug.debug( fun() -> sprintf "produce spec form FOL match\n"); 
    produce_fol state fol snp fc
  | Prog.SL slf ->
    Debug.debug( fun() -> sprintf "produce spec form SL match\n"); 
    produce_sl state slf snp fc

(** produce_specs is the entry point for producing an assertion list (spec list),
    this function iterates over the assns calling produce_spec_form on each spec. *)
let rec produce_specs state (assns: Prog.spec list) snp fc =
  match assns with
  | [] -> None 
  | hd :: assns' -> 
      Debug.debug(fun () -> sprintf "Produces calling produce on hd\n");
      (match produce_spec_form state hd.spec_form snp fc with
      | Some err -> Some err
      | None -> produce_specs state assns' snp fc)

(** verify checks procedures and predicates for well-formed specs and the postcondition
   can be met by executing the body under the precondition *)
let verify spl_prog prog proc =
  Debug.info (fun () ->
      "Checking procedure " ^ Grass.string_of_ident (Prog.name_of_proc proc) ^ "...\n");

  (** Extract sorts of formal params and havoc them into a fresh store. *)
  let formals = Prog.formals_of_proc proc in
  let locs = Prog.locals_of_proc proc in
  let formal_arg_terms =
    List.fold_left
      (fun term_lst var ->
        let srt = Grass.IdMap.find var locs in
        Grass.Var (var, srt.var_sort) :: term_lst)
      [] formals
  in
  let init_state = mk_symb_state
    (havoc_terms empty_store formal_arg_terms) in

  Debug.debug(fun() ->
      sprintf "%sInitial State:\n{%s\n}\n\n"
      lineSep (string_of_state init_state)
  );
  let mk_fresh_snap_freesrt label = mk_fresh_snap (Grass.FreeSrt (label, 0)) in

  let precond = Prog.precond_of_proc proc in
  let postcond = Prog.postcond_of_proc proc in
  produce_specs init_state precond (mk_fresh_snap_freesrt "pre")
    (fun st ->
      let st2 = { st with heap=[]; old=st.heap } in
      produce_specs st2 postcond (mk_fresh_snap_freesrt "post") (fun _ -> None))
