(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open GrassUtil
open Grass
open SymbEval
open SymbState
open SymbConsume
open Prog

(** branch implements branching and executes each path using f1 where symbv
  holds, otherwise f2 is executed *)
let branch state smybv f1 f2 = todo()

let produce_symb_expr state v snp (fc: symb_state -> 'a option) =
  let s2 = { state with pc = pc_add_path_cond state.pc v} in
  let s3 = {s2 with pc = pc_add_path_cond s2.pc 
    (Term (App (Eq, [term_of_snap snp; term_of_snap Unit], Bool)))}
  in
  Debug.debug( fun() ->
    sprintf "%sState: %s\n" 
    lineSep (string_of_state s3)
  );
  fc s2

let rec produce_fol state (f: Grass.form) snp (fc: symb_state -> 'a option) =
  match f with
     | Grass.Atom (t, _) as a -> 
       Debug.debug(fun() -> sprintf "Producing fol Atom (%s)\n"
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
     Debug.debug( fun() -> sprintf "SL SepOp SepStar f1=(%s), f2=(%s)\n"
     (Sl.string_of_form f1) (Sl.string_of_form f2));
     produce_sl state f1 (snap_first snp) (fun state' ->
       produce_sl state' f2 (snap_second snp) fc)
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
    Debug.debug( fun() -> sprintf "produce spec form SL match \n"); 
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

let rec exec state comm (fc: symb_state -> 'a option) = 
  Debug.debug( fun () -> sprintf "exec state comms *******\n");
  match comm with
  | (Basic (Assign {assign_lhs=[_];
                    assign_rhs=[App (Write, [arr; idx; rhs], Loc (Array _))]}, pp)) ->
      Debug.debug( fun () -> sprintf "basic assign foo");
      fc state
  | Basic (Assign {assign_lhs=[fld];
        assign_rhs=[App (Write, [App (FreeSym fld', [], _);
          loc; rhs], srt)]}, pp) ->
      Debug.debug(
        fun () ->
          sprintf "lhs(%s), rhs(%s)\n"
          (string_of_ident fld) (string_of_term rhs)
      );
      fc state
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, pp) ->
      evalts state ts (fun state' ts' ->
        let st = List.combine ids ts'
        |> List.fold_left (fun macc (id, t') ->
            {macc with store = IdMap.add id t' macc.store}
        ) state'
        in
        fc st)
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, pp) ->
      fc state
  | Seq (s1 :: s2 :: comms, _) ->
      Debug.debug( fun () -> sprintf "SEQ (%d) \n"
        (List.length comms)
      );
      exec state s1 (fun state' ->
        exec state' s2 fc)
  | Seq (_::[], _) -> fc state
  | Seq ([], _) -> fc state
  | Basic (Havoc {havoc_args=vars}, pp) ->
      fc state
  | Basic (Assume {spec_form=FOL spec}, pp) ->
      fc state
  | Choice (comms, _) ->
      fc state
  | Basic (Assert spec, pp) ->
      Debug.debug(
        fun () ->
          sprintf "foo bar ASSERT MFER \n"
      );
      let f = function 
        | SL _ ->
            Debug.debug(fun () -> sprintf "SL");
            state
        | FOL spec_form ->
            let subs = subst_symbv state in
            let symbv = (Form (map_terms subs spec_form)) in
            Debug.debug(
              fun () -> sprintf "Assert spec form %s\n"
              (string_of_symb_val symbv)
            );
            Debug.debug( fun() ->
              sprintf "%sState Before: %s\n" 
              lineSep (string_of_state state)
            );
            (* TODO(eric): replace this with proper consume of an assert*)
            let _ = check state.pc state.prog (symb_val_to_form symbv) in 
            { state with pc = pc_add_path_cond state.pc symbv}
      in
      fc (f spec.spec_form)
  | Basic (Return {return_args=xs}, pp)  ->
      fc state
  | Basic (Split spec, pp) ->
      fc state
  | Basic (New {new_lhs=id; new_sort=srt; new_args=ts}, pp) ->
      fc state
  | Basic (Assume _, _) ->
      fc state
  | Basic (Dispose _, _) ->
      fc state
  | Loop (l, _) ->
      fc state

and execs state comms (fc: symb_state -> 'a option) =
  match comms with
  | [] -> fc state
  | comm :: comms' ->
      exec state comm (fun state' ->
        execs state' comms' fc)

(*
let rec print_spec_list = function
  | [] -> ()
  | hd :: tail -> (print_form hd); printf " "; (print_spec_list tail) 
  *)

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
    (havoc_terms empty_store formal_arg_terms) prog in

  let old_store =
    IdMap.fold (fun id v acc -> IdMap.add id v acc) init_state.store empty_store in
  let init_state = {init_state with old_store=old_store} in

  Debug.debug(fun() ->
      sprintf "%sInitial State:\n{%s\n}\n\n"
      lineSep (string_of_state init_state)
  );
  let mk_fresh_snap_freesrt label = mk_fresh_snap (Grass.FreeSrt (label, 0)) in
  let precond = Prog.precond_of_proc proc in
  let postcond = Prog.postcond_of_proc proc in
  produce_specs init_state precond (mk_fresh_snap_freesrt "pre")
    (fun st ->
      let st2 = { st with heap=[] } in
      produce_specs st2 postcond (mk_fresh_snap_freesrt "post") (fun st' ->
           (match proc.proc_body with
           | Some body ->
              exec st2 body (fun st3 ->
                Debug.debug(fun () -> sprintf "consume post cond\n");
                let st4 = {st3 with store=st3.old_store} in
                consume_specs st4 postcond (fun _ _ -> None))
           | None ->
               None)
      ))
