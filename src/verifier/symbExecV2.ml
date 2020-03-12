(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open GrassUtil
open Grass
open SymbEval
open SymbState
open SymbConsume
open SymbProduce
open Prog

(** branch implements branching and executes each path using f1 where symbv
  holds, otherwise f2 is executed *)
let branch state smybv f1 f2 = todo "branch"

let rec exec state comm (fc: symb_state -> 'a option) =
  Debug.debug( fun () -> sprintf "exec state comms *******\n");
  match comm with
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, pp) ->
      eval_terms state ts (fun state' ts' ->
        let st = List.combine ids ts'
        |> List.fold_left (fun macc (id, t') ->
            {macc with store = IdMap.add id t' macc.store}
        ) state'
        in
        fc st)
  | Seq (s1 :: s2 :: comms, _) ->
      Debug.debug( fun () -> sprintf "SEQ (%d) \n"
        (List.length comms)
      );
      exec state s1 (fun state' ->
        exec state' s2 fc)
  | Basic (Assert spec, pp) ->
    (match spec.spec_form with
    | SL slf ->
      (*todo figure out continuation heap and snap arent used*)
      consume_sl_form state state.heap slf (fun state' h' snap ->
        fc state)
    | FOL f->
      consume_form state state.heap f (fun state' h' snp ->
        fc state'))
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, pp) -> todo "exec 3"
  | Seq (_::[], _) -> todo "exec 4" 
  | Seq ([], _) -> todo "exec 5"
  | Basic (Havoc {havoc_args=vars}, pp) -> todo "exec 6"
  | Basic (Assume {spec_form=FOL spec}, pp) -> todo "exec 7"
  | Choice (comms, _) -> todo "exec 8"
  | Basic (Return {return_args=xs}, pp)  -> todo "exec 9"
  | Basic (Split spec, pp) -> todo "exec 10"
  | Basic (New {new_lhs=id; new_sort=srt; new_args=ts}, pp) -> todo "exec 10"
  | Basic (Assume _, _) -> todo "exec 11"
  | Basic (Dispose _, _) -> todo "exec 12"
  | Loop (l, _) -> todo "exec 13"

and execs state comms (fc: symb_state -> 'a option) =
  match comms with
  | [] -> fc state
  | comm :: comms' ->
      exec state comm (fun state' ->
        execs state' comms' fc)

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
    (havoc empty_store formal_arg_terms) prog in

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
  produces init_state precond (mk_fresh_snap_freesrt "pre")
    (fun st ->
      let st2 = { st with heap=[] } in
      produces st2 postcond (mk_fresh_snap_freesrt "post") (fun st' ->
           (match proc.proc_body with
           | Some body ->
              exec st2 body (fun st3 ->
                Debug.debug(fun () -> sprintf "consume post cond\n");
                let st4 = {st3 with store=st3.old_store} in
                consumes st4 postcond (fun _ _ -> None))
           | None ->
               None)
      ))
