(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Printf
open Util 
open GrassUtil
open Grass
open SlUtil 
open SymbEval
open SymbState
open SymbConsume
open SymbProduce
open SymbBranch
open Prog

let rec exec state comm (fc: symb_state -> 'a option) =
  match comm with
  | Basic (Assign {assign_lhs=[field];
                    assign_rhs=[App (Write, [map; t1; t2], srt)]}, pp) ->
     Debug.debug (fun () -> 
      sprintf "%sExecuting Assign Write: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    Debug.debug (fun () ->
      sprintf "field = %s, map = %s, t1 = %s, t2 = %s \n" (string_of_ident field) (string_of_term map) (string_of_term t1) (string_of_term t2));
      consume_sl_form state state.heap (mk_region t1) (fun state2' h _ ->
        let r = mk_setenum [(App (Read, [map; t1], srt))] in
        let f = mk_sep_star (mk_region (mk_setenum [t1])) (mk_pure (GrassUtil.mk_eq r t2)) in
        let state3 = {state2' with heap =h} in
        produce_sl_form state3 f (mk_fresh_snap srt) fc) 
  | Basic (Assign {assign_lhs=ids; assign_rhs=ts}, pp) ->
    Debug.debug (fun () -> 
      sprintf "%sExecuting Assign: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    eval_terms state ts (fun state' ts' ->
      let st = List.combine ids ts'
      |> List.fold_left (fun macc (id, t') ->
          {macc with store = IdMap.add id t' macc.store}
      ) state'
      in
      Debug.debug(fun() ->
        sprintf "%sBasic Assign Done:\nState:\n{%s\n}\n\n"
        lineSep (string_of_state st)
      );
      fc st)
  | Seq (comms, pp) ->
      Debug.debug (fun () -> 
        sprintf "%sExecuting Seq: %d: %s%sCurrent state:\n%s\n"
          lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
          lineSep (string_of_state state)
      );
      execs state comms (fun state' ->
        fc state')
  | Basic (Assert spec, pp) ->
    (match spec.spec_form with
    | SL slf ->
      (*todo figure out continuation heap and snap arent used*)
      consume_sl_form state state.heap slf (fun state' h' snap ->
        fc state)
    | FOL f->
      consume_form state state.heap f (fun state' h' snp ->
        fc state'))
  | Basic (Call {call_lhs=lhs; call_name=foo; call_args=args}, pp) -> 
      eval_terms state args (fun state' args' ->
        List.combine args args' |>
        Debug.debug(fun () ->
          sprintf "args' = (%s)\n" (string_of_term_list args'));
          fc state');
        (*let contr =(find_proc state'.prog foo).proc_contract in 
         let precond, postcond = contr.contr_precond, contr.contr_postcond in*)


  | Basic (Havoc {havoc_args=vars}, pp) -> todo "exec 6"
  | Basic (Assume {spec_form=f; }, pp) -> 
      produce state f (mk_fresh_snap Bool) (fun state' -> fc state')
  | Choice (comms, pp) ->
      branch_simple state comms exec (fun state' -> fc state')
  | Basic (Return {return_args=xs}, pp)  -> todo "exec 9"
  | Basic (Split spec, pp) -> 
    Debug.debug (fun () -> 
      sprintf "%sExecuting split: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    todo "exec 10"
  | Basic (New {new_lhs=id; new_sort=srt; new_args=ts}, pp) ->
    Debug.debug (fun () -> 
      sprintf "%sExecuting new: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state state)
    );
    let tnew = (Var (id, srt)) in
    (* TODO lift havoc *)
    let st2 = {state with store=(havoc state.store [tnew])} in 
    Debug.debug (fun () -> 
      sprintf "%sExecuting new done: %d: %s%sCurrent state:\n%s\n"
        lineSep (pp.pp_pos.sp_start_line) (string_of_format pr_cmd comm)
        lineSep (string_of_state st2)
    );
    produce_sl_form st2 (mk_cell tnew) (mk_fresh_snap srt) fc 
  | Basic (Dispose _, _) -> todo "exec 13"
  | Loop (l, _) -> todo "exec 14"

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

  (** Extract formal params, returns; havoc them into a fresh store as a 
   * pre-processing phase *)
  let formals = Prog.formals_of_proc proc in
  let returns = Prog.returns_of_proc proc in
  let formal_return_terms =
    let locs = Prog.locals_of_proc proc in
    List.fold_left
      (fun acc var ->
        let srt = Grass.IdMap.find var locs in
        Grass.Var (var, srt.var_sort) :: acc)
      [] (formals @ returns)
  in
  let init_state = mk_symb_state
    (havoc empty_store formal_return_terms) prog in

  let old_store =
    IdMap.fold (fun id v acc -> IdMap.add id v acc) init_state.store empty_store in
  let init_state = {init_state with old_store=old_store} in

  Debug.debug(fun() ->
      sprintf "%sInitial State:\n{%s\n}\n\n"
      lineSep (string_of_state init_state)
  );
  let precond = Prog.precond_of_proc proc in
  let postcond = Prog.postcond_of_proc proc in
  produces init_state precond (mk_fresh_snap Bool)
    (fun st ->
      let st2 = { st with heap=[] } in
      produces st2 postcond (mk_fresh_snap Bool) (fun _ ->
           (match proc.proc_body with
           | Some body ->
              exec st body (fun st3 ->
                consumes st3 postcond (fun _ _ -> None))
           | None -> None)
      ))
