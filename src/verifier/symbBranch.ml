(** {5 Symbolic execution inspired by Viper's Silicon} *)

open SymbState
open GrassUtil
open Grass
open Prog 
open Printf
open Util

let rec branch_simple (state: symb_state) comms (fexec: symb_state -> Prog.command -> (symb_state -> 'a option) -> 'a option) fc =
  match comms with
  | [] -> None
  | comm :: comms' ->
      fexec state comm fc |>
      Opt.lazy_or_else (fun () -> branch_simple state comms' fexec fc)

let pc_segs (pi: pc_stack) =
  (* the accumulator is a pair of implications of type list[term],
   * and branch conds of type list[term] *)
  let (impls, bcs) =
    List.fold_left (fun (cnds, bcs) (_, bci, (pci: form list)) -> 
      (mk_implies (mk_and (bci :: bcs)) (mk_and pci)) :: cnds,
        bci :: bcs)
    ([], []) (List.rev pi)
  in
  (List.rev impls, List.rev bcs)

let branch state f fc_f fc_notf =
  let fpush ff =
    pc_push_new state.pc (fresh_ident "branch") ff
  in
  let fs = (smk_and (pc_collect_constr state.pc)) in
  match check_entail state.prog (mk_not fs) f with
  | Some _ ->
      fc_f {state with pc= (fpush (mk_not fs))} (* not f infeasable, branch with q_f*)
  | None ->
      (match check_entail state.prog fs f with
      | Some _ -> 
          fc_notf {state with pc = (fpush fs)} (* f infeasable, branch with q_notf*)
      | None -> None)

let join state (fc_branch: symb_state -> (symb_state -> term -> 'a option) -> 'a option) fc =
  let id = (fresh_ident "j") in
  let data = [] in
  let _ = fc_branch (update_pc state (pc_push_new state.pc id (mk_true)))
   (fun state' w ->
     let _ = (pc_after state'.pc id) :: data in
      None)
  in
  (* collect new path conditions after merge and a set of (bcs, join_result) *)
  let (pc2, ws) =
    List.fold_left (fun (pcs, bres) (pci, wi) ->
      let (cnds, bcs_all) = pc_segs pci in
      ((pc_add_path_conds pci cnds), (bcs_all, wi) :: bres)) 
    (state.pc, []) data
  in
  fc {state with pc=pc2} ws
