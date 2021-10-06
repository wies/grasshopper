(** {5 Symbolic execution inspired by Viper's Silicon} *)

open Stdlib
open SymbState
open GrassUtil
open Grass
open Prog 
open Printf
open Util

let rec branch_simple (state: symb_state) comms (fexec: symb_state -> Prog.command -> (symb_state -> vresult) -> vresult) fc : vresult =
  match comms with
  | [] -> Result.Ok (Forms []) 
  | comm :: comms' ->
      match fexec state comm fc with 
      | Result.Error err as e -> e 
      | Result.Ok _ -> branch_simple state comms' fexec fc

let pc_segs (pi: pc_stack) =
  (* the accumulator is a pair of implications of type list[term],
   * and branch conds of type list[term] *)
  Debug.debug(fun () -> sprintf "pc_segs %s\n" (string_of_pc_stack pi));
  let (impls, bcs) =
    List.fold_left (fun (cnds, bcs) (_, bci, (pci: form list)) -> 
      Debug.debug(fun () -> sprintf "bci %s\n" (string_of_form bci));
      Debug.debug(fun () -> sprintf "pcis %s\n" (string_of_forms pci));
      let bci_and = mk_and (bci :: bcs) in
      let pci_and = mk_and pci in
      Debug.debug(fun () -> sprintf "bci_and %s\n" (string_of_form bci_and));
      Debug.debug(fun () -> sprintf "pci_and %s\n" (string_of_form pci_and));
      let imp = mk_implies bci_and pci_and in
      Debug.debug(fun () -> sprintf "impl %s\n" (string_of_form imp));
      (mk_implies (mk_and (bci :: bcs)) (mk_and pci)) :: cnds,
        bci :: bcs)
    ([], []) (List.rev pi)
  in

  Debug.debug(fun () -> sprintf "PCSegs %s\n" (string_of_forms impls));
  Debug.debug(fun () -> sprintf "PCSegs bcs %s\n" (string_of_forms bcs));
  (List.rev impls, List.rev bcs)

let branch state f fc_f fc_notf =
  Debug.debug(fun () -> sprintf "BRANCH\n");
  let fpush ff =
    pc_push_new state.pc (fresh_ident "branch") ff
  in
  let fs = (smk_and (pc_collect_constr state.pc)) in
  Debug.debug(fun () -> sprintf "FS **** %s\n" (string_of_form fs));

  let rnot = fc_notf {state with pc = (fpush (mk_not f))} in
  match rnot with
  | Result.Error err as e -> e
  | Result.Ok _ -> fc_f {state with pc= (fpush f)}

let join state (fc_branch: symb_state -> (symb_state -> term -> vresult) -> vresult) fc : vresult =
  let id = (fresh_ident "j") in
  let data = ref [] in
  let pcnew = pc_push_new state.pc id (mk_true) in
  Debug.debug(fun () -> sprintf "XXX join pcnew = (%s)\n" (string_of_pc_stack pcnew));
  let _ = fc_branch (update_pc state pcnew)
   (fun state' w ->
     Debug.debug (fun () -> sprintf "STATE after branch %s\n" (string_of_state state'));
     Debug.debug(fun () -> sprintf "Qjoin id = %s\n" (string_of_ident id));
     Debug.debug(fun () -> sprintf "Qjoin w = %s\n" (string_of_term w));
     
     let pcaft = pc_after state'.pc id in
     Debug.debug(fun () -> sprintf "XXX PCAFTER %s\n" (string_of_pc_stack pcaft));
     let r = ((pc_after state'.pc id), w) in
     data := r :: !data;
     Result.Ok (Forms []))
  in

  Debug.debug(fun () -> sprintf "Data:\n");
  let _ = List.map (fun (fs, ts) ->
          Debug.debug(fun () -> sprintf "(pc: %s, ts: %s)\n" (string_of_pc_stack fs) (string_of_term ts))) !data 
  in
 
  Debug.debug(fun () -> sprintf "Qbranch \n");
  (* collect new path conditions after merge and a set of (bcs, join_result) *)
  let (pc2, ws) =
    List.fold_left (fun (pcs, bres) (pci, wi) ->
      let (cnds, bcs_all) = pc_segs pci in
      Debug.debug(fun () -> sprintf "collect pc2 %s\n" (string_of_forms cnds));
      ((pc_add_path_conds pcs cnds), (bcs_all, wi) :: bres)) 
    (state.pc, []) !data
  in

  Debug.debug(fun () -> sprintf "Qbranch done 2\n");
  Debug.debug(fun () -> sprintf "Qbranch done 2\n");
  let _ = List.map (fun (fs, ts) ->
          Debug.debug(fun () -> sprintf "(fs: %s, ts: %s)\n" (string_of_forms fs) (string_of_term ts))) ws 
  in
 
  fc {state with pc=pc2} ws

let join_prime state (fc_branch: symb_state -> (symb_state -> term -> vresult) -> vresult) fc : vresult =
  join state fc_branch (fun state' bcs ->
    (* the sort of w should be the same *)
    Debug.debug(fun () -> sprintf "join in join_prime, bcs len (%d)\n" (List.length bcs));
    let jnfn = mk_free_app (sort_of (snd (List.hd bcs))) (mk_ident "joinFn") (state'.qvs) in
    let jndef = 
      List.map (fun (bcs', w) -> mk_implies (mk_and bcs') (mk_eq jnfn w)) bcs 
    in
    fc (update_pc state' (pc_add_path_conds state'.pc jndef)) jnfn)
