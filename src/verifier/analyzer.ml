(** {5 Analysis of GRASShopper programs} *)

open Util
open Grass
open GrassUtil
open Prog

(** Infer sets of accessed and modified variables for all procedures and predicates in program [prog] *)
(* TODO: the implementation of the fix-point loop is brain damaged - rather use a top. sort of the call graph *)
let infer_accesses prog =
  let process_spec_forms prog sfs =
    let accs_preds, accs, fps =
      List.fold_left (fun (acc_preds, accs, fps) sf ->
        let acc_preds =
          IdSet.union acc_preds
            (IdSet.filter (fun p -> IdMap.mem p prog.prog_preds)
               (fold_spec_form free_symbols SlUtil.free_symbols sf))
        in
        let accs =
          IdSet.union accs (fold_spec_form free_symbols SlUtil.free_symbols sf)
        in
        let fps = footprint_sorts_spec_form_acc prog fps sf in
        acc_preds, accs, fps)
        (IdSet.empty, IdSet.empty, SortSet.empty)
        sfs        
    in
    IdSet.fold (fun p (accs, fps) -> 
      let opred = find_pred prog p in
      IdSet.union opred.pred_accesses accs,
      SortSet.union (footprint_sorts_pred opred) fps)
      accs_preds (accs, fps)
  in
  let rec pm prog =
    function
    | Loop (lc, pp) ->
        let has_new1, fps1, prebody1 = pm prog lc.loop_prebody in
        let has_new2, fps2, postbody1 = pm prog lc.loop_postbody in
        let _, fps3 = process_spec_forms prog lc.loop_inv in
        has_new1 || has_new2,
        SortSet.union (SortSet.union fps1 fps2) fps3,
        mk_loop_cmd lc.loop_inv prebody1 lc.loop_test lc.loop_test_pos postbody1 pp.pp_pos
    | Choice (cs, pp) ->
        let has_new, mods, accs, fps, cs1 = 
          List.fold_right 
            (fun c (has_new, mods, accs, fps, cs1) ->
              let has_new1, fps1, c1 = pm prog c in
              has_new1 || has_new, 
              IdSet.union (modifies_cmd c1) mods, 
              IdSet.union (accesses_cmd c1) accs,
              SortSet.union fps1 fps,
              c1 :: cs1)
            cs (false, IdSet.empty, IdSet.empty, SortSet.empty, [])
        in
        let pp1 =
          { pp with
            pp_modifies = mods;
            pp_accesses = accs;
          }
        in
        has_new, fps, Choice (cs1, pp1)
    | Seq (cs, pp) ->
        let has_new, mods, accs, fps, cs1 = 
          List.fold_right 
            (fun c (has_new, mods, accs, fps, cs1) ->
              let has_new1, fps1, c1 = pm prog c in
              has_new1 || has_new, 
              IdSet.union (modifies_cmd c1) mods, 
              IdSet.union (accesses_cmd c1) accs,
              SortSet.union fps1 fps,
              c1 :: cs1)
            cs (false, IdSet.empty, IdSet.empty, SortSet.empty, [])
        in
        let pp1 =
          { pp with
            pp_modifies = mods;
            pp_accesses = accs;
          }
        in
        has_new, fps, Seq (cs1, pp1)
    | Basic (Call cc, pp) ->
        let callee = find_proc prog cc.call_name in
        let mods = IdSet.union (modifies_proc prog callee) pp.pp_modifies in
        let accs = IdSet.union (accesses_proc prog callee) pp.pp_accesses in
        let fps = List.fold_left (footprint_sorts_term_acc prog) (footprint_sorts_proc callee) cc.call_args in
        let has_new = 
          not (IdSet.subset mods pp.pp_modifies) ||  
          not (IdSet.subset accs pp.pp_accesses)
        in
        let pp1 =
          { pp with
            pp_modifies = mods;
            pp_accesses = accs;
          }
        in
        has_new, fps, Basic (Call cc, pp1)
    | Basic(bc, _) as c ->  false, footprint_sorts_basic_cmd prog bc, c
  in
  let pm_pred prog pred =
    let accs, fps =
      process_spec_forms prog
        (Opt.to_list pred.pred_body @ pred.pred_contract.contr_precond @ pred.pred_contract.contr_postcond)
    in
    let global_accs = 
      IdSet.filter
        (fun id ->
          IdMap.mem id prog.prog_vars ||
          IdMap.mem id prog.prog_preds ||
          IdMap.mem id prog.prog_procs
        ) accs
    in
    let fps = SortSet.union fps (footprint_sorts_pred pred) in
    not (IdSet.subset global_accs pred.pred_accesses) ||
    not (SortSet.subset fps (footprint_sorts_pred pred)),
    { pred with
      pred_accesses = global_accs;
      pred_contract = { pred.pred_contract with contr_footprint_sorts = fps }
    }
  in
  let pm_proc prog proc =
    let has_new, body, body_fps =
      match proc.proc_body with
      | Some body ->
          let has_new, body_fps, body = pm prog body in
          has_new, Some body, body_fps
      | _ -> false, None, SortSet.empty
    in
    let fps =
      List.fold_left (footprint_sorts_spec_form_acc prog)
        body_fps (proc.proc_contract.contr_precond @ proc.proc_contract.contr_postcond)
    in
    has_new || not (SortSet.subset fps (footprint_sorts_proc proc)),
    { proc with
      proc_body = body;
      proc_contract = { proc.proc_contract with contr_footprint_sorts = fps }
    }
  in
  let rec pm_prog prog = 
    let preds = preds prog in
    let has_new, preds1 = 
      List.fold_left 
        (fun (has_new, preds1) pred ->
          let has_new1, pred1 = pm_pred prog pred in
          (has_new || has_new1, pred1 :: preds1))
        (false, []) preds
    in
    let preds2 = 
      List.fold_left 
        (fun preds2 pred -> IdMap.add (name_of_pred pred) pred preds2)
        IdMap.empty preds1
    in
    let prog = 
      { prog with 
        prog_preds = preds2 
      }
    in
    let procs = procs prog in
    let has_new, procs1 =
      List.fold_left 
        (fun (has_new, procs1) proc ->
          let has_new1, proc1 = pm_proc prog proc in
              (has_new || has_new1, proc1 :: procs1))
        (has_new, []) procs
    in 
    let procs2 = 
      List.fold_left 
      (fun procs2 proc -> IdMap.add (name_of_proc proc) proc procs2) 
      IdMap.empty procs1
    in
    let prog1 = 
      { prog with 
        prog_procs = procs2;
        prog_preds = preds2 
      }
    in
    if has_new then pm_prog prog1 else prog1 
  in
  pm_prog prog

