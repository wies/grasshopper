open Form
open Programs

(** coarse-grained frame inference *)
let annotate_modifies prog =
  let rec pm prog = function
    | Loop (lc, pp) ->
        let has_new1, prebody1 = pm prog lc.loop_prebody in
        let has_new2, postbody1 = pm prog lc.loop_postbody in
        let lc1 = {lc with loop_prebody = prebody1; loop_postbody = postbody1} in
        let mods = IdSet.union (modifies prebody1) (modifies postbody1) in
        let pp1 = {pp with pp_modifies = mods} in
        has_new1 || has_new2, Loop (lc1, pp1)
    | Choice (cs, pp) ->
        let has_new, mods, cs1 = 
          List.fold_right 
            (fun c (has_new, mods, cs1) ->
              let has_new1, c1 = pm prog c in
              has_new1 || has_new, IdSet.union (modifies c1) mods, c1 :: cs1)
            cs (false, IdSet.empty, [])
        in
        let pp1 = {pp with pp_modifies = mods} in
        has_new, Choice (cs1, pp1)
    | Seq (cs, pp) ->
        let has_new, mods, cs1 = 
          List.fold_right 
            (fun c (has_new, mods, cs1) ->
              let has_new1, c1 = pm prog c in
              has_new1 || has_new, IdSet.union (modifies c1) mods, c1 :: cs1)
            cs (false, IdSet.empty, [])
        in
        let pp1 = {pp with pp_modifies = mods} in
        has_new, Seq (cs1, pp1)
    | Basic (ac, pp) ->
        let mods = basic_modifies prog ac in
        let has_new = IdSet.subset mods pp.pp_modifies in
        let pp1 = {pp with pp_modifies = mods} in
        has_new, Basic (ac, pp1)
  in
  let rec pm_prog prog = 
    let procs = procs prog in
    let has_new, procs1 =
      List.fold_left 
        (fun (has_new, procs1) proc ->
          match proc.proc_body with
          | Some body ->
              let has_new1, body1 = pm prog body in
              let proc1 = {proc with proc_body = Some body1} in
              (has_new || has_new1, proc1 :: procs1)
          | None -> (has_new, proc :: procs1))
        (false, []) procs
    in 
    let procs2 = 
      List.fold_left 
      (fun procs2 proc -> IdMap.add proc.proc_name proc procs2) 
      IdMap.empty procs1
    in
    let prog1 = {prog with prog_procs = procs2} in
    if has_new then prog1 else pm_prog prog1
  in
  pm_prog prog

(*
let short_circuit_eval prog =
  let rec sce new_locals = function
    | Choice (cs, pp) ->
        let new_locals, cs1 = 
          List.fold_right 
            (fun c (new_locals, cs1) ->
              let new_locals1, c1 = sce new_locals c in
              new_locals1, c1 :: cs1)
            cs (new_locals, [])
        in
        new_locals, Choice (cs1, pp)
    | Seq (cs, pp) ->
        let new_locals, cs1 = 
          List.fold_right 
            (fun c (new_locals, cs1) ->
              let new_locals1, c1 = sce new_locals c in
              new_locals1, c1 :: cs1)
            cs (new_locals, [])
        in
        new_locals, Seq (cs1, pp)
  in
*)
