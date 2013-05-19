open Form
open FormUtil
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

let elim_return prog =
  let elim returns posts = function
    | (Return rc, pp) ->
        let rt_assign = 
          mk_assign_cmd returns rc.return_args pp.pp_pos 
        in
        let fls = 
          mk_spec_form 
            (FOL mk_false) true (Some "return") pp.pp_pos 
        in
        let rt_false = mk_assume_cmd fls pp.pp_pos in
        let rt_postcond = 
          List.map (fun sf -> mk_assert_cmd sf pp.pp_pos) posts
        in
        Seq (rt_assign :: rt_postcond @ [rt_false], pp)
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc =
    let posts = 
      Util.filter_map 
        (fun sf -> sf.spec_free)
        (fun sf ->
          match sf.spec_form with
          | FOL _ -> sf
          | SL _ -> failwith "elim_return: Found SL formula that should have been desugared.")
        proc.proc_postcond
    in
    let body = 
      Util.optmap (map_basic (elim proc.proc_returns posts)) 
        proc.proc_body 
    in
    { proc with proc_body = body }
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }


let vcgen prog =
  let vcp acc proc =
    let rec vcs acc pre = function
      | Loop _ -> 
          failwith "vcgen: loop should have been desugared"
      | Choice (cs, pp) ->
          let acc1, traces = 
            List.fold_left (fun (acc, traces) c ->
              let acc1, trace = vcs acc pre c in
              acc1, trace :: traces)
              (acc, []) cs
          in acc1, [mk_or (List.rev_map mk_and traces)]
      | Seq (cs, pp) -> 
          let acc1, trace, _ = 
            List.fold_right (fun c (acc, trace, pre) ->
              let acc1, c_trace = vcs acc pre c in
              acc1, trace @ c_trace, pre @ c_trace)
              cs (acc, [], pre)
          in
          acc1, trace
      | Basic (bc, pp) ->
          match bc with
          | Assume s ->
              (match s.spec_form, s.spec_msg with
              | FOL f, None -> acc, [f]
              | FOL f, Some msg -> acc, [mk_comment msg f]
              | _ -> 
                  failwith "vcgen: found SL formula that should have been desugared")
          | Assert s ->
              let f, msg =
                (match s.spec_form, s.spec_msg with
                | FOL f, None -> 
                    let msg = 
                      Printf.sprintf "assert_%d_%d" 
                        s.spec_pos.sp_start_line s.spec_pos.sp_start_col
                    in
                    mk_not f, msg
                | FOL f, Some msg -> mk_not f, msg
                | _ ->
                    failwith "vcgen: found SL formula that should have been desugared")
              in
              let vc_name = str_of_ident proc.proc_name ^ "_" ^ msg in
              let vc = pre @ [f] in
              (vc_name, vc) :: acc, []
          | _ -> 
              failwith "vcgen: found unexpected basic command that should have been desugared"
    in
    match proc.proc_body with
    | Some body -> fst (vcs acc [] body)
    | None -> acc
  in
  IdMap.fold (fun _ proc acc -> vcp acc proc) prog.prog_procs

