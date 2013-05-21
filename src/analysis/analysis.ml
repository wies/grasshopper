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

let alloc_id = mk_ident "Alloc"

let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

let frame_id = mk_ident "Frame"

let frame_set = mk_free_const ~srt:(Set Loc) frame_id

let compile_to_fol prog =
  let compile_proc proc =
    let alloc_decl = 
      { var_name = alloc_id;
        var_orig_name = name alloc_id;
        var_sort = Set Loc;
        var_is_ghost = true;
        var_is_aux = true;
        var_pos = proc.proc_pos;
      }
    in
    let frame_decl = 
      { alloc_decl with 
        var_name = frame_id; 
        var_orig_name = name frame_id; 
      }
    in
    let locals1 = IdMap.add alloc_decl.var_name alloc_decl proc.proc_locals in
    let locals2 = IdMap.add frame_decl.var_name frame_decl locals1 in
    let returns = alloc_id :: frame_id :: proc.proc_returns in
    let formals = alloc_id :: frame_id :: proc.proc_returns in
    { proc with
      proc_formals = formals;
      proc_returns = returns;
      proc_locals = locals2;
    } 
  in
  { prog with prog_procs = IdMap.map compile_proc prog.prog_procs }

let elim_new_dispose prog =
  let elim = function
    | (New nc, pp) ->
        let havoc = mk_havoc_cmd [nc.new_lhs] pp.pp_pos in
        let arg = mk_free_const ~srt:nc.new_sort nc.new_lhs in
        let aux =
          match nc.new_sort with
          | Loc ->          
              let new_loc = mk_and [mk_not (mk_elem arg alloc_set); mk_neq arg mk_null] in
              let sf = mk_spec_form (FOL new_loc) false (Some "new") pp.pp_pos in
              let assume_fresh = mk_assume_cmd sf pp.pp_pos in
              let assign_alloc = mk_assign_cmd [alloc_id] [mk_union [alloc_set; mk_setenum [arg]]] pp.pp_pos in
              [assume_fresh; assign_alloc]
          | _ -> []
        in
        Seq (havoc :: aux, pp)
    | (Dispose dc, pp) ->
        let arg = dc.dispose_arg in
        let arg_in_alloc = FOL (mk_elem arg alloc_set) in
        let sf = mk_spec_form arg_in_alloc false (Some "check_dispose") pp.pp_pos in
        let check_dispose = mk_assert_cmd sf pp.pp_pos in
        let assign_alloc = mk_assign_cmd [alloc_id] [mk_diff alloc_set (mk_setenum [arg])] pp.pp_pos in
        Seq ([check_dispose; assign_alloc], pp)
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc = { proc with proc_body = Util.optmap (map_basic elim) proc.proc_body } in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }

(** Eliminate all return commands.
 ** Assumes that all SL formulas have been desugared. *)
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

(** Eliminate assignment and havoc commands (via SSA computation) 
 ** Assumes that:
 ** - all SL formulas have been desugared
 ** - all loops have been eliminated 
 ** - the only remaining basic commands are assume/assert/assign/havoc. *)
let elim_assign_havoc prog =
  let subst_spec sm sf =
    match sf.spec_form with
    | FOL f -> { sf with spec_form = FOL (subst_id sm f) }
    | SL _ -> failwith "elim_assign: found SL formula that should have been desugared."
  in
  let elim_proc proc =
    let fresh_decl id pos =
      let decl = find_var prog proc id in
      let id1 = fresh_ident (name id) in
      let decl1 = 
        { decl with 
          var_name = id1;
          var_is_aux = true;
          var_pos = pos;
        }
      in decl1
    in
    let fresh sm locals pos ids =
      List.fold_left (fun (sm, locals) id ->
        let decl = fresh_decl id pos in
        IdMap.add id decl.var_name sm, 
        IdMap.add decl.var_name decl locals)
        (sm, locals) ids
    in
    let rec elim sm locals = function
      | Loop _ as c -> sm, locals, c
      | Seq (cs, pp) ->
          let sm, locals, cs1 = 
            List.fold_right 
              (fun c (sm, locals, cs1) ->
                let sm, locals, c1 = elim sm locals c in
                sm, locals, c1 :: cs1)
              cs (sm, locals, [])
          in
          sm, locals, Seq (cs1, pp)
      | Choice (cs, pp) ->
          let sms, locals, cs1 =
            List.fold_right  
              (fun c (sms, locals, cs1) ->
                let sm1, locals, c1 = elim sm locals c in
                sm1 :: sms, locals, c1 :: cs1)
              cs ([], locals, [])
          in
          let sm_join = 
            List.fold_left 
              (fun sm1 sm -> 
                IdMap.merge 
                  (fun x -> function 
                    | None -> (function 
                        | None -> None
                        | Some z -> Some z)
                    | Some y -> (function
                        | None -> Some y
                        | Some z -> Some y)
                  )
                  sm1 sm
              )
              IdMap.empty sms
          in
          let cs2 =
            List.fold_right2 (fun sm_c c cs2 ->
              let pp = prog_point c in
              let eqs = 
                IdSet.fold 
                  (fun x eqs ->
                    let x_join = IdMap.find x sm_join in
                    let x_c = IdMap.find x sm_c in
                    if x_join  = x_c then eqs
                    else 
                      let x_decl = find_var prog proc x in
                      let x_srt = x_decl.var_sort in
                      let xc = mk_free_const ~srt:x_srt x_c in
                      let xj = mk_free_const ~srt:x_srt x_join in
                      mk_eq xj xc :: eqs
                  )
                  pp.pp_modifies []
              in 
              let sf = mk_spec_form (FOL (mk_and eqs)) false (Some "join") pp.pp_pos in
              Seq ([c; mk_assume_cmd sf pp.pp_pos], pp) :: cs2)
              sms cs1 []
          in
          sm_join, locals, Choice (cs2, pp)
      | Basic (bc, pp) ->
          match bc with
          | Assume sf -> 
              sm, locals, Basic (Assume (subst_spec sm sf), pp)
          | Assert sf ->
              sm, locals, Basic (Assert (subst_spec sm sf), pp)
          | Havoc hc ->
              let sm1, locals = fresh sm locals pp.pp_pos hc.havoc_args in
              sm1, locals, Seq ([], pp)
          | Assign ac ->
              let sm1, locals = fresh sm locals pp.pp_pos ac.assign_lhs in
              let eqs =
                List.map2 
                  (fun x e ->
                    let x_decl = find_var prog proc x in
                    let x1 = mk_free_const ~srt:x_decl.var_sort (IdMap.find x sm1) in
                    let e1 = subst_id_term sm e in
                    mk_eq x1 e1)
                  ac.assign_lhs ac.assign_rhs
              in
              let sf = mk_spec_form  (FOL (mk_and eqs)) false (Some "assign") pp.pp_pos in
              sm1, locals, mk_assume_cmd sf pp.pp_pos
          | _ -> sm, locals, Basic (bc, pp)
    in
    let locals, body =
      match proc.proc_body with
      | None -> proc.proc_locals, None
      | Some body -> 
          let _, locals, body1 = elim IdMap.empty proc.proc_locals body in
          locals, Some body1
    in
    { proc with proc_locals = locals; proc_body = body }
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

