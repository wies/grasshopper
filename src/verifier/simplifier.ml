(** {5 Simplifications for verification condition generation} *)

open Grass
open GrassUtil
open Prog

(** Transform loops into tail recursive procedures. *)
let elim_loops (prog : program) =
  let first_iter_id = fresh_ident "first_iter" in
  let first_iter_decl pos = 
    { var_name = first_iter_id;
      var_orig_name = name first_iter_id;
      var_sort = Bool;
      var_is_ghost = true;
      var_is_implicit = false; 
      var_is_aux  = true;
      var_pos = pos;
      var_scope = pos;
    }
  in
  let rec elim prog dep_procs proc = function
    | Loop (lc, pp) -> 
        let proc_name = 
          fresh_ident ((string_of_ident proc.proc_name) ^ "_loop") 
        in
        let locals = 
          IdMap.filter 
            (fun id _ -> IdSet.mem id pp.pp_accesses)
            proc.proc_locals
        in
        let returns, return_decls = 
          IdMap.fold 
            (fun id decl (returns, decls) -> id :: returns, decl :: decls)
            locals ([], [])
        in
        let subst_formals, formals, locals =
          List.fold_right
            (fun decl (sm, ids, locals) -> 
              let init_id = fresh_ident (GrassUtil.name decl.var_name) in
              let local_decl = { decl with var_is_implicit = false } in
              let init_decl = { local_decl with var_name = init_id } in
              IdMap.add decl.var_name init_id sm, 
              init_id :: ids,
              IdMap.add decl.var_name local_decl (IdMap.add init_id init_decl locals)
            )
            return_decls (IdMap.empty, [], IdMap.singleton first_iter_id (first_iter_decl pp.pp_pos))
        in    
        let formals = first_iter_id :: formals in
        let id_to_term id =
          let decl = IdMap.find id locals in
          mk_free_const decl.var_sort id
        in
        let ids_to_terms ids = List.map id_to_term ids in
        let loop_call first pos = 
          let pp_call = 
            { pp_pos = pos; 
              pp_modifies = pp.pp_modifies; 
              pp_accesses = pp.pp_accesses;
            }
          in
          let call = mk_call_cmd returns proc_name (mk_bool_term first :: ids_to_terms returns) pos in
          update_ppoint pp_call call
        in
        let loop_end_pos = end_pos pp.pp_pos in
        let loop_start_pos = start_pos pp.pp_pos in
        let body, prog, dep_procs2, prebody =
          let prog, dep_procs1, prebody = 
            elim prog dep_procs proc lc.loop_prebody 
          in
          let prog, dep_procs2, postbody = 
            elim prog dep_procs1 proc lc.loop_postbody 
          in
          let init_returns = 
            mk_assign_cmd returns (ids_to_terms (List.tl formals)) loop_start_pos 
          in
          let else_cmd = 
            (*mk_return_cmd (ids_to_terms returns) loop_end_pos*)
            mk_seq_cmd [] loop_end_pos
          in
          let then_cmd = 
            mk_seq_cmd
              [ postbody;
		prebody;
                loop_call false loop_end_pos
              ] 
              pp.pp_pos
          in
          let else_msg = "This loop has been exited on the error trace" in
          let then_msg = "The body of this loop has been executed on the error trace" in
          mk_seq_cmd 
            [ init_returns;
              mk_ite 
                lc.loop_test lc.loop_test_pos
                then_cmd else_cmd 
                then_msg else_msg pp.pp_pos
            ]
            pp.pp_pos,
          prog,
          dep_procs2,
	  prebody
        in
        (* loop exit condition *)
        let loop_exit =
          let name = "loop exit condition of " ^ (string_of_ident proc_name) in
          mk_free_spec_form (FOL (mk_not lc.loop_test)) name None loop_end_pos
        in
        (* frame conditions for non modified locals *)          
        let framecond =
          List.fold_left2 
            (fun frames id init_id ->
              if IdSet.mem id pp.pp_modifies 
              then frames
              else 
                let f = mk_eq (id_to_term id) (id_to_term init_id) in
                mk_free_spec_form (FOL f) 
                  ("framecondition of " ^ string_of_ident proc_name) 
                  None pp.pp_pos :: frames
            )
            [] returns (List.tl formals)
        in
        let postcond =
          loop_exit :: 
          (* invariant *)
          List.map (fun sf -> { sf with spec_kind = Free }) lc.loop_inv
          (* framecondition *)
          @ framecond
        in
        let loop_proc = 
          { proc_name = proc_name;
            proc_formals = formals;
            proc_returns = returns;
            proc_locals = locals;
            proc_precond = List.map (subst_id_spec subst_formals) lc.loop_inv;
            proc_postcond = postcond;
            proc_body = Some body;
            proc_pos = pp.pp_pos;
            proc_deps = [];
            proc_is_tailrec = true;
          } 
        in
        let call_loop =
          loop_call true loop_start_pos
        in
        declare_proc prog loop_proc,
	proc_name :: dep_procs2,
	mk_seq_cmd [prebody; call_loop] loop_start_pos
    | Seq (cs, pp) ->
       let prog1, dep_procs1, cs1 =
         List.fold_right 
           (fun c (prog, dep_procs, cs1) ->
             let prog1, dep_procs1, c1 = elim prog dep_procs proc c in
             prog1, dep_procs1, c1 :: cs1)
           cs (prog, dep_procs, [])
       in 
       prog1, dep_procs1, mk_seq_cmd cs1 pp.pp_pos
    | Choice (cs, pp) ->
       let prog1, dep_procs1, cs1 =
         List.fold_right 
           (fun c (prog, dep_procs, cs1) ->
             let prog1, dep_procs1, c1 = elim prog dep_procs proc c in
             prog1, dep_procs1, c1 :: cs1)
           cs (prog, dep_procs, [])
       in 
       prog1, dep_procs1, mk_choice_cmd cs1 pp.pp_pos
    | Basic _ as c -> prog, dep_procs, c
  in
  let elim_proc prog proc =
    let prog1, dep_procs1, body1 =
      match proc.proc_body with
      | Some body -> 
          let prog1, dep_procs1, body1 = elim prog [] proc body in
          prog1, dep_procs1, Some body1
      | None -> prog, [], None
    in 
    let proc1 = 
      { proc with 
        proc_body = body1; 
        proc_deps = dep_procs1 @ proc.proc_deps
      } 
    in
    declare_proc prog1 proc1
  in
  fold_procs elim_proc prog prog

(** Eliminate global dependencies of predicates *)
let elim_global_deps prog =
  let elim_spec sf = 
    let get_tas p =
      let decl = find_pred prog p in
      let accs = decl.pred_accesses in
      let tas = 
        List.map 
          (fun id ->
            let decl = find_global prog id in
            mk_free_const decl.var_sort id)
          (IdSet.elements accs)
      in
      tas
    in
    let rec subst_terms = function
      | App (sym, ts, srt) ->
          let ts1 = List.map subst_terms ts in
          (match sym with
          | FreeSym id when IdMap.mem id prog.prog_preds ->
              let tas = get_tas id in
              App (FreeSym id, tas @ ts1, srt)
          | _ -> 
              App (sym, ts1, srt))
      | Var _ as t -> t
    in
    let subst_preds_sl f =
      let sf p args pos =
        let tas = get_tas p in
        SlUtil.mk_pred ?pos:pos p (tas @ args)
      in SlUtil.map_terms subst_terms (SlUtil.subst_preds sf f)
    in
    let subst_preds_fol f = 
      map_terms subst_terms f
    in
    map_spec_form subst_preds_fol subst_preds_sl sf
  in
  let elim_stmt = function
    | (Assert sf, pp) ->
        mk_assert_cmd (elim_spec sf) pp.pp_pos
    | (Assume sf, pp) ->
        mk_assume_cmd (elim_spec sf) pp.pp_pos
    | (bc, pp) -> Basic (bc, pp)
  in
  let elim_proc proc =
    let precond1 = List.map elim_spec proc.proc_precond in
    let postcond1 = List.map elim_spec proc.proc_postcond in
    let body1 = Util.Opt.map (map_basic_cmds elim_stmt) proc.proc_body in
    { proc with 
      proc_body = body1;
      proc_precond = precond1;
      proc_postcond = postcond1;
    } 
  in
  let elim_pred pred =
    let body1 = elim_spec pred.pred_body in
    let accesses = pred.pred_accesses in
    let formals1 = IdSet.elements accesses @ pred.pred_formals in
    let locals1 = 
      IdSet.fold 
        (fun id locals -> IdMap.add id (find_global prog id) locals) 
        accesses pred.pred_locals
    in
    { pred with 
      pred_body = body1; 
      pred_formals = formals1; 
      pred_locals = locals1; 
      pred_accesses = IdSet.empty;
    } 
  in
  let prog1 = map_procs elim_proc prog in
  map_preds elim_pred prog1

(** Eliminate all return commands.
 ** Assumes that all SL formulas have been desugared. *)
let elim_return prog =
  let elim returns mk_postcond_check = function
    | (Return rc, pp) ->
        let rt_assign = 
          mk_assign_cmd returns rc.return_args pp.pp_pos 
        in
        let fls = 
          mk_spec_form (FOL mk_false) "return" None pp.pp_pos 
        in
        let rt_false = mk_assume_cmd fls pp.pp_pos in
        let rt_postcond = mk_postcond_check pp.pp_pos in
        mk_seq_cmd (rt_assign :: rt_postcond @ [rt_false]) pp.pp_pos
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc =
    let mk_postcond_check = 
      let posts = 
        Util.filter_map 
          is_checked_spec
          (fun sf ->
            match sf.spec_form with
            | FOL f -> oldify_spec (id_set_of_list proc.proc_formals) sf
            | SL _ -> failwith "elim_return: Found SL formula that should have been desugared.")
          proc.proc_postcond
      in fun pos -> List.map (fun sf -> mk_assert_cmd sf pos) posts
    in
    let body = 
      (* add final check of postcondition at the end of procedure body *)
      let body1 = 
        Util.Opt.map 
          (fun body -> 
            let pos = (prog_point body).pp_pos in
            let return_pos = 
              { sp_file = pos.sp_file;
                sp_start_line = pos.sp_end_line;
                sp_start_col = pos.sp_end_col;
                sp_end_line = pos.sp_end_line;
                sp_end_col = pos.sp_end_col;
              } 
            in
            mk_seq_cmd (body :: mk_postcond_check return_pos) (prog_point body).pp_pos) 
          proc.proc_body
      in
      Util.Opt.map (map_basic_cmds (elim proc.proc_returns mk_postcond_check)) body1
         
    in
    { proc with proc_body = body }
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }


(** Eliminate all state (via SSA computation). 
 ** Assumes that:
 ** - all loops have been eliminated 
 ** - all SL formulas have been desugared
 ** - the only remaining basic commands are assume/assert/assign/havoc/call. *)
let elim_state prog =
  let elim_proc proc =
    let fresh_decl proc id pos =
      let decl = find_var prog proc id in
      let id1 = fresh_ident (name id) in
      let decl1 = 
        { decl with 
          var_name = id1;
          var_is_implicit = false;
          (*var_is_aux = true;*)
          var_pos = pos;
        }
      in decl1
    in
    let fresh proc sm locals pos ids =
      List.fold_left (fun (sm, locals) id ->
        let decl = fresh_decl proc id pos in
        IdMap.add id decl.var_name sm, 
        IdMap.add decl.var_name decl locals)
        (sm, locals) ids
    in
    let rec elim sm locals = function
      | Loop _ as c -> 
          (* ignore loops - they should have been desugared by now *)
          sm, locals, c
      | Seq (cs, pp) ->
          let sm, locals, cs1 = 
            List.fold_left 
              (fun (sm, locals, cs1) c  ->
                let sm, locals, c1 = elim sm locals c in
                sm, locals, c1 :: cs1)
              (sm, locals, []) cs
          in
          sm, locals, Seq (List.rev cs1, pp)
      | Choice (cs, pp) ->
          (* bring commands cs into SSA form *)
          let sms, locals, cs1 =
            List.fold_right  
              (fun c (sms, locals, cs1) ->
                let sm1, locals, c1 = elim sm locals c in
                sm1 :: sms, locals, c1 :: cs1)
              cs ([], locals, [])
          in
          (* compute joined substitution map *)
          let sm_join = 
            List.fold_left 
              (fun sm1 sm2 -> 
                IdMap.merge 
                  (fun x -> function 
                    | None -> (function 
                        | None -> None
                        | Some z -> Some z)
                    | Some y -> (function
                        | None -> Some y
                        | Some z -> 
                            let old_x = 
                              try IdMap.find x sm with Not_found -> x 
                            in 
                            if y = old_x then Some z else Some y)
                  )
                  sm1 sm2
              )
              IdMap.empty sms
          in
          (* add missing equalities to commands cs according to joined substitution map *)
          let cs2 =
            List.fold_right2 (fun sm_c c cs2 ->
              let eqs = 
                IdSet.fold 
                  (fun x eqs ->
                    let x_join = IdMap.find x sm_join in
                    let x_c = 
                      try IdMap.find x sm_c with Not_found -> x
                    in
                    if x_join  = x_c then eqs
                    else 
                      let x_decl = find_var prog proc x in
                      let x_srt = x_decl.var_sort in
                      let xc = mk_free_const x_srt x_c in
                      let xj = mk_free_const x_srt x_join in
                      mk_eq xj xc :: eqs
                  )
                  pp.pp_modifies []
              in 
              let sf = mk_spec_form (FOL (mk_and eqs)) "join" None pp.pp_pos in
              Seq ([c; mk_assume_cmd sf pp.pp_pos], pp) :: cs2)
              sms cs1 []
          in
          sm_join, locals, mk_choice_cmd cs2 pp.pp_pos
      | Basic (bc, pp) ->
          match bc with
          | Assume sf -> 
              sm, locals, Basic (Assume (subst_id_spec sm sf), pp)
          | Assert sf ->
              let sf1 = unoldify_spec (subst_id_spec sm sf) in
              sm, locals, Basic (Assert sf1, pp)
          | Havoc hc ->
              let sm1, locals1 = fresh proc sm locals pp.pp_pos hc.havoc_args in
              let eqs = 
                List.map 
                  (fun x ->
                    let new_x = IdMap.find x sm1 in
                    let x_decl = find_var prog proc x in
                    let x_srt = x_decl.var_sort in
                    let xc = mk_free_const x_srt new_x in
                    mk_eq xc xc
                  ) hc.havoc_args
              in
              let sf = mk_spec_form (FOL (mk_and eqs)) "havoc" None pp.pp_pos in
              sm1, locals1, mk_assume_cmd sf pp.pp_pos
          | Assign ac ->
              let sm1, locals = fresh proc sm locals pp.pp_pos ac.assign_lhs in
              let eqs =
                List.map2 
                  (fun x e ->
                    let x_decl = find_var prog proc x in
                    let x1 = mk_free_const x_decl.var_sort (IdMap.find x sm1) in
                    let e1 = subst_id_term sm e in
                    mk_eq x1 e1)
                  ac.assign_lhs ac.assign_rhs
              in
              let sf = mk_spec_form  (FOL (mk_and eqs)) "assign" None pp.pp_pos in
              sm1, locals, mk_assume_cmd sf pp.pp_pos
          | Call cc ->
              let to_term_subst_merge sm locals term_subst =
                IdMap.fold (fun id1 id2 term_subst -> 
                  let decl = IdMap.find id2 locals in
                  IdMap.add id1 (mk_free_const decl.var_sort id2) term_subst)
                  sm term_subst
              in
              let to_term_subst sm locals = to_term_subst_merge sm locals IdMap.empty in
              let callee_decl = find_proc prog cc.call_name in
              (* update actual arguments of call *)
              let args1 = List.map (subst_id_term sm) cc.call_args in
              (* compute substitution for precondition *)
              let implicit_formals, explicit_formals =
                List.partition 
                  (fun id -> (IdMap.find id callee_decl.proc_locals).var_is_implicit) 
                  callee_decl.proc_formals
              in
              let subst_pre_explicit = 
                List.fold_left2 
                  (fun sm id arg -> IdMap.add id arg sm) 
                  (to_term_subst sm locals) 
                  explicit_formals args1
              in
              let subst_implicits, locals = 
                fresh callee_decl IdMap.empty locals pp.pp_pos implicit_formals 
              in
              let subst_pre = 
                to_term_subst_merge subst_implicits locals subst_pre_explicit
              in
              (* assert updated precondition *)
              let assert_precond, assume_precond_implicits =
                let checked_preconds =
                  Util.filter_map is_checked_spec 
                    (fun sf -> subst_spec subst_pre sf)
                    callee_decl.proc_precond
                in
                let implicits = List.map (fun id -> IdMap.find id subst_implicits) implicit_formals in
                let implicitss = id_set_of_list implicits in
                let preconds_wo_implicits, preconds_w_implicits =
                  List.partition 
                    (fun sf -> IdSet.is_empty (IdSet.inter (free_consts (form_of_spec sf)) implicitss)) 
                    checked_preconds
                in
                let assume_precond_implicits = 
                  List.map 
                    (fun sf -> 
                      let sf1 = map_spec_fol_form strip_error_msgs sf in
                      mk_assume_cmd sf1 pp.pp_pos) 
                    preconds_w_implicits
                in
                (* skolemize implicits *)
                let preconds_w_implicits =
                  let fs, aux = 
                    List.fold_left (fun (fs, aux) sf ->
                      let new_aux =
                        match aux with
                        | Some (_, _, p) ->
                            Some (sf.spec_name, sf.spec_msg, merge_src_pos p sf.spec_pos)
                        | None -> Some (sf.spec_name, sf.spec_msg, sf.spec_pos)
                      in
                      form_of_spec sf :: fs, new_aux)
                      ([], None) preconds_w_implicits
                  in
                  List.map 
                    (fun (name, msg, pos) ->
                      let implicits_w_sorts, implicits_var_subst =
                        List.fold_left 
                          (fun (implicits_w_sorts, implicits_var_subst) id ->
                            let decl = IdMap.find id locals in
                            (id, decl.var_sort) :: implicits_w_sorts,
                            IdMap.add id (mk_var decl.var_sort id) implicits_var_subst) 
                          ([], IdMap.empty) implicits
                      in
                      let f_pos = mk_exists implicits_w_sorts (subst_consts implicits_var_subst (mk_and fs)) in
                      mk_spec_form (FOL f_pos) name msg pos)
                    (Util.Opt.to_list aux)
                in
                List.map (fun sf -> mk_assert_cmd sf pp.pp_pos) (preconds_wo_implicits @ preconds_w_implicits),
                assume_precond_implicits
              in
              (* compute mod set and final substitution *)
              let global_mods = IdSet.elements (modifies_proc prog callee_decl) in
              let mods = cc.call_lhs @ global_mods in
              let sm1, locals = fresh proc sm locals pp.pp_pos mods in
              let mods_havoc = 
                (* this is a work around for trace generation *)
                let eqs = 
                  List.map (fun id -> 
                    let mid = IdMap.find id sm1 in
                    let decl = IdMap.find mid locals in
                    let vid = mk_free_const decl.var_sort mid in
                    mk_eq vid vid) mods
                in
                let sf = mk_spec_form (FOL (mk_and eqs)) "havoc" None pp.pp_pos in
                [mk_assume_cmd sf pp.pp_pos]
              in
              (* compute substitution for postcondition *)
              let subst_post = 
                (* substitute formal parameters to actual parameters *)
                let subst_wo_old_mods_formals =
                  List.fold_left 
                    (fun sm id ->
                      IdMap.add (oldify id) (IdMap.find id subst_pre) sm)
                    subst_pre callee_decl.proc_formals
                in
                (* substitute formal return parameters to actual return parameters *)
                let subst_wo_old_mods = 
                  List.fold_left2
                    (fun sm id rtn_id -> 
                      let decl = IdMap.find rtn_id locals in
                      IdMap.add id (mk_free_const decl.var_sort rtn_id) sm)
                    subst_wo_old_mods_formals
                    callee_decl.proc_returns 
                    (List.map (fun id -> IdMap.find id sm1) cc.call_lhs)
                in
                (* TODO: I currently have no idea what this was supposed to do. Is this redundant? *)
                let subst_wo_old =
                  List.fold_left (fun sm id -> 
                    IdMap.add id (IdMap.find id (to_term_subst sm1 locals)) sm)
                    subst_wo_old_mods
                    mods
                in
                (* substitute old versions of global variables *)
                IdMap.fold 
                  (fun id decl subst_post ->
                    let old_id = try IdMap.find id sm with Not_found -> id in
                    IdMap.add (oldify id) (mk_free_const decl.var_sort old_id) subst_post)
                   prog.prog_vars subst_wo_old
              in
              (* assume updated postcondition *)
              let assume_postcond =
                List.map
                  (fun sf -> 
                    let old_sf = oldify_spec (id_set_of_list callee_decl.proc_formals) sf in
                    let sf1 = subst_spec subst_post old_sf in
                    let sf2 = map_spec_fol_form strip_error_msgs sf1 in
                    mk_assume_cmd sf2 pp.pp_pos)
                  callee_decl.proc_postcond
              in
              sm1, locals, mk_seq_cmd (assert_precond @ assume_precond_implicits @ mods_havoc @ assume_postcond) pp.pp_pos
          | _ -> sm, locals, Basic (bc, pp)
    in
    let locals, body =
      match proc.proc_body with
      | None -> proc.proc_locals, None
      | Some body -> 
          let _, locals, body1 = elim IdMap.empty proc.proc_locals body in
          let preconds = 
            List.map 
              (fun sf -> 
                let sf1 = map_spec_fol_form strip_error_msgs sf in
                mk_assume_cmd sf1 sf.spec_pos) 
              proc.proc_precond 
          in
          locals, Some (mk_seq_cmd (preconds @ [body1]) (prog_point body).pp_pos)
    in
    { proc with proc_locals = locals; proc_body = body }
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }
