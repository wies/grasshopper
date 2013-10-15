open Form
open FormUtil
open Prog
open AuxNames
open Reachify

(** Desugare SL specification to FOL specifications. 
 ** Assumes that loops have been transformed to tail-recursive procedures. *)
let elim_sl prog =
  let compile_proc proc =
    (* add auxiliary set variables *)
    let new_locals = 
      let alloc_decl = mk_set_decl alloc_id proc.proc_pos in
      (alloc_id, { alloc_decl with var_is_implicit = true }) ::
      List.map (fun id -> (id, mk_set_decl id proc.proc_pos)) 
        [init_alloc_id; final_alloc_id; frame_id; final_alloc_callee_id; init_alloc_callee_id]
    in
    let locals =
      List.fold_left 
        (fun locals (id, decl) -> IdMap.add id decl locals)
        proc.proc_locals 
        new_locals
    in
    let returns = proc.proc_returns @ [init_alloc_id; final_alloc_id] in
    let formals = proc.proc_formals @ [frame_id; alloc_id] in
    let convert_sl_form sfs name =
      let fs, aux, kind = 
        List.fold_right (fun sf (fs, aux, kind) -> 
          let new_kind = 
            match kind with
            | Free -> sf.spec_kind
            | k -> k
          in
          match sf.spec_form, aux with
          | SL f, None -> 
              f :: fs, 
              Some (sf.spec_name, sf.spec_msg, sf.spec_pos),
              new_kind
          | SL f, Some (_, _, p) -> 
              f :: fs, 
              Some (sf.spec_name, sf.spec_msg, merge_src_positions p sf.spec_pos),
              new_kind
          | _ -> fs, aux, kind)
          sfs ([], None, Free)
      in
      let name, msg, pos = Util.safe_unopt (name, None, dummy_position) aux in
      SlUtil.mk_sep_star_lst fs, kind, name, msg, pos
    in
    (* compile SL precondition *)
    let sl_precond, other_precond = List.partition is_sl_spec proc.proc_precond in
    let precond, free_precond =
      let name = "precondition of " ^ str_of_ident proc.proc_name in
      let f, _, name, msg, pos = convert_sl_form sl_precond name in
      let f_notin_frame = ToGrass.to_grass_not_contained pred_to_form frame_id f in
      let f_eq_init_alloc = 
        mk_and [ToGrass.to_grass pred_to_form alloc_id f; mk_subseteq alloc_set frame_set] in
      let precond = mk_spec_form (FOL f_eq_init_alloc) name msg pos in
      let fp_name = "initial footprint of " ^ str_of_ident proc.proc_name in
      let free_precond = 
        FOL (mk_not (mk_elem mk_null alloc_set))
      in
      { precond with spec_form_negated = Some f_notin_frame }, 
      mk_free_spec_form free_precond fp_name None pos
    in
    (* compile SL postcondition *)
    let sl_postcond, other_postcond = List.partition is_sl_spec proc.proc_postcond in
    let postcond, post_pos =
      let name = "postcondition of " ^ str_of_ident proc.proc_name in
      let f, kind, name, msg, pos = convert_sl_form sl_postcond name in
      
      let f_eq_final_alloc = 
        ToGrass.to_grass pred_to_form final_alloc_id f in
      let f_neq_final_alloc = ToGrass.to_grass_negated pred_to_form final_alloc_id f in
      let final_alloc_postcond = mk_spec_form (FOL f_eq_final_alloc) name msg pos in
      let init_alloc_postcond = 
        mk_free_spec_form (FOL (mk_eq init_alloc_set (oldify_term (IdSet.singleton alloc_id) alloc_set))) name msg pos
      in
      [{ final_alloc_postcond with 
        spec_kind = kind;
        spec_form_negated = Some f_neq_final_alloc;
      }; init_alloc_postcond], pos
    in
    (* generate frame condition *) 
    let framecond = 
      let frame_wo_alloc = mk_diff frame_set init_alloc_set in
      let name = "framecondition of " ^ (str_of_ident proc.proc_name) in
      let mk_framecond f = mk_free_spec_form (FOL f) name None post_pos in
      (* null is not allocated *)
      mk_framecond (mk_not (smk_elem mk_null final_alloc_set)) ::
      (* final footprint is disjoint from frame w/o alloc *)
      mk_framecond (mk_eq (mk_inter [final_alloc_set; frame_wo_alloc]) (mk_empty (Some (Set Loc)))) ::
      (* frame axioms for modified fields
       * in this version the frame contains all the pairs of fields both unprimed and primed
       *)
      let all_fields =
        List.fold_left
          (fun acc var ->
            match var.var_sort with
            | Fld _ -> IdSet.add var.var_name acc 
            | _ -> acc
          )
          IdSet.empty
          (vars prog)
      in
      let mod_fields =
        IdSet.inter
          all_fields 
          (modifies_proc prog proc)
      in
      let fields_for_frame =
        IdSet.fold
          (fun var frames ->
            let old_var = 
              if IdSet.mem var mod_fields then oldify var
              else var
            in
            let srt = (find_global prog var).var_sort in
              (mk_free_const ~srt:srt old_var) ::
              (mk_free_const ~srt:srt var) ::
              frames
          )
          all_fields
          []
      in
        mk_framecond (mk_frame_lst init_alloc_set frame_set fields_for_frame) :: []
    in
    (* update all procedure calls and return commands in body *)
    let rec compile_stmt = function
      | (Call cc, pp) ->
          let assign_alloc =
            let new_alloc_set =
              mk_union [final_alloc_callee_set; (mk_diff alloc_set init_alloc_callee_set)]
            in
            mk_assign_cmd [alloc_id] [new_alloc_set] pp.pp_pos
          in
          let cc1 = 
            { cc with 
              call_lhs = cc.call_lhs @ [init_alloc_callee_id; final_alloc_callee_id];
              call_args = cc.call_args @ [alloc_set];
            } 
          in
          mk_seq_cmd [Basic (Call cc1, pp); assign_alloc] pp.pp_pos
      | (Return rc, pp) ->
          let rc1 = { return_args = rc.return_args @ [init_alloc_set; alloc_set] } in
          Basic (Return rc1, pp)
      | (Assume sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = ToGrass.to_grass pred_to_form alloc_id f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assume_cmd sf1 pp.pp_pos
          | FOL f -> Basic (Assume sf, pp))
      | (Assert sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = ToGrass.to_grass pred_to_form alloc_id f in
              let f1_negated = ToGrass.to_grass_negated pred_to_form alloc_id f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assert_cmd { sf1 with spec_form_negated = Some f1_negated } pp.pp_pos
          | FOL f -> Basic (Assert sf, pp))
      | (c, pp) -> Basic (c, pp)
    in
    let body = 
      Util.optmap 
        (fun body ->
          let body1 = map_basic_cmds compile_stmt body in
          let assign_init_alloc = mk_assign_cmd [init_alloc_id] [alloc_set] free_precond.spec_pos in
          let assign_final_alloc = mk_assign_cmd [final_alloc_id] [alloc_set] free_precond.spec_pos in
          mk_seq_cmd [assign_init_alloc; body1; assign_final_alloc] (prog_point body).pp_pos
        ) proc.proc_body 
    in
    (*let old_footprint = 
      oldify_spec (modifies_proc prog proc) footprint
    in*)
    { proc with
      proc_formals = formals;
      proc_returns = returns;
      proc_locals = locals;
      proc_precond = precond :: free_precond :: other_precond;
      proc_postcond = postcond @ framecond @ other_postcond;
      proc_body = body;
    } 
  in
  let preds = fold_preds compile_pred_acc_new IdMap.empty prog in
  let prog = { prog with prog_preds = preds } in
  { prog with prog_procs = IdMap.map compile_proc prog.prog_procs }

(** Annotate safety checks for heap accesses *)
let annotate_heap_checks prog =
  let rec derefs acc = function
    | App (Read, [fld; loc], _) ->
        derefs (derefs (TermSet.add loc acc) fld) loc
    | App (Write, fld :: loc :: ts, _) ->
        List.fold_left derefs (TermSet.add loc acc) (fld :: loc :: ts)
    | App (_, ts, _) -> 
        List.fold_left derefs acc ts
    | _ -> acc
  in
  let mk_term_checks pos acc t =
    let locs = derefs TermSet.empty t in
    TermSet.fold 
      (fun t acc ->
        let t_in_alloc = FOL (mk_elem t alloc_set) in
        let mk_msg callee pos = "Possible heap access through null or dangling reference." in
        let sf = mk_spec_form t_in_alloc "check heap access" (Some mk_msg) pos in
        let check_access = mk_assert_cmd sf pos in
        check_access :: acc)
      locs acc
  in
  let ann_term_checks ts cmd =
    let checks = List.fold_left (mk_term_checks (source_pos cmd)) [] ts in
    mk_seq_cmd (checks @ [cmd]) (source_pos cmd)
  in
  let annotate = function
    | (Assign ac, pp) ->
        ann_term_checks ac.assign_rhs (Basic (Assign ac, pp))
    | (Dispose dc, pp) ->
        let arg = dc.dispose_arg in
        let arg_in_alloc = FOL (mk_elem arg alloc_set) in
        let mk_msg callee pos = "This deallocation might be unsafe." in
        let sf = mk_spec_form arg_in_alloc "check free" (Some mk_msg) pp.pp_pos in
        let check_dispose = mk_assert_cmd sf pp.pp_pos in
        let arg_checks = mk_term_checks pp.pp_pos [check_dispose] arg in
        mk_seq_cmd (arg_checks @ [Basic (Dispose dc, pp)]) pp.pp_pos
    | (Call cc, pp) ->
        ann_term_checks cc.call_args (Basic (Call cc, pp))
    | (Return rc, pp) ->
        ann_term_checks rc.return_args (Basic (Return rc, pp))
    | (bc, pp) -> Basic (bc, pp)
  in
  let annotate_proc proc = 
    { proc with proc_body = Util.optmap (map_basic_cmds annotate) proc.proc_body } 
  in
  { prog with prog_procs = IdMap.map annotate_proc prog.prog_procs }

(** Eliminate all new and dispose commands.
 ** Assumes that alloc sets have been introduced. *)
let elim_new_dispose prog =
  let elim = function
    | (New nc, pp) ->
        let havoc = mk_havoc_cmd [nc.new_lhs] pp.pp_pos in
        let arg = mk_free_const ~srt:nc.new_sort nc.new_lhs in
        let aux =
          match nc.new_sort with
          | Loc ->          
              let new_loc = mk_and [mk_not (mk_elem arg alloc_set); mk_neq arg mk_null] in
              let sf = mk_spec_form (FOL new_loc) "new" None pp.pp_pos in
              let assume_fresh = mk_assume_cmd sf pp.pp_pos in
              let assign_alloc = mk_assign_cmd [alloc_id] [mk_union [alloc_set; mk_setenum [arg]]] pp.pp_pos in
              [assume_fresh; assign_alloc]
          | _ -> []
        in
        mk_seq_cmd (havoc :: aux) pp.pp_pos
    | (Dispose dc, pp) ->
        let arg = dc.dispose_arg in
        let assign_alloc = 
          mk_assign_cmd [alloc_id] [mk_diff alloc_set (mk_setenum [arg])] pp.pp_pos 
        in
        assign_alloc
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc = { proc with proc_body = Util.optmap (map_basic_cmds elim) proc.proc_body } in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }
