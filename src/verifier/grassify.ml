(** {5 Translation of program with SL specifications to a pure GRASS program} *)

open Grass
open GrassUtil
open Prog
open AuxNames

(** Add reachability invariants for ghost fields of sort Loc *)
let add_ghost_field_invariants prog =
  let ghost_loc_fields =
    List.filter 
      (fun decl -> decl.var_sort = Fld Loc && decl.var_is_ghost)
      (Prog.vars prog)
  in
  let locals = IdMap.add alloc_id alloc_decl IdMap.empty in
  let preds, pred_map =
    List.fold_left (fun (preds, pred_map) decl ->
      let open Axioms in
      let fld = mk_free_const decl.var_sort decl.var_name in
      let body_form =
        mk_and 
          [ mk_name "field_eventually_null" 
              (mk_forall [l1] (mk_reach fld loc1 mk_null));
            mk_name "field_nonalloc_null"
              (mk_forall [l1; l2]
                 (mk_sequent
                    [mk_reach fld loc1 loc2]
                    [mk_eq loc1 loc2; mk_and [mk_elem loc1 alloc_set; mk_elem loc2 alloc_set]; mk_eq loc2 mk_null]));
          ]
      in
      let pred_id = fresh_ident "ghost_field_invariant" in
      let name = "ghost field invariant for " ^ string_of_ident decl.var_name in
      let body = mk_spec_form (FOL body_form) name None (decl.var_pos) in
      let pred = 
        { pred_name = pred_id;
          pred_formals = [decl.var_name; alloc_id]; 
          pred_outputs = []; 
          pred_locals = IdMap.add decl.var_name decl locals; 
          pred_body = body;
          pred_pos = decl.var_pos;
          pred_accesses = IdSet.empty;
          pred_is_free = false;
        }
      in
      (pred :: preds, IdMap.add decl.var_name pred_id pred_map)) 
      ([], IdMap.empty) 
      ghost_loc_fields
  in
  let add_invs proc = 
    let all_accesses = accesses_proc prog proc in
    let all_modifies = 
      if !Config.opt_field_mod
      then modifies_proc prog proc 
      else all_accesses
    in
    let accessed =
      List.filter 
        (fun decl -> 
          IdSet.mem alloc_id all_modifies ||
          IdSet.mem decl.var_name all_accesses) 
        ghost_loc_fields
    in
    let modified =
      List.filter 
        (fun decl -> 
          IdSet.mem alloc_id all_modifies ||
          IdSet.mem decl.var_name all_modifies) 
        ghost_loc_fields
    in
    let mk_inv decl =
      let fld = mk_free_const decl.var_sort decl.var_name in
      let pred_id = IdMap.find decl.var_name pred_map in
      let inv = mk_pred pred_id [fld; alloc_set] in
      let name = "ghost field invariant for " ^ string_of_ident decl.var_name in
      mk_spec_form (FOL inv) name None decl.var_pos
    in 
    let pre_invs = List.map mk_inv accessed in
    let post_invs = List.map mk_inv modified in
    { proc with 
      proc_precond = pre_invs @ proc.proc_precond; 
      proc_postcond = post_invs @ proc.proc_postcond;
    }
  in
  let prog1 = List.fold_left declare_pred prog preds in
  map_procs add_invs prog1


(** Desugare SL specification to FOL specifications. 
 ** Assumes that loops have been transformed to tail-recursive procedures. *)
let elim_sl prog =
  let pred_to_form p args domain = 
    let decl = find_pred prog p in
    if List.length decl.pred_formals > List.length args then
      mk_pred p (args @ [domain])
    else 
      let fp = List.hd (List.rev args) in
      mk_and [mk_eq domain fp; mk_pred p args]
  in
  (* transform the preds from SL to GRASS *)
  (*let preds =
    if !Config.predefPreds
    then fold_preds compile_pred_acc IdMap.empty prog
    else compile_preds (preds prog)
  in
  let prog = { prog with prog_preds = preds; } in *)
  let compile_proc proc =
    (* add auxiliary set variables *)
    let new_locals = 
      let footprint_decl = mk_loc_set_decl footprint_id proc.proc_pos in
      (footprint_id, { footprint_decl with var_is_implicit = true }) ::
      List.map (fun id -> (id, mk_loc_set_decl id proc.proc_pos)) 
        [footprint_caller_id; final_footprint_caller_id]
    in
    let locals =
      List.fold_left 
        (fun locals (id, decl) -> IdMap.add id decl locals)
        proc.proc_locals 
        new_locals
    in
    let returns = proc.proc_returns @ [final_footprint_caller_id] in
    let formals = proc.proc_formals @ [footprint_caller_id; footprint_id] in
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
      let name, msg, pos = Util.Opt.get_or_else (name, None, dummy_position) aux in
      SlUtil.mk_sep_star_lst fs, kind, name, msg, pos
    in
    (* translate SL precondition *)
    let sl_precond, other_precond = List.partition is_sl_spec proc.proc_precond in
    let precond, free_precond =
      let name = "precondition of " ^ string_of_ident proc.proc_name in
      let f, _, name, msg, pos = convert_sl_form sl_precond name in
      let f_eq_init_footprint =  
        propagate_exists (mk_and [SlToGrass.to_grass pred_to_form footprint_set f; 
                                  mk_subseteq footprint_set footprint_caller_set])
      in
      let precond = mk_spec_form (FOL f_eq_init_footprint) name msg pos in
      let fp_name = "initial footprint of " ^ string_of_ident proc.proc_name in
      let free_precond = 
        FOL (mk_and [mk_subseteq footprint_caller_set alloc_set; mk_not (mk_elem mk_null alloc_set)])
      in
      precond,
      mk_free_spec_form free_precond fp_name None pos
    in
    (* translate SL postcondition *)
    let init_alloc_set = oldify_term (IdSet.singleton alloc_id) alloc_set in
    let init_footprint_caller_set = footprint_caller_set in
    let init_footprint_set = footprint_set in
    let final_footprint_set = 
      mk_union [mk_inter [alloc_set; init_footprint_set];
                mk_diff alloc_set init_alloc_set]
    in
    let final_alloc_set =
      mk_union [mk_diff init_alloc_set init_footprint_caller_set;
                final_footprint_caller_set]
    in
    let sl_postcond, other_postcond = List.partition is_sl_spec proc.proc_postcond in
    let postcond, post_pos =
      let name = "postcondition of " ^ string_of_ident proc.proc_name in
      let f, kind, name, msg, pos = convert_sl_form sl_postcond name in
      let f_eq_final_footprint = 
        SlToGrass.to_grass pred_to_form final_footprint_set f 
      in
      let final_footprint_postcond = mk_spec_form (FOL f_eq_final_footprint) name msg pos in
      (*let init_footprint_postcond = 
        mk_free_spec_form (FOL (mk_eq init_footprint_set (oldify_term (IdSet.singleton footprint_id) footprint_set))) name msg pos
      in*)
      [{ final_footprint_postcond with 
        spec_kind = kind;
       }], pos
    in
    (* generate frame condition by applying the frame rule *) 
    let framecond = 
      let name = "framecondition of " ^ (string_of_ident proc.proc_name) in
      let mk_framecond f = mk_free_spec_form (FOL f) name None post_pos in
      (* final caller footprint is frame with final footprint *)
      let final_footprint_caller_postcond = 
        mk_eq final_footprint_caller_set 
          (mk_union [mk_diff init_footprint_caller_set init_footprint_set;
                     final_footprint_set])
      in
      mk_framecond final_footprint_caller_postcond ::
      (* null is not allocated *)
      mk_framecond (mk_and [mk_eq alloc_set final_alloc_set; 
                            mk_not (smk_elem mk_null alloc_set)]) ::
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
      let frame_preds =
        IdSet.fold
          (fun var frames ->
            let old_var = oldify var in
            let srt = (find_global prog var).var_sort in
            mk_framecond (mk_frame init_footprint_set init_alloc_set 
                             (mk_free_const srt old_var)
                             (mk_free_const srt var)) ::
            frames
          )
          all_fields
          []
      in
      frame_preds
    in
    (* update all procedure calls and return commands in body *)
    let rec compile_stmt = function
      | (Call cc, pp) ->
          mk_call_cmd ~prog:(Some prog) 
            (cc.call_lhs @ [footprint_id]) 
            cc.call_name 
            (cc.call_args @ [footprint_set]) 
            pp.pp_pos
      | (Return rc, pp) ->
          let rc1 = { return_args = rc.return_args @ [mk_union [footprint_caller_set; footprint_set]] } in
          Basic (Return rc1, pp)
      | (Assume sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = SlToGrass.to_grass pred_to_form footprint_set f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assume_cmd sf1 pp.pp_pos
          | FOL f -> Basic (Assume sf, pp))
      | (Assert sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = SlToGrass.to_grass pred_to_form footprint_set f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assert_cmd sf1 pp.pp_pos
          | FOL f -> Basic (Assert sf, pp))
      | (c, pp) -> Basic (c, pp)
    in
    let body = 
      Util.Opt.map 
        (fun body ->
          let body1 = map_basic_cmds compile_stmt body in
          let body_pp = prog_point body in
          let assign_init_footprint_caller =
            let new_footprint_caller_set =
              mk_diff footprint_caller_set footprint_set
            in
            mk_assign_cmd 
              [footprint_caller_id] 
              [new_footprint_caller_set] 
              body_pp.pp_pos
          in
          let assign_final_footprint_caller =
            mk_assign_cmd 
              [final_footprint_caller_id] 
              [mk_union [footprint_caller_set; footprint_set]] 
              body_pp.pp_pos
          in
          mk_seq_cmd 
            [assign_init_footprint_caller; body1; assign_final_footprint_caller]
            body_pp.pp_pos
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
  add_ghost_field_invariants (map_procs compile_proc prog)

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
        let t_in_footprint = FOL (mk_elem t footprint_set) in
        let mk_msg callee = "Possible invalid heap access", "" in
        let sf = mk_spec_form t_in_footprint "check heap access" (Some mk_msg) pos in
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
        let arg_in_footprint = FOL (mk_elem arg footprint_set) in
        let mk_msg callee = "This deallocation might be unsafe", "" in
        let sf = 
          mk_spec_form arg_in_footprint "check free" (Some mk_msg) pp.pp_pos 
        in
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
    { proc with proc_body = Util.Opt.map (map_basic_cmds annotate) proc.proc_body } 
  in
  map_procs annotate_proc prog


(** Eliminate all new and dispose commands.
 ** Assumes that footprint sets have been introduced. *)
let elim_new_dispose prog =
  let elim = function
    | (New nc, pp) ->
        let havoc = mk_havoc_cmd [nc.new_lhs] pp.pp_pos in
        let arg = mk_free_const nc.new_sort nc.new_lhs in
        let aux =
          match nc.new_sort with
          | Loc ->          
              let new_loc = mk_and [mk_not (mk_elem arg alloc_set); mk_neq arg mk_null] in
              let sf = mk_spec_form (FOL new_loc) "new" None pp.pp_pos in
              let assume_fresh = mk_assume_cmd sf pp.pp_pos in
              let assign_alloc = 
                mk_assign_cmd 
                  [alloc_id] 
                  [mk_union [alloc_set; mk_setenum [arg]]] 
                  pp.pp_pos 
              in
              let assign_footprint = 
                mk_assign_cmd 
                  [footprint_id] 
                  [mk_union [footprint_set; mk_setenum [arg]]] 
                  pp.pp_pos 
              in
              [assume_fresh; assign_alloc; assign_footprint]
          | _ -> []
        in
        mk_seq_cmd (havoc :: aux) pp.pp_pos
    | (Dispose dc, pp) ->
        let arg = dc.dispose_arg in
        let assign_alloc = 
          mk_assign_cmd 
            [alloc_id] 
            [mk_diff alloc_set (mk_setenum [arg])] 
            pp.pp_pos 
        in
        let assign_footprint = 
          mk_assign_cmd 
            [footprint_id] 
            [mk_diff footprint_set (mk_setenum [arg])] 
            pp.pp_pos 
        in
        mk_seq_cmd [assign_alloc; assign_footprint] pp.pp_pos
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc = 
    { proc with proc_body = Util.Opt.map (map_basic_cmds elim) proc.proc_body } 
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }
