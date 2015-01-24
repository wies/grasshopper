(** {5 Translation of program with SL specifications to a pure GRASS program} *)

open Grass
open GrassUtil
open Prog

(** Auxiliary variables for desugaring SL specifications *)
let footprint_id = mk_name_generator "FP"
let footprint_set struct_srt = mk_loc_set struct_srt (footprint_id struct_srt)

let footprint_caller_id = mk_name_generator "FP_Caller"
let footprint_caller_set struct_srt = mk_loc_set struct_srt (footprint_caller_id struct_srt)

let final_footprint_caller_id = mk_name_generator "FP_Caller_final"
let final_footprint_caller_set struct_srt = mk_loc_set struct_srt (final_footprint_caller_id struct_srt)

(** Auxiliary variables for desugaring arrays *)

let array_state_id = mk_name_generator "array_state"
let array_state srt = mk_free_const (Map (Loc (ArrayCell srt), srt)) (array_state_id srt)
let array_state_decl srt =
  let id = array_state_id srt in
  { var_name = id;
    var_orig_name = name id;
    var_sort = Map (Loc (ArrayCell srt), srt);
    var_is_ghost = false;
    var_is_implicit = false;
    var_is_aux = true;
    var_pos = dummy_position;
    var_scope = global_scope
  }

let tmp_array_cell_set_id =
  let gen = mk_name_generator "tmp" in
  fun srt -> gen (ArrayCell srt) 
let tmp_array_cell_set_decl srt = mk_loc_set_decl (ArrayCell srt) (tmp_array_cell_set_id srt) dummy_position
let tmp_array_cell_set srt = mk_free_const (Set (Loc (ArrayCell srt))) (tmp_array_cell_set_id srt)
    
(** Add reachability invariants for ghost fields of sort Loc *)
let add_ghost_field_invariants prog =
  let ghost_loc_fields =
    List.filter 
      (fun decl ->
        match decl.var_sort with
        | Map (Loc id1, Loc id2) -> id1 = id2 && decl.var_is_ghost
        | _ -> false)
      (Prog.vars prog)
  in
  let mk_inv_pred (preds, pred_map, alloc_ids) decl =
    let open Axioms in
    let struct_srt = struct_sort_of_sort (dom_sort decl.var_sort) in
    let alloc_decl, alloc_set, alloc_id = alloc_all struct_srt in
    let locals = IdMap.add alloc_id alloc_decl IdMap.empty in
    let fld = mk_free_const decl.var_sort decl.var_name in
    let l1 = Axioms.l1 struct_srt in
    let loc1 = Axioms.loc1 struct_srt in
    let l2 = Axioms.l2 struct_srt in
    let loc2 = Axioms.loc2 struct_srt in
    let null = mk_null struct_srt in
    let body_form =
      mk_and 
        [ mk_name "field_eventually_null" 
            (mk_forall [l1] (mk_reach fld loc1 null));
          mk_name "field_nonalloc_null"
            (mk_forall [l1; l2]
               (mk_sequent
                  [mk_reach fld loc1 loc2]
                  [mk_eq loc1 loc2; mk_and [mk_elem loc1 alloc_set; mk_elem loc2 alloc_set]; mk_eq loc2 null]));
          ]
    in
    let pred_id = fresh_ident "ghost_field_invariant" in
    let name = "ghost field invariant for " ^ string_of_ident decl.var_name in
    let body = mk_spec_form (FOL body_form) name None (decl.var_pos) in
    let pred = 
      { pred_name = pred_id;
        pred_formals = [decl.var_name; alloc_id];
        pred_footprints = [];
        pred_outputs = []; 
        pred_locals = IdMap.add decl.var_name decl locals; 
        pred_body = body;
        pred_pos = decl.var_pos;
        pred_accesses = IdSet.empty;
        pred_is_free = false;
      }
    in
    pred :: preds,
    IdMap.add decl.var_name pred_id pred_map,
    IdSet.add alloc_id alloc_ids
  in
  let preds, pred_map, alloc_ids =
    List.fold_left mk_inv_pred ([], IdMap.empty, IdSet.empty) ghost_loc_fields
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
          IdSet.empty <> IdSet.inter alloc_ids all_modifies ||
          IdSet.mem decl.var_name all_accesses) 
        ghost_loc_fields
    in
    let modified =
      List.filter 
        (fun decl -> 
          IdSet.empty <> IdSet.inter alloc_ids all_modifies ||
          IdSet.mem decl.var_name all_modifies) 
        ghost_loc_fields
    in
    let mk_inv decl =
      let fld = mk_free_const decl.var_sort decl.var_name in
      let pred_id = IdMap.find decl.var_name pred_map in
      let struct_srt = struct_sort_of_sort (dom_sort decl.var_sort) in
      let inv = mk_pred pred_id [fld; alloc_set struct_srt] in
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

(** Desugare arrays. *)
let elim_arrays prog =
  let rec compile_term = function
    | Var (id, srt) -> Var (id, srt)
    | App (Read, [map; idx], _) ->
        let map1 = compile_term map in
        let idx1 = compile_term idx in
        (match sort_of map with
        | Loc (Array srt) -> mk_read (array_state srt) (mk_read (mk_array_cells map1) idx1)
        | _ -> mk_read map1 idx1)
    | App (sym, ts, srt) ->
        let ts1 = List.map compile_term ts in
        App (sym, ts1, srt)
  in
  let rec compile_grass_form = function
    (* TODO: convert annotations *)
    | Atom (t, ann) -> Atom (compile_term t, ann)
    | BoolOp (op, fs) -> BoolOp (op, List.map compile_grass_form fs)
    | Binder (b, vs, f, ann) ->
        Binder (b, vs, compile_grass_form f, ann)
  in
  let rec compile_sl_form = function
    | Sl.Pure (p, pos) ->
        Sl.Pure (compile_grass_form p, pos)
    | Sl.Atom (a, ts, pos) ->
        Sl.Atom (a, List.map compile_term ts, pos)
    | Sl.SepOp (op, f1, f2, pos) ->
        Sl.SepOp (op, compile_sl_form f1, compile_sl_form f2, pos)
    | Sl.BoolOp (op, fs, pos) ->
        Sl.BoolOp (op, List.map compile_sl_form fs, pos)
    | Sl.Binder (b, vs, f, pos) ->
        Sl.Binder (b, vs, compile_sl_form f, pos)
  in
  let compile_spec = Prog.map_spec_form compile_grass_form compile_sl_form in
  let rec compile_cmd = function
    | Loop (lc, pp) ->
        let cond = compile_grass_form lc.loop_test in
        let preb = compile_cmd lc.loop_prebody in
        let postb = compile_cmd lc.loop_postbody in
        let inv = List.map (Prog.map_spec_form compile_grass_form compile_sl_form) lc.loop_inv in
        mk_loop_cmd inv preb cond lc.loop_test_pos postb pp.pp_pos
    | Seq (cs, pp) ->
       let cs1 = List.map compile_cmd cs in
       mk_seq_cmd cs1 pp.pp_pos
    | Choice (cs, pp) ->
       let cs1 = List.map compile_cmd cs in
       mk_choice_cmd cs1 pp.pp_pos
    | Basic (Assign ac, pp) ->
        let lhs1, rhs1, aux_cmds =
          List.fold_right2 (fun lhs rhs (lhs1, rhs1, aux_cmds) ->
            match lhs, rhs with
            | id1, App (Write, [App (FreeSym id2, [], _) as map; idx; upd], Loc (Array srt)) ->
                let idx1 = compile_term idx in
                let upd1 = compile_term upd in
                let map1 = compile_term map in
                let aux_cmds1 =
                  if id1 = id2 then aux_cmds else
                  let aux_ac = mk_assign_cmd [id1] [map1] pp.pp_pos in
                  aux_ac :: aux_cmds
                in
                array_state_id srt :: lhs1,
                mk_write (array_state srt) (mk_read (mk_array_cells map1) idx1) upd1 :: rhs1,
                aux_cmds1
            | id, t -> id :: lhs1, compile_term t :: rhs1, aux_cmds)            
            ac.assign_lhs ac.assign_rhs ([], [], [])
        in
        mk_seq_cmd (mk_assign_cmd lhs1 rhs1 pp.pp_pos :: aux_cmds) pp.pp_pos
    | Basic (Assume sf, pp) ->
        let sf1 = compile_spec sf in
        mk_assume_cmd sf1 pp.pp_pos
    | Basic (Assert sf, pp) ->
        let sf1 = compile_spec sf in
        mk_assert_cmd sf1 pp.pp_pos
    | Basic (Return rc, pp) ->
        let args1 = List.map compile_term rc.return_args in
        mk_return_cmd args1 pp.pp_pos
    | Basic (Call cc, pp) ->
        let args1 = List.map compile_term cc.call_args in
        mk_call_cmd cc.call_lhs cc.call_name args1 pp.pp_pos
    | Basic (New nc, pp) ->
        let args = List.map compile_term nc.new_args in
        mk_new_cmd nc.new_lhs nc.new_sort args pp.pp_pos
    | Basic (Dispose dc, pp) ->
        let arg = compile_term dc.dispose_arg in
        mk_dispose_cmd arg pp.pp_pos
    | c -> c
  in
  let compile_proc (elem_sorts, procs) proc =
    let locals, elem_sorts =
      IdMap.fold
        (fun id decl (locals, elem_sorts) ->
          match decl.var_sort with
          | Loc (Array srt) ->
              let tmp_decl = tmp_array_cell_set_decl srt in
              IdMap.add tmp_decl.var_name tmp_decl locals,
              SortSet.add srt elem_sorts
          | _ -> locals, elem_sorts)
        proc.proc_locals (proc.proc_locals, elem_sorts)
    in
    let body1 = Util.Opt.map compile_cmd proc.proc_body in
    let precond1 = List.map compile_spec proc.proc_precond in
    let postcond1 = List.map compile_spec proc.proc_postcond in
    let proc1 =
      { proc with
        proc_locals = locals;
        proc_body = body1;
        proc_precond = precond1;
        proc_postcond = postcond1;
      }
    in
    elem_sorts, IdMap.add proc.proc_name proc1 procs
  in
  let compile_pred (elem_sorts, preds) pred =
    let elem_sorts =
      IdMap.fold
        (fun id decl elem_sorts ->
          match decl.var_sort with
          | Loc (Array srt)
          | Loc (ArrayCell srt) -> SortSet.add srt elem_sorts
          | _ -> elem_sorts)
        pred.pred_locals elem_sorts
    in
    let body = compile_spec pred.pred_body in
    let pred1 = { pred with pred_body = body } in
    elem_sorts, IdMap.add pred.pred_name pred1 preds
  in
  let elem_sorts, procs = fold_procs compile_proc (SortSet.empty, IdMap.empty) prog in
  let elem_sorts, preds = fold_preds compile_pred (elem_sorts, IdMap.empty) prog in
  let globals =
    SortSet.fold (fun srt globals ->
      let asdecl = array_state_decl srt in
      IdMap.add asdecl.var_name asdecl globals)
      elem_sorts prog.prog_vars
  in
  { prog with
      prog_procs = procs;
      prog_preds = preds;
      prog_vars = globals;
  }
    
(** Desugare SL specification to FOL specifications. 
 ** Assumes that loops have been transformed to tail-recursive procedures. *)
let elim_sl prog =
  let pred_to_form p args domains = 
    let decl = find_pred prog p in
    let _, fps, _ =
      Util.map2_remainder (fun _ _ -> ()) args decl.pred_formals
    in
    let mk_empty_except ssrts =
      SortMap.fold
        (fun ssrt dom eqs ->
          if List.mem ssrt ssrts then eqs
          else mk_eq dom (mk_empty (Set (Loc ssrt))) :: eqs)
        domains []
    in
    match fps with
    | [] ->
        let fp_args, ssrts =
          Util.map_split (fun id ->
            let fp_decl = IdMap.find id decl.pred_locals in
            let ssrt = struct_sort_of_sort (element_sort_of_sort fp_decl.var_sort) in
            SortMap.find ssrt domains, ssrt)
            decl.pred_footprints
        in
        let eqs = mk_empty_except ssrts in
        smk_and (mk_pred p (args @ fp_args) :: eqs)
    | _ ->
        let fp_eqs, ssrts =
          Util.map_split
            (fun fp ->
              let ssrt = struct_sort_of_sort (element_sort_of_set fp) in
              mk_eq fp (SortMap.find ssrt domains), ssrt)
            fps
        in
        let eqs = mk_empty_except ssrts in
        smk_and (mk_pred p args :: fp_eqs @ eqs)
  in
  (* transform the preds from SL to GRASS *)
  (*let preds =
    if !Config.predefPreds
    then fold_preds compile_pred_acc IdMap.empty prog
    else compile_preds (preds prog)
  in
  let prog = { prog with prog_preds = preds; } in *)
  let struct_srts = struct_sorts prog in
  (* declare alloc sets *)
  let prog =
    let globals_with_alloc_sets =
      SortSet.fold
        (fun ssrt acc -> IdMap.add (alloc_id ssrt) (alloc_decl ssrt) acc)
        struct_srts
        prog.prog_vars
    in
    { prog with prog_vars = globals_with_alloc_sets }
  in
  let compile_proc proc =
    (* add auxiliary set variables *)
    let new_locals, aux_formals, aux_returns = 
      SortSet.fold (fun ssrt (new_locals, aux_formals, aux_returns) ->
        let footprint_id = footprint_id ssrt in
        let footprint_caller_id = footprint_caller_id ssrt in
        let final_footprint_caller_id = final_footprint_caller_id ssrt in
        let footprint_decl = mk_loc_set_decl ssrt footprint_id proc.proc_pos in
        (footprint_id, { footprint_decl with var_is_implicit = true }) ::
        List.map (fun id -> (id, mk_loc_set_decl ssrt id proc.proc_pos)) 
          [footprint_caller_id; final_footprint_caller_id] @
        new_locals,
        footprint_caller_id :: footprint_id :: aux_formals,
        final_footprint_caller_id :: aux_returns)
        struct_srts ([], [], [])    
    in
    let locals =
      List.fold_left 
        (fun locals (id, decl) -> IdMap.add id decl locals)
        proc.proc_locals 
        new_locals
    in
    let returns = proc.proc_returns @ aux_returns in
    let formals = proc.proc_formals @ aux_formals in
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
              Some (sf.spec_name, sf.spec_msg, merge_src_pos p sf.spec_pos),
              new_kind
          | _ -> fs, aux, kind)
          sfs ([], None, Free)
      in
      let name, msg, pos = Util.Opt.get_or_else (name, None, dummy_position) aux in
      SlUtil.mk_sep_star_lst ~pos:pos fs, kind, name, msg, pos
    in
    let footprint_ids, footprint_sets =
      SortSet.fold
        (fun ssrt (ids, sets) ->
          footprint_id ssrt :: ids,
          SortMap.add ssrt (footprint_set ssrt) sets)
        struct_srts ([], SortMap.empty)
    in
    (* translate SL precondition *)
    let sl_precond, other_precond = List.partition is_sl_spec proc.proc_precond in
    let precond =
      let name = "precondition of " ^ string_of_ident proc.proc_name in
      let f, _, name, msg, pos = convert_sl_form sl_precond name in
      let f_eq_init_footprint =
        let fp_inclusions =
          SortSet.fold
            (fun ssrt fs ->
              mk_subseteq (footprint_set ssrt) (footprint_caller_set ssrt) :: fs)
            struct_srts
            []
        in
        propagate_exists (mk_and (SlToGrass.to_grass pred_to_form footprint_sets f ::
                                  fp_inclusions))
      in
      let precond = mk_spec_form (FOL f_eq_init_footprint) name msg pos in
      let fp_name = "initial footprint of " ^ string_of_ident proc.proc_name in
      let null_not_in_alloc =
        SortSet.fold
          (fun ssrt fs -> mk_not (mk_elem (mk_null ssrt) (alloc_set ssrt)) :: fs)
          struct_srts
          []
      in
      let footprint_caller_in_alloc =
        SortSet.fold
          (fun ssrt fs -> mk_subseteq (footprint_caller_set ssrt) (alloc_set ssrt) :: fs)
          struct_srts
          []
      in
      let free_preconds =
        List.map (fun f -> mk_free_spec_form (FOL f) fp_name None pos)
          (footprint_caller_in_alloc @ null_not_in_alloc)
      in
      (* additional precondition for tail-recursive procedures *)
      let tailrec_precond =
        if not proc.proc_is_tailrec then [] else
        let first_iter_id = List.hd formals in
        let error_msg = ProgError.mk_error_info "Memory footprint at error location does not match this specification" in
        let msg caller =
          if caller <> proc.proc_name then
            "An invariant might not hold before entering this loop",
            ProgError.mk_error_info "This is the loop invariant that might not hold initially"
          else 
            "An invariant might not be maintained by this loop",
            ProgError.mk_error_info "This is the loop invariant that might not be maintained"
        in
        SortSet.fold (fun ssrt fs ->
          let f = mk_or [mk_pred first_iter_id []; 
                         mk_error_msg (pos, error_msg)
                           (mk_eq 
                              (mk_diff (footprint_caller_set ssrt) (footprint_set ssrt))
                              (mk_empty (Set (Loc ssrt))))]
          in
          mk_spec_form (FOL f) "invariant" (Some msg) pos :: fs)
          struct_srts
          []
      in
      precond :: free_preconds @ tailrec_precond
    in
    (* translate SL postcondition *)
    let init_alloc_set ssrt = oldify_term (IdSet.singleton (alloc_id ssrt)) (alloc_set ssrt) in
    let init_footprint_caller_set ssrt = footprint_caller_set ssrt in
    let init_footprint_set ssrt = footprint_set ssrt in
    let final_footprint_set ssrt =
      mk_union [mk_inter [alloc_set ssrt; init_footprint_set ssrt];
                mk_diff (alloc_set ssrt) (init_alloc_set ssrt)]
    in
    let final_alloc_set ssrt =
      mk_union [mk_diff (init_alloc_set ssrt) (init_footprint_caller_set ssrt);
                (final_footprint_caller_set ssrt)]
    in
    let sl_postcond, other_postcond = List.partition is_sl_spec proc.proc_postcond in
    let postcond, post_pos =
      let name = "postcondition of " ^ string_of_ident proc.proc_name in
      let f, kind, name, msg, pos = convert_sl_form sl_postcond name in
      let final_footprint_sets =
        SortSet.fold (fun ssrt sets -> SortMap.add ssrt (final_footprint_set ssrt) sets) struct_srts SortMap.empty
      in
      let f_eq_final_footprint = 
        SlToGrass.to_grass pred_to_form final_footprint_sets f 
      in
      let final_footprint_postcond =
        mk_spec_form (FOL f_eq_final_footprint) name msg pos
      in
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
      let final_footprint_caller_postconds = 
        SortSet.fold (fun ssrt fs ->
          let f =
            mk_eq (final_footprint_caller_set ssrt)
              (mk_union [mk_diff (init_footprint_caller_set ssrt) (init_footprint_set ssrt);
                         (final_footprint_set ssrt)])
          in
          mk_framecond f :: fs)
          struct_srts []
      in
      (* null is not allocated *)
      let final_null_alloc =
        SortSet.fold (fun ssrt fs ->
          mk_framecond (mk_and [mk_eq (alloc_set ssrt) (final_alloc_set ssrt); 
                                mk_not (smk_elem (mk_null ssrt) (alloc_set ssrt))]) :: fs)
          struct_srts []
      in
      (* frame axioms for modified fields *)
      let all_fields =
        List.fold_left
          (fun acc var ->
            match var.var_sort with
            | Map (Loc _, _) as srt -> IdMap.add var.var_name srt acc 
            | _ -> acc
          )
          IdMap.empty
          (vars prog)
      in
      let frame_preds =
        IdMap.fold
          (fun fld srt frames ->
            if !Config.opt_field_mod && not (IdSet.mem fld (modifies_proc prog proc))
            then frames else
            let old_fld = oldify fld in
            let ssrt = struct_sort_of_sort (dom_sort srt) in
            mk_framecond (mk_frame (init_footprint_set ssrt) (init_alloc_set ssrt)
                             (mk_free_const srt old_fld)
                             (mk_free_const srt fld)) ::
            frames
          )
          all_fields
          []
      in
      final_footprint_caller_postconds @ final_null_alloc @ frame_preds
    in
    (* update all procedure calls and return commands in body *)
    let rec compile_stmt = function
      | (Call cc, pp) ->
          mk_call_cmd ~prog:(Some prog) 
            (cc.call_lhs @ footprint_ids) 
            cc.call_name 
            (cc.call_args @ SortMap.fold (fun _ s sets -> s :: sets) footprint_sets []) 
            pp.pp_pos
      | (Return rc, pp) ->
          let fp_returns =
            SortSet.fold (fun ssrt fp_returns ->
              mk_union [footprint_caller_set ssrt; footprint_set ssrt] :: fp_returns)
              struct_srts []
          in
          let rc1 = { return_args = rc.return_args @ fp_returns } in
          Basic (Return rc1, pp)
      | (Assume sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = SlToGrass.to_grass pred_to_form footprint_sets f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assume_cmd sf1 pp.pp_pos
          | FOL f -> Basic (Assume sf, pp))
      | (Assert sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = SlToGrass.to_grass pred_to_form footprint_sets f in
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
          let assign_init_footprints_caller =
            let new_footprint_caller_set ssrt =
              mk_diff (footprint_caller_set ssrt) (footprint_set ssrt)
            in
            SortSet.fold
              (fun ssrt cmds ->
                mk_assign_cmd 
                  [footprint_caller_id ssrt] 
                  [new_footprint_caller_set ssrt] 
                  body_pp.pp_pos :: cmds)
              struct_srts []
          in
          let assign_final_footprints_caller =
            SortSet.fold
              (fun ssrt cmds ->
                mk_assign_cmd 
                  [final_footprint_caller_id ssrt] 
                  [mk_union [footprint_caller_set ssrt; footprint_set ssrt]]
                  body_pp.pp_pos :: cmds)
              struct_srts []
          in
          mk_seq_cmd 
            (assign_init_footprints_caller @ [body1] @ assign_final_footprints_caller)
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
      proc_precond = precond @ other_precond;
      proc_postcond = postcond @ framecond @ other_postcond;
      proc_body = body;
    } 
  in
  add_ghost_field_invariants (map_procs compile_proc prog)

(** Annotate safety checks for heap accesses *)
let annotate_heap_checks prog =
  let rec derefs acc = function
    | App (Read, [map; idx], _) ->
        let acc1 =
          match sort_of map with
          | Map (Loc _, _) -> TermSet.add idx acc
          | _ -> acc
        in
        derefs (derefs acc1 map) idx
    | App (Length, [map], _) -> TermSet.add map acc
    | App (ArrayCells, [map], _) -> TermSet.add map acc
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
        let ssrt = struct_sort_of_sort (sort_of t) in
        let t_in_footprint = FOL (mk_elem t (footprint_set ssrt)) in
        let mk_msg callee = "Possible invalid heap access", "Possible invalid heap access" in
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
        let ssrt = struct_sort_of_sort (sort_of arg) in
        let arg_in_footprint = FOL (mk_elem arg (footprint_set ssrt)) in
        let mk_msg callee = "This deallocation might be unsafe", "This deallocation might be unsafe" in
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
          | Loc ssrt ->          
              let new_loc = mk_and [mk_not (mk_elem arg (alloc_set ssrt)); mk_neq arg (mk_null ssrt)] in
              let sf = mk_spec_form (FOL new_loc) "new" None pp.pp_pos in
              let assume_fresh = mk_assume_cmd sf pp.pp_pos in
              let assign_alloc = 
                mk_assign_cmd 
                  [alloc_id ssrt] 
                  [mk_union [alloc_set ssrt; mk_setenum [arg]]] 
                  pp.pp_pos 
              in
              let assign_footprint = 
                mk_assign_cmd 
                  [footprint_id ssrt] 
                  [mk_union [footprint_set ssrt; mk_setenum [arg]]]
                  pp.pp_pos 
              in
              let array_aux =
                match ssrt with
                | Array srt ->
                    let length = List.hd nc.new_args in
                    let length_ok =
                      mk_spec_form (FOL (mk_eq (mk_length arg) length)) "new" None pp.pp_pos
                    in
                    let assume_length_ok = mk_assume_cmd length_ok pp.pp_pos in
                    let l = Axioms.loc1 (ArrayCell srt) in
                    let assume_cells_fresh =
                      let cells_fresh =
                        Axioms.mk_axiom "new_array_cells_fresh"
                          (mk_sequent
                             [mk_leq (mk_int 0) (mk_index_of_cell l);
                              mk_lt (mk_index_of_cell l) length;
                              mk_eq (mk_array_of_cell l) arg]
                             [mk_and [mk_not (mk_elem l (alloc_set (ArrayCell srt)));
                                      mk_neq l (mk_null (ArrayCell srt))]])
                      in
                      let sf = mk_spec_form (FOL cells_fresh) "new" None pp.pp_pos in
                      mk_assume_cmd sf pp.pp_pos
                    in
                    let update_set set_id set =
                      let assign_tmp_cells =
                        mk_assign_cmd [tmp_array_cell_set_id srt] [set] pp.pp_pos
                      in
                      let havoc_set =
                        mk_havoc_cmd [set_id] pp.pp_pos
                      in
                      let assume_set =
                        let f =
                          Axioms.mk_axiom "new_array_cells_alloc"
                            (mk_iff (mk_elem l set)
                               (mk_or [mk_elem l (tmp_array_cell_set srt);
                                       mk_and [mk_leq (mk_int 0) (mk_index_of_cell l);
                                               mk_lt (mk_index_of_cell l) length;
                                               mk_eq (mk_array_of_cell l) arg]]))
                        in
                        let sf = mk_spec_form (FOL f) "new" None pp.pp_pos in
                        mk_assume_cmd sf pp.pp_pos
                      in
                      [assign_tmp_cells; havoc_set; assume_set]
                    in
                    [assume_length_ok; assume_cells_fresh] @
                    update_set (alloc_id (ArrayCell srt)) (alloc_set (ArrayCell srt)) @
                    update_set (footprint_id (ArrayCell srt)) (footprint_set (ArrayCell srt))
                | _ -> []
              in
              [assume_fresh; assign_alloc; assign_footprint] @ array_aux
          | _ -> []
        in
        mk_seq_cmd (havoc :: aux) pp.pp_pos
    | (Dispose dc, pp) ->
        let arg = dc.dispose_arg in
        let ssrt = struct_sort_of_sort (sort_of arg) in
        let assign_alloc = 
          mk_assign_cmd 
            [alloc_id ssrt] 
            [mk_diff (alloc_set ssrt) (mk_setenum [arg])]
            pp.pp_pos 
        in
        let assign_footprint = 
          mk_assign_cmd 
            [footprint_id ssrt] 
            [mk_diff (footprint_set ssrt) (mk_setenum [arg])] 
            pp.pp_pos 
        in
        let array_aux =
          match ssrt with
          | Array srt ->
              let update_set set_id set =
                let assign_tmp_cells =
                  mk_assign_cmd [tmp_array_cell_set_id srt] [set] pp.pp_pos
                in
                let havoc_set =
                  mk_havoc_cmd [set_id] pp.pp_pos
                in
                let l = Axioms.loc1 (ArrayCell srt) in
                let assume_set =
                  let f =
                    Axioms.mk_axiom "free_array_cells_alloc"
                      (mk_iff (mk_elem l set)
                         (mk_and [mk_elem l (tmp_array_cell_set srt);
                                  mk_neq (mk_array_of_cell l) arg]))
                  in
                  let sf = mk_spec_form (FOL f) "free" None pp.pp_pos in
                  mk_assume_cmd sf pp.pp_pos
                in
                [assign_tmp_cells; havoc_set; assume_set]
              in
              update_set (alloc_id (ArrayCell srt)) (alloc_set (ArrayCell srt)) @
              update_set (footprint_id (ArrayCell srt)) (footprint_set (ArrayCell srt))
          | _ -> []
        in
        mk_seq_cmd ([assign_alloc; assign_footprint] @ array_aux) pp.pp_pos
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc = 
    { proc with proc_body = Util.Opt.map (map_basic_cmds elim) proc.proc_body } 
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }
