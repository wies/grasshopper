(** Translation of program with SL specifications to a pure GRASS program *)

open Form
open FormUtil
open Prog
open AuxNames
open Reachify

(** Desugare SL specification to FOL specifications. 
 ** Assumes that loops have been transformed to tail-recursive procedures. *)
let elim_sl prog =
  (* keep the original names around to generate the self framing predicates *)
  let original_preds_id = List.map (fun p -> p.pred_name) (preds prog) in
  let original_preds_with_args =
    let formula = Util.flat_map (fun p -> p.proc_precond @ p.proc_postcond) (procs prog) in
    let preds_set =
      List.fold_left
        (fun acc s -> match s.spec_form with FOL _ -> acc | SL f -> Sl.SlSet.union acc (SlUtil.preds_full f))
        Sl.SlSet.empty
        formula
    in
      Sl.SlSet.fold
        (fun p acc -> match p with
          | Sl.Atom (Sl.Pred id, args) ->
            let old = try IdMap.find id acc with Not_found -> [] in
              IdMap.add id (args :: old) acc
          | _ -> failwith "expected Sl.Pred")
        preds_set
        IdMap.empty
  in
  (* transform the preds from SL to GRASS *)
  let preds =
    if !Config.predefPreds
    then fold_preds compile_pred_acc IdMap.empty prog
    else compile_preds (preds prog)
  in
  let prog = { prog with prog_preds = preds; } in  
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
      let name, msg, pos = Util.safe_unopt (name, None, dummy_position) aux in
      SlUtil.mk_sep_star_lst fs, kind, name, msg, pos
    in
    (* translate SL precondition *)
    let sl_precond, other_precond = List.partition is_sl_spec proc.proc_precond in
    let precond, free_precond =
      let name = "precondition of " ^ str_of_ident proc.proc_name in
      let f, _, name, msg, pos = convert_sl_form sl_precond name in
      let f_eq_init_footprint =  
        propagate_exists (mk_and [ToGrass.to_grass pred_to_form footprint_set f; 
                                  mk_subseteq footprint_set footprint_caller_set])
      in
      let precond = mk_spec_form (FOL f_eq_init_footprint) name msg pos in
      let fp_name = "initial footprint of " ^ str_of_ident proc.proc_name in
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
    let sl_postcond, other_postcond = List.partition is_sl_spec proc.proc_postcond in
    let postcond, post_pos =
      let name = "postcondition of " ^ str_of_ident proc.proc_name in
      let f, kind, name, msg, pos = convert_sl_form sl_postcond name in
      let f_eq_final_footprint = 
        ToGrass.to_grass pred_to_form final_footprint_set f 
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
      let name = "framecondition of " ^ (str_of_ident proc.proc_name) in
      let mk_framecond f = mk_free_spec_form (FOL f) name None post_pos in
      (* final caller footprint is frame with final footprint *)
      let final_footprint_caller_postcond = 
        mk_eq final_footprint_caller_set 
          (mk_union [mk_diff init_footprint_caller_set init_footprint_set;
                     final_footprint_set])
      in
      mk_framecond final_footprint_caller_postcond ::
      (* null is not allocated *)
      mk_framecond (mk_and [mk_subseteq final_footprint_caller_set alloc_set; 
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
      let mod_fields =
        IdSet.inter
          all_fields 
          (modifies_proc prog proc)
      in
      let frame_preds =
        IdSet.fold
          (fun var frames ->
            let old_var = 
              if IdSet.mem var mod_fields then oldify var
              else var
            in
            let srt = (find_global prog var).var_sort in
            mk_framecond (mk_frame init_footprint_set init_alloc_set 
                             (mk_free_const ~srt:srt old_var)
                             (mk_free_const ~srt:srt var)) ::
            frames
          )
          all_fields
          []
      in
      let mk_self_framing def =
        (* args occuring in the rest of the program *)
        let args_at_pos idx =
          let args =
            try IdMap.find def.Symbols.sym_name original_preds_with_args
            with Not_found -> []
          in
          let lst = List.map (fun l -> List.nth l idx) args in
            List.fold_left (fun acc t -> TermSet.add t acc) TermSet.empty lst
        in
        let fld_at_pos idx =
          let args = args_at_pos idx in
            TermSet.fold
              (fun t acc -> match t with
                | App (FreeSym id, [], Some (Fld _)) -> t :: acc
                | _ -> acc) 
              args
              []
        in
        (* generate args for the pred:
           -add domain (universally quantified set)
           -pick the fields from the set of field seen in the rest of the program
           -for the other arguments use universally quantified variables *)
        let dom = mk_var ~srt:(Set Loc) (mk_ident "dom") in
        let rec mk_ags idx lst = match lst with
          | (id, tpe) :: xs ->
            begin
              let sub = mk_ags (idx + 1) xs in
              let top = match tpe with
                | Fld _ -> fld_at_pos idx
                | tpe -> [mk_var ~srt:tpe (fresh_ident "?a")]
              in
                Util.flat_map (fun lst -> List.map (fun t -> t :: lst) top) sub
            end
          | [] -> [[]]
        in
        let all_args = List.map (fun lst -> dom :: lst) (mk_ags 0 (List.tl def.Symbols.parameters)) in
        (* make the self framing axioms *)
        let mk_sf args =
          let oldified_args = List.map (fun t -> match t with App (FreeSym id, [], s) when IdSet.mem id mod_fields -> App (FreeSym (oldify id), [], s) | _ -> t) args in
          let dom = List.hd args in
          let in_frame = mk_eq (mk_inter [dom; init_footprint_set]) (mk_empty (Some (Set Loc))) in
          let preds_old, dom_old = pred_to_form (def.Symbols.sym_name) (List.tl oldified_args) dom in
          let preds_new, dom_new = pred_to_form (def.Symbols.sym_name) (List.tl args) dom in
          let qf = mk_implies (smk_and (in_frame :: preds_old :: dom_old)) (smk_and (preds_new :: dom_new)) in
          let q = mk_comment "self_framing" (Axioms.mk_axiom2 qf) in
            mk_framecond q
        in
          List.map mk_sf all_args
      in
      let self_framing =
        (* collect SL definition of the predicates *)
        let defs = List.map Symbols.get_symbol original_preds_id in
        (* filter out the preds with empty footprint (treeAllocInvariant) *)
        let defs =
          List.filter 
            (fun def ->
              let dom_out = snd (List.hd def.Symbols.outputs) in
                not (TermSet.mem (mk_empty (Some (Set Loc))) (ground_terms dom_out)))
            defs
        in
          if !Config.optSelfFrame then
            Util.flat_map mk_self_framing defs
          else
            []
      in
      frame_preds @ self_framing
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
              let f1 = ToGrass.to_grass pred_to_form footprint_set f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assume_cmd sf1 pp.pp_pos
          | FOL f -> Basic (Assume sf, pp))
      | (Assert sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 = ToGrass.to_grass pred_to_form footprint_set f in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assert_cmd sf1 pp.pp_pos
          | FOL f -> Basic (Assert sf, pp))
      | (c, pp) -> Basic (c, pp)
    in
    let body = 
      Util.optmap 
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
        let t_in_footprint = FOL (mk_elem t footprint_set) in
        let mk_msg callee pos = "Possible heap access through null or dangling reference" in
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
        let mk_msg callee pos = "This deallocation might be unsafe" in
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
    { proc with proc_body = Util.optmap (map_basic_cmds annotate) proc.proc_body } 
  in
  { prog with prog_procs = IdMap.map annotate_proc prog.prog_procs; }

(** Eliminate all new and dispose commands.
 ** Assumes that footprint sets have been introduced. *)
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
    { proc with proc_body = Util.optmap (map_basic_cmds elim) proc.proc_body } 
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }
