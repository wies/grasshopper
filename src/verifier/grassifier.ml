(** {5 Translation of program with SL specifications to a pure GRASS program} *)

open Grass
open GrassUtil
open Prog
open Util

(** Auxiliary variables for desugaring SL specifications *)
let footprint_id = mk_name_generator "FP"
let footprint_set struct_srt = mk_loc_set struct_srt (footprint_id struct_srt)

let footprint_caller_id = mk_name_generator "FP_Caller"
let footprint_caller_set struct_srt = mk_loc_set struct_srt (footprint_caller_id struct_srt)

let final_footprint_caller_id = mk_name_generator "FP_Caller_final"
let final_footprint_caller_set struct_srt = mk_loc_set struct_srt (final_footprint_caller_id struct_srt)

(** Auxiliary variables for desugaring arrays *)

let array_state_srt simple srt =
  if simple
  then Map ([Loc (Array srt); Int], srt)
  else Map ([Loc (ArrayCell srt)], srt)
let array_state_id = mk_name_generator "array_state"
let array_state simple srt =
  mk_free_const (array_state_srt simple srt) (array_state_id srt)
let array_state_decl simple srt =
  let id = array_state_id srt in
  { var_name = id;
    var_orig_name = name id;
    var_sort = array_state_srt simple srt;
    var_is_ghost = false;
    var_is_implicit = false;
    var_is_aux = true;
    var_pos = dummy_position;
    var_scope = global_scope
  }

let tmp_array_cell_set_id =
  let gen = mk_name_generator "tmp" in
  fun srt -> gen (ArrayCell srt) 
let tmp_array_cell_set_decl srt =
  mk_loc_set_decl (ArrayCell srt) (tmp_array_cell_set_id srt) dummy_position
let tmp_array_cell_set srt =
  mk_free_const (Set (Loc (ArrayCell srt))) (tmp_array_cell_set_id srt)
    
(** Add reachability invariants for ghost fields of sort Loc *)
let add_ghost_field_invariants prog =
  let ghost_loc_fields =
    List.filter 
      (fun decl ->
        match decl.var_sort with
        | Map ([Loc id1], Loc id2) -> id1 = id2 && decl.var_is_ghost
        | _ -> false)
      (Prog.vars prog)
  in
  let mk_inv_pred (preds, pred_map, alloc_ids) decl =
    let open Axioms in
    let struct_srt = struct_sort_of_sort (List.hd (dom_sort decl.var_sort)) in
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
                  [mk_eq loc1 loc2; mk_and [mk_elem loc1 alloc_set;
                                            mk_elem loc2 alloc_set];
                   mk_eq loc2 null]));
          ]
    in
    let pred_id = fresh_ident "ghost_field_invariant" in
    let name = "ghost field invariant for " ^ string_of_ident decl.var_name in
    let pred_term = mk_free_app Bool pred_id [fld; alloc_set] in
    let gen = TermGenerator ([Match (pred_term, [])], [mk_known pred_term]) in
    let body = mk_spec_form (FOL (annotate body_form [gen])) name None (decl.var_pos) in
    let contract =
      { contr_name = pred_id;
        contr_formals = [decl.var_name; alloc_id];
        contr_returns = []; 
        contr_locals = IdMap.add decl.var_name decl locals;
        contr_precond = [];
        contr_postcond = [];
        contr_footprint_sorts = SortSet.empty;
        contr_pos = decl.var_pos;
      }
    in
    let pred = 
      { pred_contract = contract;  
        pred_body = Some body;
        pred_accesses = IdSet.empty;
        pred_is_self_framing = false;
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
      let struct_srt = struct_sort_of_sort (List.hd (dom_sort decl.var_sort)) in
      let inv = mk_pred pred_id [fld; alloc_set struct_srt] in
      let name = "ghost field invariant for " ^ string_of_ident decl.var_name in
      mk_spec_form (FOL inv) name None decl.var_pos
    in 
    let pre_invs = List.map mk_inv accessed in
    let post_invs = List.map mk_inv modified in
    let contract =
      { proc.proc_contract with
        contr_precond = pre_invs @ precond_of_proc proc; 
        contr_postcond = post_invs @ postcond_of_proc proc;
      }
    in
    { proc with
      proc_contract = contract;
    }
  in
  let prog1 = List.fold_left declare_pred prog preds in
  map_procs add_invs prog1

(** Desugare arrays. *)
let elim_arrays prog =
  let simple = !Config.simple_arrays in
  let rec compile_term = function
    | Var (id, srt) -> Var (id, srt)
    | App (Read, [map; idx], _) ->
        let map1 = compile_term map in
        let idx1 = compile_term idx in
        (match sort_of map with
        | Loc (Array srt) when not simple ->
            let cell = match map1, idx1 with
            | App (ArrayOfCell, [c1], _), App (IndexOfCell, [c2], _) when c1 = c2 -> c1
            | _ -> mk_read (mk_array_cells map1) [idx1]
            in
            mk_read (array_state simple srt) [cell]
        | Loc (Array srt) ->
            mk_read (array_state simple srt) [map; idx]
        | _ -> mk_read map1 [idx1])
    | App (sym, ts, srt) ->
        let ts1 = List.map compile_term ts in
        App (sym, ts1, srt)
  in
  let compile_annot =
    function
    | TermGenerator (gs, ts) ->
        let gs1 = List.map (function Match (t, f) -> Match (compile_term t, f)) gs in
        TermGenerator (gs1, List.map compile_term ts)
    | a -> a
  in
  let rec compile_grass_form = function
    | Atom (t, ann) ->
        Atom (compile_term t, List.map compile_annot ann)
    | BoolOp (op, fs) ->
        BoolOp (op, List.map compile_grass_form fs)
    | Binder (b, vs, f, ann) ->
        Binder (b, vs, compile_grass_form f, List.map compile_annot ann)
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
        let inv =
          List.map (Prog.map_spec_form compile_grass_form compile_sl_form) lc.loop_inv
        in
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
                let idx =
                  if simple then [map1; idx1]
                  else [mk_read (mk_array_cells map1) [idx1]]
                in
                array_state_id srt :: lhs1,
                mk_write (array_state simple srt) idx upd1 :: rhs1,
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
    let all_locals =
      prog.prog_vars ::
      List.map (fun proc -> locals_of_proc proc) (find_proc_with_deps prog (name_of_proc proc))
    in
    let locals, elem_sorts =
      let rec process_sort (locals, elem_sorts) = function
        | Loc (Array srt)
        | Loc (ArrayCell srt) ->
            let tmp_decl = tmp_array_cell_set_decl srt in
            let locals1 = IdMap.add tmp_decl.var_name tmp_decl locals in
            let elem_sorts1 = SortSet.add srt elem_sorts in
            process_sort (locals1, elem_sorts1) srt
        | Set srt
        | Loc srt -> process_sort (locals, elem_sorts) srt
        | Map (dsrts, rsrt) ->
            List.fold_left process_sort (locals, elem_sorts) (rsrt :: dsrts)
        | _ -> locals, elem_sorts
      in
      List.fold_left
        (fun (locals, elem_sorts) vars ->
          IdMap.fold
            (fun id decl acc -> process_sort acc decl.var_sort)
            vars (locals, elem_sorts))
        (locals_of_proc proc, elem_sorts) all_locals
    in
    let body1 = Util.Opt.map compile_cmd proc.proc_body in
    let precond1 = List.map compile_spec (precond_of_proc proc) in
    let postcond1 = List.map compile_spec (postcond_of_proc proc) in
    let contract1 =
      { proc.proc_contract with
        contr_locals = locals;
        contr_precond = precond1;
        contr_postcond = postcond1;
     }
    in
    let proc1 =
      { proc with
        proc_contract = contract1;
        proc_body = body1;
      }
    in
    elem_sorts, IdMap.add (name_of_proc proc) proc1 procs
  in
  let compile_pred (elem_sorts, preds) pred =
    let elem_sorts =
      IdMap.fold
        (fun id decl elem_sorts ->
          match decl.var_sort with
          | Loc (Array srt)
          | Loc (ArrayCell srt) -> SortSet.add srt elem_sorts
          | _ -> elem_sorts)
        (locals_of_pred pred) elem_sorts
    in
    let body = Util.Opt.map compile_spec pred.pred_body in
    let precond1 = List.map compile_spec (precond_of_pred pred) in
    let postcond1 = List.map compile_spec (postcond_of_pred pred) in
    let contract1 =
      { pred.pred_contract with
        contr_precond = precond1;
        contr_postcond = postcond1;
     }
    in
    let pred1 =
      { pred with
        pred_contract = contract1;
        pred_body = body          
      }
    in
    elem_sorts, IdMap.add (name_of_pred pred) pred1 preds
  in
  let elem_sorts, procs = fold_procs compile_proc (SortSet.empty, IdMap.empty) prog in
  let elem_sorts, preds = fold_preds compile_pred (elem_sorts, IdMap.empty) prog in
  let globals =
    SortSet.fold (fun srt globals ->
      let asdecl = array_state_decl simple srt in
      IdMap.add asdecl.var_name asdecl globals)
      elem_sorts prog.prog_vars
  in
  { prog with
    prog_procs = procs;
    prog_preds = preds;
    prog_vars = globals;
  }

(** Add frame axioms for framed predicates and functions *)
(*
let annotate_frame_axioms prog =
  let process_pred frame_axioms pred =
    let find_decl id = IdMap.find id (locals_of_pred pred) in
    let footprints =
      List.fold_left (fun footprints id ->
        let decl = find_decl id in
        let struct_srt = struct_sort_of_sort (element_sort_of_sort decl.var_sort) in
        SortMap.add decl.var_sort
          (mk_var decl.var_sort id,
           mk_var decl.var_sort (alloc_id (struct_srt)),
           mk_var decl.var_sort (footprint_id (struct_srt)))
          footprints)
        SortMap.empty pred.pred_footprints (* XXX pred_footprints is no more ... *)
    in
    let res_srt = Prog.result_sort_of_pred pred in
    let old_args =
      List.map (fun id ->
        let decl = find_decl id in
        mk_var decl.var_sort id)
        ((formals_of_pred pred) @ pred.pred_footprints) (* XXX pred_footprints is no more ... *)
    in
    let old_pred = mk_free_app res_srt pred.pred_name old_args in
    let footprints =
      if pred.pred_is_self_framing
      then
        let struct_srt = struct_sort_of_sort (element_sort_of_sort res_srt) in
        SortMap.add res_srt
          (old_pred,
           mk_var res_srt (alloc_id (struct_srt)),
           mk_var res_srt (footprint_id (struct_srt)))
          footprints
      else footprints
    in
    let loc_fields =
      List.fold_left (fun loc_fields id1 ->
        let decl = IdMap.find id1 pred.pred_locals in
        match decl.var_sort with
        | Map (Loc dsrt, rsrt) ->
            if SortMap.mem (Set (Loc dsrt)) footprints then
              let id2 = fresh_ident (name id1) in 
              IdMap.add id1 (id2, Loc dsrt, rsrt) loc_fields
            else loc_fields
        | _ -> loc_fields)
        IdMap.empty (formals_of_pred pred)
    in
    let new_args =
      List.map (fun id ->
        try
          let id2, srt1, srt2 = IdMap.find id loc_fields in
          mk_var (Map (srt1, srt2)) id2
        with Not_found ->
          let decl = IdMap.find id (locals_of_pred pred) in
          mk_var decl.var_sort id)
        ((formals_of_pred pred) @ pred.pred_footprints) (* XXX pred_footprints is no more ... *)
    in
    let new_pred = mk_free_app res_srt pred.pred_name new_args in
    let frame_pred_terms =
      IdMap.fold (fun id1 (id2, srt1, srt2) frame_preds ->
        let map_srt = Map (srt1, srt2) in
        let _, a, fp = SortMap.find (Set srt1) footprints in
        mk_app Bool Frame [fp; a; mk_var map_srt id1; mk_var map_srt id2] :: frame_preds)
        loc_fields []
    in
    let frame_preds = List.map (fun t -> Atom (t, [])) frame_pred_terms in
    let guards =
      SortMap.fold (fun _ (fr, a, fp) guards ->
        mk_subseteq fr a :: mk_disjoint fr fp :: guards)
        footprints frame_preds
    in
    let name = "frame of " ^ string_of_ident (name_of_pred pred) in
    let pred_frames =
      let generators =
        let match_frame_preds =
          List.map (fun t -> Match (t, [])) frame_pred_terms
        in
        [(match_frame_preds @ [Match (new_pred, [])], [old_pred]);
         (match_frame_preds @ [Match (old_pred, [])], [new_pred])]
      in
      let frame =
        let f =
          List.fold_left (fun f t -> mk_pattern t [] f)
            (mk_sequent guards [mk_eq old_pred new_pred])
            frame_pred_terms
        in
        Axioms.mk_axiom ~gen:generators name f
      in
      let write_frames =
        (*IdMap.fold (fun id1 (id2, srt1, srt2) write_frames ->
          let dvar = mk_var srt2 Axioms.d in
          let lvar = Axioms.loc1 (struct_sort_of_sort srt1) in
          let fld1 = mk_var (Map (srt1, srt2)) id1 in
          let fld2 = mk_write fld1 lvar dvar in
          let fr, _, _ = SortMap.find (Set srt1) footprints in
          let sm = IdMap.add id1 fld2 IdMap.empty in
          let new_pred = subst_term sm old_pred in
          let f = mk_or [mk_elem lvar fr; mk_eq old_pred new_pred] in
          let generators =
            [[Match (fld2, []); Match (new_pred, [])], [old_pred];
             [Match (fld2, []); Match (old_pred, [])], [new_pred]]
          in
          (*Axioms.mk_axiom ~gen:generators name (mk_pattern old_pred [] f) ::*) write_frames)
          loc_fields*) []
      in
      List.map (fun axiom -> mk_free_spec_form (FOL axiom) name None pred.pred_pos)
        (frame :: write_frames)
    in
    match frame_pred_terms with
    | [] -> frame_axioms
    | _ -> pred_frames @ frame_axioms
  in
  let frame_axioms =
    Prog.fold_preds process_pred [] prog
  in
  { prog with prog_axioms = frame_axioms @ prog.prog_axioms }
*)
let fp_func_id_of_pred_id pname sort = mk_ident @@ (fst pname) ^ "_fp_" ^ (string_of_sort sort)
let is_fp_func_id pname (str, _) = Str.string_match (Str.regexp @@ (fst pname) ^ "_fp_.*") str 0 
  
(** Desugare SL specification to FOL specifications. 
 ** Assumes that loops have been transformed to tail-recursive procedures. *)
let elim_sl prog =
  (*let footprint_ids fps =
    SortSet.fold (fun srt acc -> footprint_id (Set srt) :: acc) fps []
  in*)
  let prepare_sl_form sfs name =
    let fs, aux, kind_opt = 
      List.fold_right (fun sf (fs, aux, kind) -> 
        let new_kind = 
          match kind with
          | Some Checked -> Some Checked
          | _ -> Some (sf.spec_kind)
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
        sfs ([], None, None)
    in
    let name, msg, pos = Util.Opt.get_or_else (name, None, dummy_position) aux in
    let kind = Util.Opt.get_or_else Checked kind_opt in
    SlUtil.mk_sep_star_lst ~pos:pos fs, kind, name, msg, pos
  in
  let is_pure_spec sf =
    match sf.spec_form with
    | FOL _ | SL (Sl.Pure _) -> true
    | _ -> false
  in
  let is_sl_pred pred =
    not (Opt.get_or_else true (Opt.map is_pure_spec pred.pred_body))
  in
  let is_pure_pred pred =
    List.for_all is_pure_spec (Opt.to_list pred.pred_body @ precond_of_pred pred)
  in
  let pred_to_form fp_context p args domains = 
    let decl = find_pred prog p in
    let mk_empty_except ssrts =
      SortMap.fold
        (fun ssrt dom eqs ->
          if SortSet.mem ssrt ssrts then eqs
          else mk_eq dom (mk_empty (Set (Loc ssrt))) :: eqs)
        domains []
    in
    let footprint_sorts = footprint_sorts_pred decl in
    let fp_caller_args, fp_args =
      SortSet.fold (fun ssrt (fp_caller_args, fp_args) ->
        try
          SortMap.find ssrt fp_context :: fp_caller_args,
          SortMap.find ssrt domains :: fp_args
        with Not_found ->
          failwith ("Could not find footprint set for sort " ^ string_of_sort ssrt ^ " in predicate " ^ string_of_ident p))
        footprint_sorts ([], [])
    in
    let fp_args, p_footprints =
      if not (is_sl_pred decl)
      then [], SortSet.empty
      else fp_args, footprint_sorts
    in
    let eqs = mk_empty_except p_footprints in
    let fp_eqs =
      fp_args
      |> List.map (fun fp_arg ->
        let sort =
          match sort_of fp_arg with
          | Set (Loc s) -> s
          | s -> failwith @@ Printf.sprintf "FP arg %s had unexpected type %s" (string_of_term fp_arg) (string_of_sort s)
        in
        let fp_func_name = fp_func_id_of_pred_id p sort in
        let fp_func = App (FreeSym fp_func_name, args, Set (Loc sort)) in
        Atom (App (Eq, [fp_arg; fp_func], Bool), [])
      )
    in
    smk_and (mk_pred p args :: eqs @ fp_eqs)
  in
  (* post process term *)
  (*let add_footprint_args sym ts srt =
    match sym with
    | FreeSym p when IdMap.mem p prog.prog_preds ->
        let decl = find_pred prog p in
        if List.length (formals_of_pred decl) <> List.length ts
            then mk_app srt sym ts else
          let fps =
            SortSet.fold
              (fun ssrt fps -> footprint_caller_set ssrt :: fps)
              (footprint_sorts_pred decl) []
          in
          mk_app srt sym (ts @ fps) 
    | _ -> mk_app srt sym ts 
  in*)
  let post_process_term t = (*subst_funs_term add_footprint_args*) t in
  (* post process formula *)
  let post_process_form f =
    let subst_preds f = (*subst_funs add_footprint_args*) f in
    let simplify f =
      let round f =
        f |>
        propagate_exists_up |>
        mk_not |>
        nnf |>
        (*(fun f -> print_endline (" (before):"); print_form stdout f; print_newline (); f) |>*)
        foralls_to_exists |>
        (*(fun f -> print_endline (" (after):"); print_form stdout f; print_newline (); f) |>*)
        SimplifyGrass.simplify_one_sets |>
        mk_not |>
        nnf |>
        foralls_to_exists |>
        elim_old_form (var_ids prog) 
      in
      f |> round |> round |> propagate_exists_up
    in
    f |>
    subst_preds |>
    simplify
  in
  let translate_contract contr is_proc is_tailrec is_pure modifies =
    let _is_func = contr.contr_returns <> [] in
    let pos = contr.contr_pos in
    let footprint_sorts = contr.contr_footprint_sorts in
    (** For predicates, call footprint func instead of using a FP set *)
    let footprint_set ssrt =
      if is_proc then
        (* Procedures and functions still get FP sets *)
        footprint_set ssrt
      else
        begin
          let formal_vars =
            contr.contr_formals
            |> List.map (fun id -> mk_free_const (IdMap.find id contr.contr_locals).var_sort id)
          in
          mk_free_app (Set (Loc ssrt)) (fp_func_id_of_pred_id contr.contr_name ssrt) formal_vars
        end
    in
    (* add auxiliary set variables *)
    let locals, footprint_formals, footprint_caller_formals, footprint_caller_returns =
      SortSet.fold
        (fun ssrt (locals, footprint_formals, footprint_caller_formals, footprint_caller_returns) ->          
          let locals1, footprint_formals1 =
            if not is_proc then locals, footprint_formals
            else 
              let footprint_id = footprint_id ssrt in
              let footprint_decl = mk_loc_set_decl ssrt footprint_id pos in
              IdMap.add footprint_id { footprint_decl with var_is_implicit = true } locals,
              footprint_id :: footprint_formals
          in
          let locals1, footprint_caller_returns1 =
            if not is_proc || not (IdSet.mem (alloc_id ssrt) modifies)
            then locals1, footprint_caller_returns
            else
              let final_footprint_caller_id = final_footprint_caller_id ssrt in
              let final_footprint_caller_decl =
                mk_loc_set_decl ssrt final_footprint_caller_id pos
              in
              IdMap.add final_footprint_caller_id final_footprint_caller_decl locals1,
              final_footprint_caller_id :: footprint_caller_returns
          in
          let footprint_caller_id = footprint_caller_id ssrt in
          let footprint_caller_decl = mk_loc_set_decl ssrt footprint_caller_id pos in
          let locals1, footprint_caller_formals1 =
            if not is_proc
            then locals1, footprint_caller_formals
            else
              IdMap.add footprint_caller_id footprint_caller_decl locals1,
              footprint_caller_id :: footprint_caller_formals
          in
          locals1,
          footprint_formals1,
          footprint_caller_formals1,
          footprint_caller_returns1
        )
        footprint_sorts (contr.contr_locals, [], [], [])    
    in
    let aux_formals = footprint_caller_formals @ footprint_formals in
    let returns = contr.contr_returns @ footprint_caller_returns in
    let formals = contr.contr_formals @ aux_formals in
    let footprint_sets, footprint_context =
      SortSet.fold
        (fun ssrt (sets, context) ->
          SortMap.add ssrt (footprint_set ssrt) sets,
          SortMap.add ssrt (footprint_caller_set ssrt) context
        )
        footprint_sorts (SortMap.empty, SortMap.empty)
    in
    let rec split_sep pure_fs = function
      | Sl.SepOp ((Sl.SepStar | Sl.SepPlus | Sl.SepIncl), Sl.Pure (f, _), slf, _)
      | Sl.SepOp ((Sl.SepStar | Sl.SepPlus), slf, Sl.Pure (f, _), _) ->
          split_sep (f :: pure_fs) slf
      | Sl.SepOp ((Sl.SepStar | Sl.SepPlus) as op, f1, f2, pos) ->
          let pure_fs, f1 = split_sep (pure_fs) f1 in
          let pure_fs, f2 = split_sep (pure_fs) f2 in
          let mk_op = match op with
          | Sl.SepStar -> SlUtil.mk_sep_star
          | Sl.SepPlus -> SlUtil.mk_sep_plus
          | _ -> failwith "impossible"
          in
          pure_fs, mk_op f1 f2
      | Sl.Pure (f, pos) ->
          f :: pure_fs, Sl.Atom (Sl.Emp, [], pos)
      | f -> pure_fs, f
    in
    (* translate SL precondition *)
    let sl_precond, other_precond = List.partition is_sl_spec contr.contr_precond in
    let precond =
      let name = "precondition of " ^ string_of_ident contr.contr_name in
      let f, _, name, msg, pos = prepare_sl_form sl_precond name in
      let error_msg srt =
        ProgError.mk_error_info
          ("Memory footprint for type " ^ (string_of_sort srt) ^
           " does not match this specification")
      in
      let f_eq_init_footprint =
        let fp_inclusions =
          SortSet.fold
            (fun ssrt fs ->
              mk_error_msg (pos, error_msg ssrt)
                (mk_srcpos pos (mk_subseteq (footprint_set ssrt) (footprint_caller_set ssrt))) :: fs)
            footprint_sorts
            []
        in
        let sl_pure, sl_nonpure = split_sep [] f in
        sl_nonpure |>
        SlToGrass.to_grass (pred_to_form footprint_context) footprint_sets |>
        (fun f -> mk_and (f :: sl_pure @ fp_inclusions)) |>
        post_process_form
        (*|> (fun f -> print_endline (string_of_ident contr.contr_name ^ " (after):"); print_form stdout f; print_newline (); f)*)
      in
      let precond = mk_spec_form (FOL f_eq_init_footprint) name msg pos in
      let fp_name = "initial footprint of " ^ string_of_ident contr.contr_name in
      let null_not_in_alloc =
        SortSet.fold
          (fun ssrt fs -> mk_not (mk_elem (mk_null ssrt) (alloc_set ssrt)) :: fs)
          footprint_sorts
          []
      in
      let footprint_caller_in_alloc =
        SortSet.fold
          (fun ssrt fs -> mk_subseteq (footprint_caller_set ssrt) (alloc_set ssrt) :: fs)
          footprint_sorts
          []
      in
      let free_preconds =
        List.map (fun f -> mk_free_spec_form (FOL f) fp_name None pos)
          (footprint_caller_in_alloc @ null_not_in_alloc)
      in
      (* additional precondition for tail-recursive procedures *)
      let tailrec_precond =
        if not is_tailrec then [] else
        let first_iter_id = List.hd formals in
        let msg caller =
          if caller <> contr.contr_name then
            "An invariant might not hold before entering this loop",
            ProgError.mk_error_info "This is the loop invariant that might not hold initially"
          else 
            "An invariant might not be maintained by this loop",
            ProgError.mk_error_info "This is the loop invariant that might not be maintained"
        in
        SortSet.fold (fun ssrt fs ->
          let f = mk_or [mk_pred first_iter_id []; 
                         mk_error_msg (pos, error_msg ssrt)
                           (mk_srcpos pos
                              (mk_subseteq
                                 (footprint_set ssrt)
                                 (footprint_caller_set ssrt)))]
          in
          mk_spec_form (FOL f) "invariant" (Some msg) pos :: fs)
          footprint_sorts
          []
      in
      precond :: free_preconds @ tailrec_precond
    in
    let other_precond = List.map (map_spec_fol_form post_process_form) other_precond in
    (* translate SL postcondition *)
    let init_alloc_set ssrt = oldify_term (IdSet.singleton (alloc_id ssrt)) (alloc_set ssrt) in
    let init_footprint_caller_set ssrt = footprint_caller_set ssrt in
    let init_footprint_set ssrt = footprint_set ssrt in
    let final_footprint_set ssrt =
      if is_proc && IdSet.mem (alloc_id ssrt) modifies then
        mk_union [mk_inter [alloc_set ssrt; init_footprint_set ssrt];
                  mk_diff (alloc_set ssrt) (init_alloc_set ssrt)]
      else init_footprint_set ssrt
    in
    let sl_postcond, other_postcond = List.partition is_sl_spec contr.contr_postcond in
    let postcond, post_pos =
      match sl_postcond with
      | [] -> [], pos
      | _ ->
          let name = "postcondition of " ^ string_of_ident contr.contr_name in
          let f, kind, name, msg, pos = prepare_sl_form sl_postcond name in
          (*Printf.printf "%s: %d\n" (string_of_ident proc.proc_name) (List.length fs);*)
          let final_footprint_sets =
            SortSet.fold
              (fun ssrt sets -> SortMap.add ssrt (final_footprint_set ssrt) sets)
              footprint_sorts SortMap.empty
          in
          let sl_pure, sl_nonpure = split_sep [] f in
          let f_eq_final_footprint =
            sl_nonpure |>
            SlToGrass.to_grass (pred_to_form final_footprint_sets) final_footprint_sets |>
            (fun f -> mk_and (f :: sl_pure)) |>
            post_process_form
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
    let other_postcond =
      List.map
        (map_spec_fol_form (fun f -> f |> post_process_form))
        other_postcond
    in
    (* generate frame condition by applying the frame rule *) 
    let framecond =
      if not is_proc then [] else
      let name = "framecondition of " ^ (string_of_ident contr.contr_name) in
      let mk_framecond f = mk_free_spec_form (FOL f) name None post_pos in
      (* final caller footprint is frame with final footprint *)
      let final_footprint_caller_postconds = 
        SortSet.fold (fun ssrt fs ->
          if IdSet.mem (alloc_id ssrt) modifies then
            let final_fpc_set =
              mk_union [mk_diff (init_footprint_caller_set ssrt) (init_footprint_set ssrt);
                        (final_footprint_set ssrt)]
            in
            let f =
              mk_eq (final_footprint_caller_set ssrt) final_fpc_set
            in
            mk_framecond f :: fs
          else fs)
          footprint_sorts []
      in
      (* null is not allocated *)
      let final_alloc_set ssrt =
        if IdSet.mem (alloc_id ssrt) modifies then
          mk_union [mk_diff (init_alloc_set ssrt) (init_footprint_caller_set ssrt);
                    (final_footprint_caller_set ssrt)]
        else init_alloc_set ssrt
      in
      let final_null_alloc =
        SortSet.fold (fun ssrt fs ->
          mk_framecond (mk_and [mk_eq (alloc_set ssrt) (final_alloc_set ssrt); 
                                mk_not (smk_elem (mk_null ssrt) (alloc_set ssrt))]) :: fs)
          footprint_sorts []
      in
      (* frame axioms for modified fields *)
      let all_fields =
        List.fold_left
          (fun acc var ->
            match var.var_sort with
            | Map (Loc _ :: _, _) as srt -> IdMap.add var.var_name srt acc 
            | _ -> acc
          )
          IdMap.empty
          (vars prog)
      in
      let frame_preds =
        IdMap.fold
          (fun fld srt frames ->
            if !Config.opt_field_mod && not (IdSet.mem fld modifies)
            then frames else
            let old_fld = oldify fld in
            let ssrt = struct_sort_of_sort (List.hd (dom_sort srt)) in
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
    let contr1 =
      { contr with
        contr_formals = formals;
        contr_returns = returns;
        contr_locals = locals;
        contr_precond = precond @ other_precond;
        contr_postcond = postcond @ framecond @ other_postcond;
      }
    in
    contr1, footprint_sets, footprint_context
  in
  (* translate the predicates from SL to GRASS *)
  let translate_pred (preds, axioms) pred =
    let is_pure = is_pure_pred pred in
    let pos = pos_of_pred pred in
    let pname = name_of_pred pred in
    (* print_endline @@ "translating predicate " ^ string_of_ident pname; *)
    let contract, footprint_sets, footprint_context =
      translate_contract pred.pred_contract false false is_pure IdSet.empty
    in
    let formals = contract.contr_formals in
    let locals = contract.contr_locals in
    let translate_sl_body body =
      body |>
      (function
        | Sl.Pure (f, _) -> f
        | f -> SlToGrass.to_grass (pred_to_form footprint_context) footprint_sets f) |>
      (* (fun f -> print_form stdout f; print_newline (); f) |> *)
      post_process_form |>
      fun f -> FOL f
    in
    let mk_arg id =
      let decl = IdMap.find id locals in
      mk_var decl.var_sort id
    in
    let mk_pred res_srt pname =
      mk_free_app res_srt pname (List.map mk_arg formals)
    in
    let res_srt = Prog.result_sort_of_pred pred in
    let frame_axioms =
      let old_pred = mk_pred res_srt pname in
      let new_arg_ids =
        List.fold_left (fun new_args id1 ->
          let decl = IdMap.find id1 locals in
          let id2 =
            match decl.var_sort with
            | Set (Loc srt) when id1 = footprint_caller_id srt -> fresh_ident (name id1)
            | _ -> id1
          in
          IdMap.add id1 (id2, decl.var_sort) new_args)
          IdMap.empty formals
      in
      let mk_new_arg id1 = 
        let id2, srt = IdMap.find id1 new_arg_ids in
        mk_var srt id2
      in
      let new_pred =
        mk_free_app res_srt pname (List.map mk_new_arg formals)
      in
      (*let guards =
        List.map
          (fun id -> mk_eq (mk_old_arg id) (mk_new_arg id))
          formals 
      in*)
      let name = "frame of " ^ string_of_ident pname in
      let annot =
        match pred.pred_contract.contr_returns with
        | [] -> [Pattern (mk_known (old_pred), []); Pattern (mk_known (new_pred), [])]
        | _ -> []
      in
      let axiom_forms =
        [Axioms.mk_axiom name (mk_eq old_pred new_pred) |> fun f -> annotate f annot]
      in
      List.map (fun axiom -> mk_free_spec_form (FOL axiom) name None pos) axiom_forms
    in
    let translate_body sf =
      let f1 = match sf.spec_form with
      | SL f -> translate_sl_body f
      | FOL f -> FOL (post_process_form f)
      in { sf with spec_form = f1 }
    in
    let make_fp_funcs pred pred1 =
      let make_for_sort sort =
        let func_name = fp_func_id_of_pred_id pname sort in
        let ret_var_id = mk_ident @@ "FP_" ^ (string_of_sort sort) in
        let ret_var = mk_loc_set_decl sort ret_var_id dummy_position in
        (* Convert the predicate body to the footprint function body *)
        let pred_body =
          let fp_form =
            if is_sl_pred pred
            then pred1.pred_body
            else
              let preconds =
                Util.filter_map
                  (fun x -> not @@ is_sl_spec x)
                  form_of_spec
                  (precond_of_pred pred1)
              in
              let precond = mk_and preconds in
              Some (mk_spec_form (FOL precond) "" None (pos_of_pred pred))
          in
          match fp_form with
          | None -> None
          | Some spec ->
            (* Go through the formula and keep only things that define the footprint *)
            let equals_fp_func = function
              | App (FreeSym id, _, _) when is_fp_func_id pname id -> true
              | _ -> false
            in
            (* True for atoms that may be used to split cases
               Right now looks to see if this atom or its negation appears in all disjuncts *)
            let is_case_split_atom =
              let disjuncts =
                match spec.spec_form with
                | SL _ -> failwith "Expected SL to be eliminated already"
                | FOL f ->
                  let f = f |> nnf |> dnf in
                  (match f with
                  | BoolOp (Or, fs) -> fs
                  | _ -> [f])
              in
              fun atom ->
                let pos, neg =
                  List.fold_left
                    (fun (pos, neg) disjunct ->
                      match disjunct with
                      | BoolOp (And, fs) ->
                          pos || List.exists (equal atom) fs,
                          neg || List.exists (equal (mk_not atom)) fs
                      | _ ->
                          pos || equal disjunct atom,
                          neg || equal disjunct (mk_not atom)
                    )
                    (false, false) disjuncts
                in
                pos && neg
            in
            let rec process_form subsets defs f =
              match f with
              (* Equalities with fp() on one side *)
              | Atom (App (Eq, [t1; t2], _), _)
                when equals_fp_func t1 || equals_fp_func t2 ->
                    subsets, defs, f
              (* Set differences that can be rewritten into a definition of fp() *)
              | Atom (App (Eq, [App (Diff, [t1; t2], _); t3], _), a)
                when equals_fp_func t1 ->
                  if List.mem (t2, t1) subsets
                  then subsets, defs, mk_eq ~ann:a t1 (mk_union [t2; t3])
                  else subsets, ((t1, t2), mk_union [t2; t3]) :: defs, mk_true
              (* Susbet atoms *)
              | Atom (App (SubsetEq, [t1; t2], _), _)
                when equals_fp_func t2 ->
                  (t1, t2) :: subsets, defs,
                  if List.mem_assoc (t2, t1) defs
                  then mk_eq t1 (List.assoc (t2, t1) defs)
                  else mk_true                    
              (* Literals used for case splitting *)
              | Atom (_, _) as atom
              | BoolOp (Not, [Atom (_, _) as atom])
                when is_case_split_atom atom ->
                  subsets, defs, f
              (* Remove all other literals *)
              | Atom (_, _) | BoolOp (Not, _) ->
                  subsets, defs, mk_true
              | BoolOp (op, fs) ->
                  let subsets1, defs1, fs1 =
                    List.fold_right (fun f (subsets, defs, fs1) ->
                      let subsets1, defs1, f1 = process_form subsets defs f in
                      match op with
                      | And -> subsets1, defs1, f1 :: fs1
                      | _ -> subsets, defs1, f1 :: fs1)
                      fs (subsets, defs, [])
                  in
                  if op = And
                  then subsets1, defs1, smk_op op fs1
                  else subsets, defs1, smk_op op fs1
              (* TODO should we allow quantified formulas?? *)
              | Binder (b, vs, f, annots) ->
                  let subsets1, defs1, f1 = process_form subsets defs f in
                  match vs with
                  | [] -> subsets1, defs1, Binder (b, vs, f1, annots)
                  | _ -> subsets, defs, Binder (b, vs, f1, annots)
            in
            let spec_form =
              match spec.spec_form with
              | SL _ -> failwith "Expected SL to be eliminated already"
              | FOL f ->
                  FOL (f |> nnf |> nnf |> process_form [] [] |> function (_, _, f) -> f)
            in
            Some { spec with spec_form = spec_form}
        in
        let fp_func_contract =
          {
            contr_name = func_name;
            contr_formals = pred.pred_contract.contr_formals;
            contr_returns = [ret_var_id];
            contr_locals = IdMap.add ret_var_id ret_var pred.pred_contract.contr_locals; (* TODO find the set of locals used here *)
            contr_precond = [];
            contr_postcond = [];
            contr_footprint_sorts = SortSet.empty;
            contr_pos = dummy_position;
          }
        in
        let footprint_func =
          {
            pred_contract = fp_func_contract;
            pred_body = pred_body;
            pred_accesses = IdSet.empty; (* TODO confirm *)
            pred_is_self_framing = true;
          }
        in
        func_name, footprint_func
      in
      pred.pred_contract.contr_footprint_sorts
      |> SortSet.elements
      |> List.map make_for_sort
    in (* end of make_fp_funcs *)
    let pred1 =
      { pred with
        pred_contract = contract;
        pred_body = Util.Opt.map translate_body pred.pred_body
      }
    in
    let pred_frame_axioms =
      if SortSet.is_empty pred.pred_contract.contr_footprint_sorts
        (*|| pred1.pred_contract.contr_returns <> []*)  (* No extra frame axioms for functions *)
      then []
      else
        begin
          (* we need:
              ∀ new/old_field_1/2 frame old_alloc FP_Caller params.
                Frame(modified, old_alloc, old_field_1, new_field_1) ∨ old_field_1 == new_field_1 ⇒
                Frame(modified, old_alloc, old_field_2, new_field_2) ∨ old_field_2 == new_field_2 ⇒
                Disjoint(pred_fp(old_fields, params), modified) ∧ pred_fp(old_fields, params) ⊆ old_alloc ⇒
                Disjoint(FP_Caller, modified) ∧ FP_Caller ⊆ old_alloc ⇒
                  pred(old_field_1, old_field_2, params) == pred(new_field_1, new_field_2, params)
            
            Also, since pred_fp() is self framing, we add:
              ∀ new/old_field_1/2 frame old_alloc FP_Caller params.
                Frame(modified, old_alloc, old_field_1, new_field_1) ∨ old_field_1 == new_field_1 ⇒
                Frame(modified, old_alloc, old_field_2, new_field_2) ∨ old_field_2 == new_field_2 ⇒
                Disjoint(pred_fp(old_fields, params), modified) ∧ pred_fp(old_fields, params) ⊆ old_alloc ⇒
                Disjoint(FP_Caller, modified) ∧ FP_Caller ⊆ old_alloc ⇒
                  pred_fp(old_fields, params) == pred_fp(new_fields, params)
          *)
          let is_fp srt = SortSet.mem srt pred.pred_contract.contr_footprint_sorts in
          (*let id_fp id = 
            let decl = IdMap.find id locals in
            match decl.var_sort with
            | Set (Loc srt) -> id = footprint_caller_id srt
            | _ -> false
          in*)
          let res_srt = Prog.result_sort_of_pred pred in
          let mk_old_arg id =
            let decl = IdMap.find id locals in
            mk_var decl.var_sort id
          in
          let old_pred =
            mk_free_app res_srt pname (List.map mk_old_arg formals)
          in
          (* To make the axioms linear, create fresh variables for the new predicate term *)
          let new_arg_ids =
            List.fold_left (fun new_args id1 ->
              let decl = IdMap.find id1 locals in
              let id2 = fresh_ident (name id1) in
              IdMap.add id1 (id2, decl.var_sort) new_args)
              IdMap.empty formals
          in
          let mk_new_arg id1 = 
            let id2, srt = IdMap.find id1 new_arg_ids in
            mk_var srt id2
          in
          let new_pred =
            mk_free_app res_srt pname (List.map mk_new_arg formals)
          in
          let sorts = SortSet.elements (pred.pred_contract.contr_footprint_sorts) in
          let frames_and_allocs =
            List.fold_left
              (fun acc s ->
                let str = string_of_sort s in
                let f = mk_var (Set (Loc s)) (fresh_ident ("Modified_" ^ str)) in
                let a = mk_var (Set (Loc s)) (alloc_id (Loc s)) in
                SortMap.add (Set (Loc s)) (f, a) acc)
              SortMap.empty sorts
          in
          (* Generate Disjoint & Subset conditions for both footprints and "reads" footprints *)
          let mk_fp_func args sort =
            mk_free_app (Set (Loc sort)) (fp_func_id_of_pred_id pname sort) args in
          let old_fp_terms =
            let old_args = formals |> List.map mk_old_arg in
            sorts |> List.map (mk_fp_func old_args)
          in
          let new_fp_terms =
            let new_args = formals |> List.map mk_new_arg in
            sorts |> List.map (mk_fp_func new_args)
          in
          (*let reads_terms = formals |> List.filter id_fp |> List.map mk_old_arg in*)
          let in_frame terms =
            List.flatten (
              List.map
                (fun t ->
                  let srt = sort_of t in
                  let modif, alloc = SortMap.find srt frames_and_allocs in
                  [ mk_disjoint t modif ;
                    mk_subseteq t alloc ]
                )
                terms
            )
          in
          let fps_in_frame = in_frame old_fp_terms in
          (*let reads_in_frame = in_frame reads_terms in*)
          let loc_fields =
            List.fold_left (fun loc_fields id1 ->
              let decl = IdMap.find id1 (locals_of_pred pred) in
              match decl.var_sort with
              | Map ([Loc dsrt], _) when is_fp dsrt -> (id1, dsrt) :: loc_fields
              | _ -> loc_fields)
              [] (formals_of_pred pred)
          in
          let loc_fields_modified, frame_terms =
            loc_fields
            |> List.map (fun (id, srt) ->
              let modif, alloc = SortMap.find (Set (Loc srt)) frames_and_allocs in
              let new_field = mk_new_arg id in
              let old_field = mk_old_arg id in
              mk_or [ mk_frame modif alloc old_field new_field ;
                      mk_eq new_field old_field ],
                mk_frame_term modif alloc old_field new_field
            )
            |> List.split
          in
          let args_are_equal =
            formals
            (* Only take the non-fields *)
            |> List.filter (fun id ->
              match (IdMap.find id locals).var_sort with
              | Map ([Loc srt], _) -> is_fp srt |> not
              | _ -> true)
            |> List.map (fun f -> mk_eq (mk_old_arg f) (mk_new_arg f))
          in
          let pred_form = mk_sequent
            (args_are_equal @ loc_fields_modified @ fps_in_frame (*@ reads_in_frame*))
            [mk_eq old_pred new_pred]
          in
          let add_frame_pattern f =
            let frame_patterns = frame_terms |> List.map (fun t -> Pattern (mk_known t, [])) in
            annotate f frame_patterns
          in
          let add_generators f =
            let gen = TermGenerator ([Match (old_pred, [])], old_fp_terms) in
            annotate f [gen]
          in
          let name = "(extra) frame of " ^ string_of_ident pname in
          let axiom_form =
            Axioms.mk_axiom name pred_form
            |> add_frame_pattern
            |> add_generators 
            (* TODO do we need to do this?
            |> fun f -> annotate f [Pattern (mk_known (old_pred), []); Pattern (mk_known (new_pred), [])] *)
          in
          let fp_func_axiom_name = "frame for footprint funcs of " ^ string_of_ident pname in
          let fp_func_axiom =
            Axioms.mk_axiom
              fp_func_axiom_name
              (mk_sequent
                (args_are_equal @ loc_fields_modified @ fps_in_frame)
                (List.combine old_fp_terms new_fp_terms
                  |> List.map (fun (t1, t2) -> mk_eq t1 t2)))
            |> add_frame_pattern
          in
          Debug.debug (fun () -> name);
          Debug.debug (fun () -> string_of_form axiom_form);
          [mk_free_spec_form (FOL axiom_form) name None pos;
            mk_free_spec_form (FOL fp_func_axiom) fp_func_axiom_name None pos]
        end
    in
    (* Add functions for the footprints *)
    let preds =
      if is_pure_pred pred1
      then
        (* Only add for predicates, not for functions *)
        make_fp_funcs pred pred1
        |> List.fold_left
            (fun preds (func_name, func) ->
              IdMap.add func_name func preds)
            preds
      else preds
    in
    IdMap.add pname pred1 preds, pred_frame_axioms @ frame_axioms @ axioms
  in
  let axioms = List.map (map_spec_fol_form post_process_form) prog.prog_axioms in
  let preds, axioms = fold_preds translate_pred (IdMap.empty, axioms) prog in
  let prog = { prog with prog_preds = preds; prog_axioms = axioms } in
  let compile_proc proc =
    let proc_footprints = footprint_sorts_proc proc in
    let contract, footprint_sets, footprint_pre_context =
      translate_contract proc.proc_contract true proc.proc_is_tailrec false (modifies_proc prog proc)
    in
    (* update all procedure calls and return commands in body *)
    let rec compile_stmt = function
      | (Assign ac, pp) ->
          let rhs = List.map post_process_term ac.assign_rhs in
          mk_assign_cmd ac.assign_lhs rhs pp.pp_pos
      | (Return rc, pp) ->
          let fp_returns =
            SortSet.fold (fun ssrt fp_returns ->
              if IdSet.mem (alloc_id ssrt) (modifies_proc prog proc) then
                mk_union [footprint_caller_set ssrt; footprint_set ssrt] :: fp_returns
              else fp_returns)
              proc_footprints []
          in
          let return_args = List.map post_process_term rc.return_args in
          let rc1 = { return_args = return_args @ fp_returns } in
          Basic (Return rc1, pp)
      | (Assume sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 =
                f |>
                SlToGrass.to_grass (pred_to_form footprint_sets) footprint_sets |>
                post_process_form
              in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assume_cmd sf1 pp.pp_pos
          | FOL f ->
	     let f1 = post_process_form f in
	     let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
             mk_assume_cmd sf1 pp.pp_pos)
      | (Assert sf, pp) ->
          (match sf.spec_form with
          | SL f ->
              let f1 =
                f |>
                SlToGrass.to_grass (pred_to_form footprint_sets) footprint_sets |>
                post_process_form
              in
              let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
              mk_assert_cmd sf1 pp.pp_pos
          | FOL f ->
	     let f1 = post_process_form f in
	     let sf1 = mk_spec_form (FOL f1) sf.spec_name sf.spec_msg sf.spec_pos in
             mk_assert_cmd sf1 pp.pp_pos)
      | (Call cc, pp) ->
          let decl = find_proc prog cc.call_name in
          let footprint_ids, footprint_sets =
            SortSet.fold
              (fun ssrt (ids, sets) ->
                (if IdSet.mem (alloc_id ssrt) (modifies_proc prog decl)
                then footprint_id ssrt :: ids
                else ids),
                footprint_set ssrt :: sets
              )
              (footprint_sorts_proc decl) ([], [])
          in
          let call_args = List.map post_process_term cc.call_args in
          mk_call_cmd ~prog:(Some prog) 
            (cc.call_lhs @ footprint_ids) 
            cc.call_name 
            (call_args @ footprint_sets) 
            pp.pp_pos
      | (c, pp) -> Basic (c, pp)
    in
    let body = 
      Util.Opt.map 
        (fun body ->
          let body1 = map_basic_cmds compile_stmt body in
          let body_pp = prog_point body in
          let assign_init_footprints_caller =
            let new_footprint_caller_set ssrt =
              if IdSet.mem (alloc_id ssrt) body_pp.pp_modifies then
                [mk_assign_cmd [footprint_caller_id ssrt] 
                  [mk_diff (footprint_caller_set ssrt) (footprint_set ssrt)]
                  body_pp.pp_pos]
              else []
            in
            SortSet.fold
              (fun ssrt cmds -> new_footprint_caller_set ssrt @ cmds)
              proc_footprints []
          in
          let assign_final_footprints_caller =
            SortSet.fold
              (fun ssrt cmds ->
                (if IdSet.mem (alloc_id ssrt) body_pp.pp_modifies then
                  [mk_assign_cmd 
                    [final_footprint_caller_id ssrt] [mk_union [footprint_caller_set ssrt; footprint_set ssrt]]
                    body_pp.pp_pos]
                  else []) @ cmds)
              proc_footprints []
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
      proc_contract = contract;
      proc_body = body;
    } 
  in
  add_ghost_field_invariants (map_procs compile_proc prog)

(** Annotate safety checks for heap accesses *)
let annotate_heap_checks prog =
  let rec checks acc = function
    | App (Read, map :: idx :: _, _) ->
        let acc1 =
          match sort_of map with
          | Map (Loc _ :: _, _) -> TermSet.add idx acc
          | _ -> acc
        in
        checks (checks acc1 map) idx
    | App (Length, [map], _) -> TermSet.add map acc
    | App (ArrayCells, [map], _) -> TermSet.add map acc
    | App (Write, fld :: loc :: ts, _) ->
        List.fold_left checks (TermSet.add loc acc) (fld :: loc :: ts)
    | App ((Div | Mod), [t1; t2], _) ->
        List.fold_left checks (TermSet.add t2 acc) [t1; t2]
    | App (_, ts, _) -> 
        List.fold_left checks acc ts
    | _ -> acc
  in
  let mk_term_checks pos acc t =
    let to_check = checks TermSet.empty t in
    TermSet.fold 
      (fun t acc ->
        match sort_of t with
        | Int ->
            let t_not_zero = FOL (mk_not (mk_eq t (mk_int 0))) in
            let mk_msg callee =
              let msg = "Possible division by zero" in
              msg, msg
            in
            let sf = mk_spec_form t_not_zero "check division" (Some mk_msg) pos in
            let check_division = mk_assert_cmd sf pos in
            check_division :: acc
        | _ ->
            let ssrt = struct_sort_of_sort (sort_of t) in
            let t_in_footprint = FOL ((annotate (mk_elem t (footprint_set ssrt)) [SrcPos pos])) in
            let mk_msg callee =
              let msg = "Possible invalid heap access to location of type " ^ (string_of_sort ssrt) in
              msg, msg
            in
            let sf = mk_spec_form t_in_footprint "check heap access" (Some mk_msg) pos in
            let check_access = mk_assert_cmd sf pos in
        check_access :: acc)
      to_check acc
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
  let simple_arrays = !Config.simple_arrays in
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
                    if simple_arrays
                    then [assume_length_ok]
                    else
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
          | Array srt when not simple_arrays ->
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
  (* declare alloc sets *)
  let struct_srts = struct_sorts prog in
  let prog =
    let globals_with_alloc_sets =
      SortSet.fold
        (fun ssrt acc -> IdMap.add (alloc_id ssrt) (alloc_decl ssrt) acc)
        struct_srts
        prog.prog_vars
    in
    { prog with prog_vars = globals_with_alloc_sets }
  in
  let elim_proc proc =
    { proc with proc_body = Util.Opt.map (map_basic_cmds elim) proc.proc_body } 
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }
