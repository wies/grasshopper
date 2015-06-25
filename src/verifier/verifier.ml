(** {5 Verification of GRASS programs} *)

open Grass
open GrassUtil
open Prog
open Simplifier
open Grassifier

(** Simplify the given program [prog] by applying all transformation steps. *)
let simplify prog =
  let dump_if n prog = 
    if !Config.dump_ghp == n 
    then print_prog stdout prog 
    else ()
  in
  dump_if 0 prog;
  Debug.info (fun () -> "Inferring accesses, eliminating loops, arrays, and global dependencies.\n");
  let prog = elim_arrays prog in
  let prog = Analyzer.infer_accesses prog in
  let prog = elim_loops prog in
  let prog = elim_global_deps prog in
  dump_if 1 prog;
  Debug.info (fun () -> "Eliminating SL, adding heap access checks, and eliminating new/dispose.\n");
  let prog = elim_sl prog in
  let prog = annotate_heap_checks prog in
  let prog = elim_new_dispose prog in
  dump_if 2 prog;
  Debug.info (fun () -> "Eliminating return statements and transforming to SSA form.\n");
  let prog = elim_return prog in
  let prog = elim_state prog in
  dump_if 3 prog;
  prog

(** Annotate [msg] as comment to leaves of formula [f] *)
let annotate_aux_msg msg f = 
  let annotate annot = 
    if List.exists (function ErrorMsg _ -> true | _ -> false) annot 
    then annot
    else 
      Util.partial_map 
        (function SrcPos pos -> Some (ErrorMsg (pos, msg)) | _ -> None)
        annot @ annot
  in
  let rec annotate_form = function
    | Binder (Forall as b, vs, (BoolOp (Or, fs) as f), annot)
    | Binder (Exists as b, vs, (BoolOp (And, fs) as f), annot) ->
        if List.for_all (function Atom (_, _) | BoolOp (Not, [Atom (_, _)]) -> true | _ -> false) fs &&
          List.exists (function SrcPos _ -> true | _ -> false) annot
        then Binder (b, vs, f, annotate annot)
        else 
          Binder (b, vs, annotate_form f, annotate annot)
    | Binder (b, vs, f, annot) ->
        Binder (b, vs, annotate_form f, annotate annot)
    | BoolOp (op, fs) -> 
        BoolOp (op, List.map annotate_form fs)
    | Atom (t, annot) -> Atom (t, annotate annot)
  in annotate_form f  

(** Add labels for trace generation and debugging to verification condition [vc] *)
let add_labels vc =
  let process_annot (ltop, annots) = function
    | ErrorMsg (pos, msg) ->
        let lbl = fresh_ident "Label" in
        IdMap.add lbl (pos, msg) ltop, 
        Label lbl :: annots 
    | ann -> ltop, ann :: annots
  in
  let rec al f ltop = 
    match f with
    | BoolOp (op, fs) -> 
        let ltop1, fs1 = 
          List.fold_right (fun f (ltop, fs1) -> 
            let ltop1, f1 = al f ltop in
            ltop1, f1 :: fs1) fs (ltop, [])
        in
        ltop1, BoolOp (op, fs1)
    | Binder (b, vs, f, annots) ->
        let ltop1, f1 = al f ltop in
        let ltop2, annots1 = List.fold_left process_annot (ltop1, []) annots in
        ltop2, Binder (b, vs, f1, annots1)
    | Atom (t, annots) -> 
        let ltop1, annots1 = List.fold_left process_annot (ltop, []) annots in
        ltop1, Atom (t, annots1)
  in
  al vc IdMap.empty

(** Expand predicate definitions for all predicates in formula [f] according to program [prog] *)
let add_pred_insts prog f =
  let expand_pred pos p ts =
    let pred = find_pred prog p in
    let sm =
      try
        List.fold_left2 
          (fun sm id t -> IdMap.add id t sm)
          IdMap.empty (pred.pred_formals @ pred.pred_footprints) ts
      with Invalid_argument _ ->
        failwith ("Fatal error while expanding predicate " ^ string_of_ident pred.pred_name)
    in
    let sm =
      match pred.pred_outputs with
      | [] -> sm
      | [id] -> 
          let var = IdMap.find id pred.pred_locals in
          IdMap.add id (mk_free_fun var.var_sort p ts) sm
      | _ -> failwith "Functions may only have a single return value."
    in
    let body = subst_consts sm (form_of_spec pred.pred_body) in
    if pos then body else nnf (mk_not body)
  in
  let f_inst = 
    let rec expand_neg msg_opt seen = function
      | Binder (b, vs, f, a) -> 
          Binder (b, vs, expand_neg msg_opt seen f, a)
      | BoolOp (And as op, fs)
      | BoolOp (Or as op, fs) ->
          let fs_inst = List.map (expand_neg msg_opt seen) fs in
          smk_op op fs_inst
      | BoolOp (Not, [Atom (App (FreeSym p, ts, _), a)])
        when IdMap.mem p prog.prog_preds && 
          not (IdSet.mem p seen) ->
            let pbody = expand_pred false p ts in
            let p_msg = ProgError.mk_error_info ("Definition of predicate " ^ (string_of_ident p)) in
            let a1 = 
              match msg_opt with
              | Some msg ->
                  Util.partial_map (function SrcPos pos -> Some (ErrorMsg (pos, msg)) | _ -> None) a @ a
              | None -> a
            in
            let p1 = (smk_and [(*mk_not (mk_pred p ts);*) pbody]) in
            let f1 = expand_neg (Some p_msg) (IdSet.add p seen) p1 in
            annotate (annotate_aux_msg p_msg f1) a1
      | f -> f
    in 
    let f1 = expand_neg None IdSet.empty (nnf f) in
    (*print_endline "f1:";
    print_form stdout (f1); print_newline (); print_newline ();
    print_endline "foralls_to_exists f1:";
    print_form stdout (foralls_to_exists f1); print_newline (); print_newline ();*)
    propagate_exists (foralls_to_exists f1)
  in
  let vs, f, a = match f_inst with
  | Binder (Exists, vs, f, a) -> vs, f, a
  | _ -> [], f_inst, []
  in
  (*let pos_preds = 
    let rec collect pos = function
      | (seen, Binder (_, [], f, _)) :: todo -> 
          collect pos ((seen, f) :: todo)
      | (seen, BoolOp (And, fs)) :: todo
      | (seen, BoolOp (Or, fs)) :: todo ->
          collect pos (List.fold_left (fun todo f -> (seen, f) :: todo) todo fs)
      | (seen, Atom (App (FreeSym p, ts, _) as t, _)) :: todo -> 
          let todo1 = 
            List.fold_left (fun todo t -> (seen, Atom (t, [])) :: todo) todo ts
          in
          let pos1, todo2 =
            if IdMap.mem p prog.prog_preds && not (TermSet.mem t pos) && not (IdSet.mem p seen)
            then 
              TermSet.add t pos, (IdSet.add p seen, expand_pred true p ts) :: todo1
            else pos, todo1
          in
          collect pos1 todo2
      | (seen, BoolOp (Not, [Atom (App (_, ts, _), _)])) :: todo
      | (seen, Atom (App (_, ts, _), _)) :: todo -> 
          let todo1 = 
            List.fold_left (fun todo t -> (seen, Atom (t, [])) :: todo) todo ts
          in
          collect pos todo1
      | _ :: todo -> collect pos todo
      | [] -> pos
    in collect TermSet.empty [(IdSet.empty, f)]
  in*)
  let pred_def pred =
    let args = pred.pred_formals @ pred.pred_footprints in
    let sorted_vs, sm =
      List.fold_right
        (fun id (sorted_vs, sm) ->
          let var = IdMap.find id pred.pred_locals in
          (id, var.var_sort) :: sorted_vs,
          IdMap.add id (Var (id, var.var_sort)) sm
        )
        args ([], IdMap.empty)
    in
    let body = form_of_spec pred.pred_body in
    let body =
      match body with
      | Binder (Forall, vs, BoolOp (And, fs), a) ->
          List.map (fun f -> Binder (Forall, vs, f, a)) fs
      | BoolOp (And, fs) ->
          fs
      | f -> [f]
    in
    let vs = List.map (fun (id, srt) -> Var (id, srt)) sorted_vs in
    let sm, body =
      match pred.pred_outputs with
      | [] -> sm, List.map (fun f -> mk_implies (mk_pred pred.pred_name vs) f) body
      | [id] -> 
          let var = IdMap.find id pred.pred_locals in
          IdMap.add id (mk_free_fun var.var_sort pred.pred_name vs) sm, body
      | _ -> failwith "Functions may only have a single return value."
    in
    List.map (fun f -> smk_forall sorted_vs (subst_consts sm f)) body    
  in
  let pred_defs = Prog.fold_preds (fun acc pred -> pred_def pred @ acc) [] prog in
  (*let pos_instances = 
    TermSet.fold (fun t instances ->
      match t with
      | App (FreeSym p, ts, srt) ->
          let pbody = expand_pred true p ts in
          (match srt with
          | Bool -> mk_implies (mk_pred p ts) pbody :: instances
          | _ -> pbody :: instances)
      | _ -> instances)
      pos_preds []
  in*)
  (*print_form stdout (smk_and (f_inst :: pos_instances)); print_newline ();*)
  let f = mk_exists ~ann:a vs (smk_and (f :: pred_defs (*@ pos_instances*))) in
  f
        
(** Generate verification conditions for procedure [proc] of program [prog]. 
 ** Assumes that [proc] has been transformed into SSA form. *)
let vcgen prog proc =
  let axioms = 
    Util.flat_map 
      (fun sf -> 
        let name = 
          Printf.sprintf "%s_%d_%d" 
            sf.spec_name sf.spec_pos.sp_start_line sf.spec_pos.sp_start_col
        in
        match sf.spec_form with FOL f -> [mk_name name f] | SL _ -> [])
      prog.prog_axioms
  in
  let rec vcs acc pre = function
    | Loop _ -> 
        failwith "vcgen: loop should have been desugared"
    | Choice (cs, pp) ->
        let acc1, traces = 
          List.fold_left (fun (acc, traces) c ->
            let acc1, trace = vcs acc pre c in
            acc1, trace :: traces)
            (acc, []) cs
        in acc1, [smk_or (List.rev_map smk_and traces)]
    | Seq (cs, pp) -> 
        let acc1, trace, _ = 
          List.fold_left (fun (acc, trace, pre) c ->
            let acc1, c_trace = vcs acc pre c in
            acc1, trace @ c_trace, pre @ c_trace)
            (acc, [], pre) cs 
        in
        acc1, trace
    | Basic (bc, pp) ->
        match bc with
        | Assume s ->
            let name = 
              Printf.sprintf "%s_%d_%d" 
                s.spec_name pp.pp_pos.sp_start_line pp.pp_pos.sp_start_col
            in
            (match s.spec_form with
              | FOL f -> acc, [mk_name name f]
              | _ -> failwith "vcgen: found SL formula that should have been desugared")
        | Assert s ->
            let name = 
              Printf.sprintf "%s_%d_%d" 
                s.spec_name pp.pp_pos.sp_start_line pp.pp_pos.sp_start_col
            in
            let vc_msg, vc_aux_msg = 
              match s.spec_msg with
              | None -> 
                  "Possible assertion violation.", 
                  ProgError.mk_error_info "This is the assertion that might be violated"
              | Some msg -> msg proc.proc_name
            in 
            let vc_msg = (vc_msg, pp.pp_pos) in
            let f =
              match s.spec_form with
              | FOL f ->
                  let f1 = unoldify_form (mk_not f) in
                  let f2 = annotate_aux_msg vc_aux_msg f1 in
                  f2
              | _ -> failwith "vcgen: found SL formula that should have been desugared"
            in
            let vc_name = 
              Str.global_replace (Str.regexp " ") "_"
                (string_of_ident proc.proc_name ^ "_" ^ name)
            in
            let vc = pre @ [mk_name name f] in
            (vc_name, vc_msg, smk_and (axioms @ vc)) :: acc, []
        | _ -> 
            failwith "vcgen: found unexpected basic command that should have been desugared"
  in
  match proc.proc_body with
  | Some body -> List.rev (fst (vcs [] [] body))
  | None -> []

(** Generate verification conditions for procedure [proc] of program [prog] and check them. *)
let check_proc prog ?(multiple_models=false) proc =
  let check_vc errors (vc_name, (vc_msg, pp), vc0) =
    let check_one vc =
      if errors <> [] && not !Config.robust then errors else
      let vc_and_preds = add_pred_insts prog vc in
      let labels, vc_and_preds = add_labels vc_and_preds in
      Debug.info (fun () -> "Checking VC: " ^ vc_name ^ ".\n");
      Debug.debug (fun () -> (string_of_form vc_and_preds) ^ "\n");
      (*IdMap.iter (fun id (pos, c) -> Printf.printf ("%s -> %s: %s\n") 
          (string_of_ident id) (string_of_src_pos pos) c) labels;*)
      let sat_means = 
        Str.global_replace (Str.regexp "\n\n") "\n  " (ProgError.error_to_string pp vc_msg)
      in
      let session_name =
        Filename.chop_extension (Filename.basename pp.sp_file) ^ "_" ^ vc_name 
      in
      match Prover.get_model
	      ~session_name:session_name ~sat_means:sat_means
	      ~multiple_models:multiple_models
	      vc_and_preds
      with
      | None -> errors
      | Some ([]) -> errors
      | Some (model :: models) -> 
          (* generate error message from model *)
          let add_msg pos msg error_msgs =
            let filtered_msgs = 
              List.filter 
                (fun (pos2, _) -> not (contained_in_src_pos pos pos2))
                error_msgs
            in
            (pos, msg) :: filtered_msgs
          in
          let error_msgs = 
            IdMap.fold 
              (fun id (pos, msg) error_msgs ->
                let p = mk_free_const Bool id in
                match Model.eval_bool_opt model p with
                | Some true ->
                    add_msg pos msg error_msgs
                | _ -> error_msgs
              ) 
              labels []
          in
          let sorted_error_msgs = 
            List.sort
              (fun (pos1, msg1) (pos2, msg2) -> 
                let mc = 
                  compare (String.get msg1 0) (String.get msg2 0) 
                in
                if mc = 0 then compare_src_pos pos1 pos2 else mc) 
              error_msgs
          in
          let error_msg_strings = 
            List.map 
              (fun (pos, msg) -> ProgError.error_to_string pos msg) 
              sorted_error_msgs
          in
          let error_msg =
            String.concat "\n\n" (vc_msg :: error_msg_strings)
          in
          (pp, error_msg, model, models) :: errors
    in check_one vc0
  in
  let _ = Debug.info (fun () -> "Checking procedure " ^ string_of_ident proc.proc_name ^ "...\n") in
  let vcs = vcgen prog proc in
  List.fold_left check_vc [] vcs

(** Generate a counterexample trace from a failed VC of procedure [proc] in [prog]. 
  * Here [pp] is the point of failure in [proc] and [model] is the counterexample model. *)
let get_trace prog proc (pp, model) =
  let add (pos, state) = function
    | (prv_pos, prv_state) :: trace ->
        if prv_pos = pos 
        then (prv_pos, prv_state) :: trace
        else (pos, state) :: (prv_pos, prv_state) :: trace
    | [] -> [(pos, state)]
  in
  let rec update_vmap (vmap, all_aux) = function
    | Atom (App (Eq, [App (FreeSym (name, num), [], _); _], _), _) ->
        let decl = find_var prog proc (name, num) in
        IdMap.add (name, 0) (name, num) vmap,
        decl.var_is_aux && all_aux
    | BoolOp (And, fs) ->
        List.fold_left update_vmap (vmap, all_aux) fs
    | Binder (_, [], f, _) -> 
        update_vmap (vmap, all_aux) f
    | _ -> vmap, all_aux
  in
  let get_curr_state pos vmap model =
    let ids = 
      IdMap.fold 
        (fun _ id ids -> 
          let decl = find_var prog proc id in
          if decl.var_is_aux && name id <> "FP" && name id <> "Alloc" || 
             not (contained_in_src_pos pos decl.var_scope) 
          then ids
          else IdSet.add id ids) 
        vmap IdSet.empty 
    in
    let rmodel = Model.restrict_to_idents model ids in
    Model.rename_free_symbols rmodel (fun (name, _) -> (name, 0))
  in
  let rec gt vmap trace = function
    | Choice (cs, pp) :: cs1 ->
        Util.flat_map (gt vmap trace) (List.map (fun c -> c :: cs1) cs)
    | Seq (cs, pp) :: cs1 -> 
        gt vmap trace (cs @ cs1)
    | Basic (bc, _)  :: cs1 ->
        (match bc with
        | Assume s ->
            (match s.spec_name with
            | "assign" | "if_then" | "if_else" | "havoc" ->
                let f = form_of_spec s in
                (match Model.eval_form model f with
                | None -> 
                    (*print_string "Ignoring command: ";
                    print_endline (Grass.string_of_src_pos s.spec_pos);
                    Prog.print_cmd stdout c;
                    print_newline ();*)
                    gt vmap trace cs1
                | Some true -> 
                    (*print_string "Adding command: ";
                    print_endline (Grass.string_of_src_pos s.spec_pos);
                    Prog.print_cmd stdout c;
                    print_newline ();*)
                    let curr_state = get_curr_state s.spec_pos vmap model in
                    if s.spec_name = "assign" || s.spec_name = "havoc"
                    then 
                      let vmap1, all_aux = update_vmap (vmap, true) f in
                      let trace1 = 
                        if all_aux 
                        then trace 
                        else add (s.spec_pos, curr_state) trace
                      in
                      gt vmap1 trace1 cs1
                    else gt vmap (add (s.spec_pos, curr_state) trace) cs1
                | Some false -> 
                    (* print_string "Dropping trace on assume: ";
                    print_endline (Grass.string_of_src_pos s.spec_pos);
                    Prog.print_cmd stdout c;
                    print_newline (); *)
                    [])
            | "join" -> 
                let vmap1, _ = update_vmap (vmap, true) (form_of_spec s) in
                gt vmap1 trace cs1
            | _ -> gt vmap trace cs1)
        | Assert s ->
            if pp = s.spec_pos
            then 
              let curr_state = get_curr_state pp vmap model in
              List.rev ((pp, curr_state) :: trace)
            else gt vmap trace cs1
        | _ -> gt vmap trace cs1)
    | _ :: cs1 -> gt vmap trace cs1
    | [] -> 
        let curr_state = get_curr_state pp vmap model in
        List.rev ((pp, curr_state) :: trace)
  in 
  let init_vmap =
    let vars = IdMap.merge (fun id v1 v2 ->
      match v1, v2 with
      | Some v1, _ -> Some v1
      | _, Some v2 -> Some v2
      | _, _ -> None) prog.prog_vars proc.proc_locals
    in
    IdMap.fold 
      (fun (name, num) _ vmap -> 
        try 
          if snd (IdMap.find (name, 0) vmap) > num 
          then IdMap.add (name, 0) (name, num) vmap
          else vmap
        with Not_found -> IdMap.add (name, 0) (name, num) vmap)
      vars IdMap.empty
  in
  match gt init_vmap [] (Util.Opt.to_list proc.proc_body) with
  | _ :: trace -> trace
  | [] -> []
