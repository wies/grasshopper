(** {5 Verification of GRASS programs} *)

open Util
open Grass
open GrassUtil
open Prog
open Simplifier
open Grassifier

(** Simplify the given program [prog] by applying all transformation steps. *)
let simplify prog =
  let dump_if n prog = 
    if !Config.dump_ghp == n 
    then (print_prog stdout prog; prog)
    else prog
  in
  let info msg prog = Debug.info (fun () -> msg); prog in
  prog |>
  dump_if 0 |>
  info "Inferring accesses, eliminating loops, arrays, new/dispose, and global dependencies.\n" |>
  elim_arrays |>
  elim_new_dispose |>
  Analyzer.infer_accesses |>
  elim_loops |>
  elim_global_deps |>
  dump_if 1 |>
  info "Eliminating SL, adding heap access checks.\n" |>
  elim_sl |>
  (*(fun prog -> if !Config.abstract_preds then annotate_frame_axioms prog else prog) |> *)
  (*annotate_term_generators |>*)
  annotate_heap_checks |>
  dump_if 2 |>
  info "Eliminating return statements and transforming to SSA form.\n" |>
  elim_return |>
  elim_state |>
  dump_if 3

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
  (* Annotates term generators in predicate bodies *)
  let annotate_term_generators pred f =
    let locals = locals_of_pred pred in
    let formals = formals_of_pred pred in
    let returns = returns_of_pred pred in
    let name = name_of_pred pred in
    let fun_terms bvs f =
      let rec ft acc = function
        | App (sym, _ :: _, srt) as t when is_free_symbol sym || srt <> Bool ->
            let fvs = fv_term t in
            if IdSet.subset fvs bvs && not @@ IdSet.is_empty (fv_term t)
            then TermSet.add t acc else acc
        | App (_, ts, _) ->
            List.fold_left ft acc ts
        | _ -> acc
      in
      fold_terms ft TermSet.empty f
    in
    let sorted_vs =
      List.map
        (fun x ->
          let var = IdMap.find x locals in
          x, var.var_sort)
        formals
    in
    let pvs = List.map (fun (x, srt) -> mk_var srt x) sorted_vs in
    let m, kgen = match returns with
    | [] ->
        let mt = mk_free_fun Bool name pvs in
        let m = Match (mt, []) in
        m, [TermGenerator ([m], [mk_known mt])]
    | [x] ->
        let var = IdMap.find x locals in
        Match (mk_free_fun var.var_sort name pvs, []), []
    | _ -> failwith "Functions may only have a single return value."
    in
    let rec add_match = function
      | Binder (b, vs, f, annots) ->
          let annots1 =
            List.map (function TermGenerator (ms, ts) -> TermGenerator (m :: ms, ts) | a -> a) annots
          in
          Binder (b, vs, add_match f, annots1)
      | BoolOp (op, fs) ->
          BoolOp (op, List.map add_match fs)
      | f -> f
    in
    let rec add_generators bvs = function
      | BoolOp (op, fs) ->
          BoolOp (op, List.map (add_generators bvs) fs)
      | Binder (Forall, vs, f, ann) ->
          let bvs = List.fold_left (fun bvs (v, _) -> IdSet.add v bvs) bvs vs in
          let pvs = id_set_of_list @@ List.map fst sorted_vs in
          let ft =
            f |>
            fun_terms bvs |>
            TermSet.elements |>
            List.filter (fun t -> IdSet.subset (fv_term t) pvs)
          in
          let generators =
            (match ft with
            | [] -> []
            | _ -> [TermGenerator ([m], ft)])
            @ kgen              
          in
          Binder (Forall, vs, add_generators bvs f, generators @ ann)
      | f -> f
    in
    add_generators IdSet.empty (add_match f)
  in
  (* Expands definition of predicate [p] for arguments [ts] assuming polarity of occurrence [pol] *)
  let expand_pred pos p ts =
    let pred = find_pred prog p in
    let locals = locals_of_pred pred in
    let formals = formals_of_pred pred in
    let returns = returns_of_pred pred in
    let name = name_of_pred pred in
    let sm =
      try
        List.fold_left2 
          (fun sm id t -> IdMap.add id t sm)
          IdMap.empty formals ts
      with Invalid_argument _ ->
        failwith ("Fatal error while expanding predicate " ^ string_of_ident name)
    in
    let sm =
      match returns with
      | [] -> sm
      | [id] -> 
          let var = IdMap.find id locals in
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
    f |>
    nnf |>
    expand_neg None IdSet.empty |>
    (*fun f -> print_endline "before: "; print_form stdout f; print_newline(); f ) |> *)
    foralls_to_exists |>
    (*fun f -> print_endline "after: "; print_form stdout f; print_newline(); f ) |> *)
    propagate_exists |>
    foralls_to_exists
    (* (fun f -> print_endline "after: "; print_form stdout f; print_newline(); f ) *)
  in
  let vs, f, a = match f_inst with
  | Binder (Exists, vs, f, a) -> vs, f, a
  | _ -> [], f_inst, []
  in
  let pred_def pred =
    let locals = locals_of_pred pred in
    let formals = formals_of_pred pred in
    let returns = returns_of_pred pred in
    let name = name_of_pred pred in
    let sorted_vs, sm =
      List.fold_right
        (fun id (sorted_vs, sm) ->
          let var = IdMap.find id locals in
          (id, var.var_sort) :: sorted_vs,
          IdMap.add id (Var (id, var.var_sort)) sm
        )
        formals ([], IdMap.empty)
    in
    let defs = List.map form_of_spec (pred.pred_body :: postcond_of_pred pred) in
    let defs =
      let rec split acc = function
        | Binder (Forall, vs, BoolOp (And, fs), a) :: ofs ->
            split acc (List.map (fun f -> Binder (Forall, vs, f, a)) fs @ ofs)
      | BoolOp (And, fs) :: ofs ->
          split ofs (fs @ ofs)
      | f :: ofs -> split (f :: acc) ofs
      | [] -> List.rev acc
      in split [] defs
    in
    let vs = List.map (fun (id, srt) -> Var (id, srt)) sorted_vs in
    let sm, defs =
      match returns with
      | [] -> sm, List.map (fun f -> mk_implies (mk_pred name vs) f) defs
      | [id] -> 
          let var = IdMap.find id locals in
          IdMap.add id (mk_free_fun var.var_sort name vs) sm, defs
      | _ -> failwith "Functions may only have a single return value."
    in
    let cnt = ref 0 in
    let annot () =
      let i = !cnt in
      cnt := i+1;
      Name ("definition_of_" ^ (string_of_ident name), i)
    in
    let pat =
      match returns with
      | [] -> [Pattern (mk_known (mk_free_fun Bool name vs), [])]
      | _ -> []
    in
    List.map (fun f ->
      f |>
      subst_consts sm |>
      smk_forall ~ann:(annot () :: pat) sorted_vs |>
      skolemize |>
      (*propagate_forall |>*)
      annotate_term_generators pred)
      defs
      (*(fun fs -> print_forms stdout fs; print_newline (); fs)*)
  in
  let pred_defs = Prog.fold_preds (fun acc pred -> pred_def pred @ acc) [] prog in
  let f = mk_exists ~ann:a vs (smk_and (f :: pred_defs)) in
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
  let proc_name = name_of_proc proc in
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
              | Some msg -> msg proc_name
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
                (string_of_ident proc_name ^ "_" ^ name)
            in
            let vc = pre @ [mk_name name f] in
            let vc_and_preds = add_pred_insts prog (smk_and vc) in
            let labels, vc_and_preds = add_labels vc_and_preds in
            (vc_name, vc_msg, smk_and (axioms @ [vc_and_preds]), labels) :: acc, []
        | _ -> 
            failwith "vcgen: found unexpected basic command that should have been desugared"
  in
  match proc.proc_body with
  | Some body -> List.rev (fst (vcs [] [] body))
  | None -> []

(** Generate verification conditions for procedure [proc] of program [prog] and check them. *)
let check_proc prog proc =
  let check_vc errors (vc_name, (vc_msg, pp), vc0, labels) =
    let check_one vc =
      if errors <> [] && not !Config.robust then errors else begin
        Debug.info (fun () -> "Checking VC: " ^ vc_name ^ ".\n");
        Debug.debug (fun () -> (string_of_form vc) ^ "\n");
      (*IdMap.iter (fun id (pos, c) -> Printf.printf ("%s -> %s: %s\n") 
         (string_of_ident id) (string_of_src_pos pos) c) labels;*)
        let sat_means = 
          Str.global_replace (Str.regexp "\n\n") "\n  " (ProgError.error_to_string pp vc_msg)
        in
        let session_name =
          Filename.chop_extension (Filename.basename pp.sp_file) ^ "_" ^ vc_name 
        in
        match Prover.get_model ~session_name:session_name ~sat_means:sat_means vc with
        | None -> errors
        | Some model -> 
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
            (pp, error_msg, model) :: errors
      end
    in check_one vc0
  in
  let _ = Debug.info (fun () -> "Checking procedure " ^ string_of_ident (name_of_proc proc) ^ "...\n") in
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
      | _, _ -> None) prog.prog_vars (locals_of_proc proc)
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
