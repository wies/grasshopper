open Grass
open GrassUtil
open Util
open Axioms

let mk_inst_closure_term t = mk_free_app Bool ("inst-closure", 0) [t]
let mk_inst_closure t = mk_pred ("inst-closure", 0) [t]
  
let get_signature fs =
  let sign = overloaded_sign (mk_and fs) in
  if !Config.instantiate then sign else
  (* Add known and inst-closure predicates to signature *)
  let all_srts =
    SymbolMap.fold
      (fun _ funSig acc ->
        List.fold_left
          (fun acc (args, ret) ->
              List.fold_left (fun acc srt -> SortSet.add srt acc) (SortSet.add ret acc) args
          )
          acc
          funSig
      )
      sign
      SortSet.empty
  in
  let inst_closure_variants =
    SortSet.fold (fun srt variants -> ([srt], Bool) :: variants) all_srts []
  in
  let known_variants =
    SortSet.fold (fun srt variants -> ([srt], Pat) :: variants) all_srts []
  in
  if inst_closure_variants <> [] then
    sign |>
    SymbolMap.add (FreeSym ("inst-closure", 0)) inst_closure_variants |>
    SymbolMap.add Known known_variants
  else sign

  
let encode_labels fs =
  let mk_label annots f = 
    let lbls = 
      Util.partial_map 
        (function 
          | Label (pol, t) ->
              Some (if pol then Atom (t, []) else mk_not (Atom (t, [])))
          | _ -> None)
        annots
    in
    mk_and (f :: lbls)
  in
  let rec el = function
    | Binder (b, vs, f, annots) ->
        let f1 = el f in
        mk_label annots (Binder (b, vs, f1, annots))
    | (BoolOp (Not, [Atom (_, annots)]) as f)
    | (Atom (_, annots) as f) ->
        mk_label annots f
    | BoolOp (op, fs) ->
        BoolOp (op, List.map el fs)
  in List.rev_map el fs

let add_inst_closures fs gts =
  if not !Config.smtpatterns && !Config.instantiate then fs else
  (*let gts_fs = ground_terms (mk_and fs) in*)
  let extra_gts = (*TermSet.diff gts gts_fs*) gts in
  let fs1 = 
    TermSet.fold (fun t fs1 ->
      match sort_of t with
      | Bool -> fs1
      | srt ->
          mk_inst_closure t :: fs1)
      extra_gts fs
  in fs1

let encode_term_generators fs generators =
  let process_gen fs = function
    | ms, (_ :: _ as ts)
      when List.for_all (function Match (_, []) -> true | _ -> false) ms ->
        let mk_ic (Match (t, _)) = mk_inst_closure t in
        let f = mk_sequent (List.map mk_ic ms) [mk_and (List.map mk_inst_closure ts)] in
        let ps = List.map (function Match (t, _) -> Pattern (mk_inst_closure_term t, [])) ms in
        let vs = sorted_free_vars f |> IdSrtSet.elements in
        mk_forall ~ann:(Comment "term_generator" :: ps) vs f :: fs
    | _ -> fs
  in
  List.fold_left process_gen fs generators
    
(** Compute term generators for Btwn fields *)
let btwn_field_generators fs =
  let make_generators acc f =
    let ts = terms_with_vars f in
    let btwn_fields t flds = match t with
      | App (Btwn, fld :: _, _) ->
          let vs = fv_term fld in
          if IdSet.is_empty vs
          then flds
          else TermSet.add fld flds
      | _ -> flds
    in
    let btwn_flds = TermSet.fold btwn_fields ts TermSet.empty in
    let process t acc = match t with
      | App (FreeSym _, ts, _) ->
          TermSet.fold (fun fld acc ->
            if IdSet.subset (fv_term fld) (fv_term t)
            then ([Match (t, [])], [mk_known fld]) :: acc
            else acc)
            btwn_flds acc
      | _ -> acc
    in
    TermSet.fold process ts acc
  in
  List.fold_left make_generators [] fs 


(** Linearize axioms *)
let linearize fs =
  let lin_fold fn seen eqs es =
    List.fold_right (fun e (seen, eqs, es1) ->
      let seen, eqs, e1 = fn seen eqs e in
      seen, eqs, e1 :: es1)
      es (seen, eqs, [])
  in
  let rec lin_term noinst seen eqs = function
    | Var (x, srt) as t when IdSet.mem x seen ->
        let x1 = fresh_ident (name x) in
        let t1 = Var (x1, srt) in
        seen, mk_neq t t1 :: eqs, t1
    | Var (x, srt) as t ->
        let seen1 =
          if IdSet.mem x noinst then seen
          else IdSet.add x seen
        in
        seen1, eqs, t
    | App (sym, ts, srt) ->
        let seen, eqs, ts1 = lin_fold (lin_term noinst) seen eqs ts in
        seen, eqs, App (sym, ts1, srt)
  in
  let collect_noinsts noinst anns =
    List.fold_left (fun noinst -> function
      | NoInst ids ->
          IdSet.of_list ids |> IdSet.union noinst
      | _ -> noinst)
      noinst anns
  in
  let rec lin_form noinst seen eqs = function
    | BoolOp (op, fs) ->
      let seen, eqs, fs1 = lin_fold (lin_form noinst) seen eqs fs in
      seen, eqs, BoolOp (op, fs1)
    | Binder (b, [], f, anns) ->
        let noinst = collect_noinsts noinst anns in 
        let seen, eqs, f1 = lin_form noinst seen eqs f in
        seen, eqs, Binder (b, [], f1, anns)
    | Atom (App (sym, ts, srt), anns) ->
        let noinst = collect_noinsts noinst anns in 
        let seen, eqs, ts1 = lin_fold (fun _ -> lin_term noinst IdSet.empty) seen eqs ts in
        seen, eqs, Atom (App (sym, ts1, srt), anns)
    | f -> seen, eqs, f 
  in
  List.map (fun f ->
    let _, eqs, f1 = lin_form IdSet.empty IdSet.empty [] f in
    mk_or (f1 :: eqs))
    fs

let flatten fs =
  let flat_fold fn eqs es =
    List.fold_right (fun e (eqs, es1) ->
      let eqs, e1 = fn eqs e in
      eqs, e1 :: es1)
      es (eqs, [])
  in
  let rec flat_term flatten eqs t = match t with
  | App (sym, ts, srt) ->
      let flatten1 = match sym, srt with
      | (Constructor _ | Destructor _), _
      | _, Adt _ -> fv_term t <> IdSet.empty
      | _ -> false
      in
      let eqs, ts1 = flat_fold (flat_term flatten1) eqs ts in
      if flatten then
        let x = mk_var srt (fresh_ident "x") in
        mk_neq x (mk_app srt sym ts1) :: eqs, x
      else eqs, App (sym, ts1, srt)
  | _ -> eqs, t
  in
  let rec flat_form eqs = function
    | BoolOp (op, fs) ->
      let eqs, fs1 = flat_fold flat_form eqs fs in
      eqs, BoolOp (op, fs1)
    | Binder (b, [], f, anns) ->
        let eqs, f1 = flat_form eqs f in
        eqs, Binder (b, [], f1, anns)
    | Atom (App (sym, ts, srt), anns) ->
        let eqs, ts1 = flat_fold (flat_term false) eqs ts in
        eqs, Atom (App (sym, ts1, srt), anns)
    | f -> eqs, f 
  in
  List.map (fun f ->
    let eqs, f1 = flat_form [] f in
    mk_or (f1 :: eqs))
    fs
    
(** Generate local instances of all axioms of [fs] in which variables occur below function symbols *)
let instantiate_and_prove session fs =
  let fs1 = encode_labels fs in
  let signature = get_signature fs1 in
  let session = SmtLibSolver.declare session signature in
  let rename_forms fs =
    if !Config.named_assertions then
      let fs = List.rev_map unique_names fs in
      let fs = List.rev_map name_unnamed fs in
      fs
    else fs
  in
  let rec is_horn seen_pos = function
    | BoolOp (Or, fs) :: gs -> is_horn seen_pos (fs @ gs)
    | Binder (Forall, [], f, _) :: gs -> is_horn seen_pos (f :: gs)
    | (Atom (App ((Eq | FreeSym _ | SubsetEq | Disjoint), _, _), _)) :: gs ->
        (not seen_pos && is_horn true gs)
    | BoolOp (And, fs) :: gs ->
        List.for_all (fun f -> is_horn seen_pos [f]) gs && is_horn true gs
    | BoolOp (Not, [Atom (App ((Eq | FreeSym _ | SubsetEq | Disjoint) , _, _), _)]) :: gs ->
        is_horn seen_pos gs
    | _ :: _ -> false
    | [] -> true
  in
  let generate_knowns gts =
    TermSet.fold
      (fun t gts ->
        match t with
        | App (FreeSym _, [], Loc _)
        | App (FreeSym _, _ :: _, _) ->
            TermSet.add (mk_known t) gts
        | App (Elem, e :: _, _) when is_loc_sort (sort_of e) ->
            TermSet.add (mk_known t) gts
        | _ -> gts)
      gts gts
  in
  let fs1, generators = open_axioms isFunVar fs1 in
  let btwn_gen = btwn_field_generators fs in
  let gts = ground_terms ~include_atoms:true (mk_and fs) in
  (*let gts = generate_knowns gts in*)
  let tgcode = EMatching.compile_term_generators_to_ematch_code (btwn_gen @ generators) in
  (*let _ =
    print_endline "Term Generator code:";
    EMatching.print_ematch_code pr_term_list stdout tgcode;
    print_newline ()
  in*)
  let cc_graph =
    CongruenceClosure.create () |>
    CongruenceClosure.add_terms gts |>
    CongruenceClosure.add_conjuncts fs
  in
  let round1 fs_inst cc_graph =
    let _, cc_graph = EMatching.generate_terms_from_code tgcode cc_graph in
    let equations = List.filter (fun f -> is_horn false [f]) fs_inst in
    let ground_fs = List.filter is_ground fs_inst in
    let code, patterns = EMatching.compile_axioms_to_ematch_code equations in
    let eqs = EMatching.instantiate_axioms_from_code patterns code cc_graph in
    let gts1 = ground_terms ~include_atoms:true (mk_and eqs) in
    let eqs1 = List.filter (fun f -> IdSet.is_empty (fv f)) eqs in
    let cc_graph =
      cc_graph |>
      CongruenceClosure.add_terms gts1 |>
      CongruenceClosure.add_conjuncts (List.rev_append eqs1 fs)
    in
    let implied = CongruenceClosure.get_implied_equalities cc_graph in
    let gts1 = TermSet.union (ground_terms ~include_atoms:true (mk_and implied)) gts1 in
    let cc_graph = CongruenceClosure.add_terms gts1 cc_graph in
    rev_concat [eqs; ground_fs; implied], cc_graph
  in
  let round1 fs_inst = measure_call "round1" (round1 fs_inst) in
  let round2 fs_inst cc_graph =
    let fs_inst0 = fs_inst in
    let gts_known = generate_knowns gts in
    let core_terms =
      let gts_a = ground_terms (mk_and fs) in
      TermSet.fold (fun t acc ->
        match sort_of t with
        | Loc _ | Int | FreeSrt _ -> TermSet.add (mk_known t) acc
        | _ -> acc)
        gts_a gts_known
    in
    let cc_graph = CongruenceClosure.add_terms core_terms cc_graph in
    let fs1 = linearize fs1 in
    let code, patterns = EMatching.compile_axioms_to_ematch_code fs1 in
    (*let _ =
      print_endline "E-matching code:";
      EMatching.print_ematch_code
        (fun ppf (f, _) -> pr_form ppf f) stdout code;
      print_newline ()
    in*)
    let rec saturate i fs_inst cc_graph =
      Debug.debugl 1 (fun () -> Printf.sprintf "Saturate iteration %d\n" i);
      let has_mods2, cc_graph =
        cc_graph |>
        EMatching.generate_terms_from_code tgcode
      in
      Debug.debugl 1 (fun () -> "Instantiating axioms (round 2)\n");
      let fs_inst = EMatching.instantiate_axioms_from_code patterns code cc_graph in
      Debug.debugl 1 (fun () -> "Getting gound terms (round 2)\n");
      let gts_inst = ground_terms ~include_atoms:true (mk_and fs_inst) in
      (*let gts_inst = ground_terms_acc ~include_atoms:true gts_inst (mk_and implied_eqs) in*)
      (*print_endline "Implied equalities:";
        print_endline (string_of_form (mk_and implied_eqs));*)
      Debug.debugl 1 (fun () -> "Recomputing congruences (round 2)\n");
      let cc_graph =
        cc_graph |>
        CongruenceClosure.add_terms gts_inst |>
        (fun cc_graph -> Debug.debugl 1 (fun () -> "Adding conjuncts (round 2)\n"); cc_graph) |>
        CongruenceClosure.add_conjuncts (rev_concat [fs_inst; fs])
      in
      Debug.debugl 1 (fun () -> "Done recomputing congruences (round 2)\n");
      let has_mods1 = CongruenceClosure.has_mods cc_graph in
      if not !Config.propagate_reads || not (has_mods1 || has_mods2)
      then
        let implied_eqs = CongruenceClosure.get_implied_equalities cc_graph in
        rev_concat [fs_inst; implied_eqs], cc_graph
      else
        saturate (i + 1) fs_inst (CongruenceClosure.reset cc_graph)
    in
    let saturate i fs_inst = measure_call "saturate" (saturate i fs_inst) in
    let fs, cc_graph = saturate 1 fs_inst0 cc_graph in
    let _ =
      if Debug.is_debug 1 then
        begin
          let gts_inst = CongruenceClosure.get_terms cc_graph in
          print_endline "ground terms:";
          TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) gts;
          print_endline "generated terms:";
          TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) (TermSet.diff gts_inst gts)
        end
    in
    fs, cc_graph
  in
  let round2 fs_inst = measure_call "round2" (round2 fs_inst) in
  let do_rounds rounds =
    let dr (k, result, fs_asserted, fs_inst, cc_graph) r =
    match result with
    | Some true | None ->
        let fs_inst1, classes1 = r fs_inst cc_graph in
        let fs_inst1 = rename_forms fs_inst1 in
        let fs_asserted1, fs_inst1_assert =
          List.fold_left (fun (fs_asserted1, fs_inst1_assert) f ->
            let f1 = strip_names f in
            if FormSet.mem f1 fs_asserted1
            then (fs_asserted1, fs_inst1_assert)
            else (FormSet.add f1 fs_asserted1, f :: fs_inst1_assert))
            (fs_asserted, [])
            fs_inst1
        in
        Debug.debug (fun () -> Printf.sprintf "Asserting formulas (round %d)...\n" k);
        measure_call "SmtLibSolver.assert_forms" (SmtLibSolver.assert_forms session) fs_inst1_assert;
        Debug.debug (fun () -> Printf.sprintf "Calling SMT solver in instantiation round %d...\n" k);
        let result1 = measure_call "SmtLibSolver.is_sat" SmtLibSolver.is_sat session in
        Debug.debug (fun () -> "Solver done.\n");
        k + 1, result1, fs_asserted1, fs_inst1, classes1
    | _ -> k, result, fs_asserted, fs_inst, cc_graph
    in List.fold_left dr (1, None, FormSet.empty, fs1, cc_graph) rounds
  in
  let _, result, fs_asserted, fs_inst, _ =
    if !Config.instantiate
    then do_rounds [round1; round2]
    else begin
      let gts = generate_knowns gts in
      let fs1 = encode_term_generators fs1 generators in
      let fs1 = add_inst_closures fs1 gts in
      let fs1 = rename_forms fs1 in
      let fs1 = linearize fs1 in
      SmtLibSolver.assert_forms session fs1;
      let result = measure_call "SmtLibSolver.is_sat" SmtLibSolver.is_sat session in
      (1, result, FormSet.of_list fs1, fs1, cc_graph)
    end
  in
  (match result with
  | Some true | None ->
    Debug.debugl 1 (fun () ->
      "\nSMT called with:\n\n"
      ^ ((FormSet.elements fs_asserted)
          |> smk_and |> string_of_form) ^ "\n\n")
  | Some false -> ());
  result, session, fs_inst

let instantiate_and_prove session = measure_call "Prover.instantiate_and_prove" (instantiate_and_prove session)

let prove name sat_means f =
  if false && name = "b-link-ghost_half_split_precondition_of_lemma_int_valid_fold_627_4" then begin
    Debug.more_verbose (); Debug.more_verbose ()
  end;
  let fs = Reduction.reduce f in
  let session = SmtLibSolver.start name sat_means in
  let result, session, fs = instantiate_and_prove session fs in
  result, session, mk_and fs
  

let dump_model session f =
  if !Config.model_file <> "" then begin
    let gts = ground_terms ~include_atoms:true f in
    let model = Opt.get (SmtLibSolver.get_model session) in
    let model_chan = open_out !Config.model_file in
    if Str.string_match (Str.regexp ".*\\.html$") !Config.model_file 0 then
      ModelPrinting.output_html model_chan (Model.complete model) gts
    else
      ModelPrinting.output_graph model_chan (Model.complete model) gts;
    close_out model_chan;
  end

let dump_core session =
  if !Config.unsat_cores then
    begin
      let core_name = session.SmtLibSolver.log_file_name ^ ".core" in
      (*repeat in a fixed point in order to get a smaller core*)
      let rec minimize core =
        Debug.info (fun () -> "minimizing core " ^ (string_of_int (List.length core)) ^ "\n");
        let s = SmtLibSolver.start core_name session.SmtLibSolver.sat_means in
        let signature = get_signature core in
        let s = SmtLibSolver.declare s signature in
        SmtLibSolver.assert_forms s core;
        let core2 = Opt.get (SmtLibSolver.get_unsat_core s) in
        SmtLibSolver.quit s;
        if List.length core2 < List.length core
        then minimize core2
        else core
      in
      let core = Opt.get (SmtLibSolver.get_unsat_core session) in
      let core = minimize core in
      Debug.debugl 1 (fun () -> "\n\nCore:\n" ^ (string_of_form (smk_and core) ^ "\n\n"));
      let config = !Config.dump_smt_queries in
      Config.dump_smt_queries := true;
      let s = SmtLibSolver.start core_name session.SmtLibSolver.sat_means in
      let signature = get_signature core in
      let s = SmtLibSolver.declare s signature in
      SmtLibSolver.assert_forms s core;
      SmtLibSolver.quit s;
      Config.dump_smt_queries := config
    end

        

let check_sat ?(session_name="form") ?(sat_means="sat") f =
  let result, session, f_inst = prove session_name sat_means f in
  (match result with
  | Some true -> dump_model session f_inst
  | Some false -> dump_core session
  | _ -> ());
  SmtLibSolver.quit session;
  result

let get_model ?(session_name="form") ?(sat_means="sat") f =
  let result, session, f_inst = prove session_name sat_means f in
  let model = 
    match result with
    | Some true | None ->
        dump_model session f_inst;
        SmtLibSolver.get_model session
    | Some false -> 
        dump_core session;
        None
  in
  SmtLibSolver.quit session;
  Util.Opt.map Model.complete model
