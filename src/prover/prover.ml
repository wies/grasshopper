open Grass
open GrassUtil
open Util
open Axioms
open InstGen

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

(** Generate local instances of all axioms of [fs] in which variables occur below function symbols *)
let instantiate_and_prove session fs =
  let fs1 = encode_labels fs in
  let signature = overloaded_sign (mk_and fs1) in
  let session = SmtLibSolver.declare session signature in
  let rename_forms fs =
    if !Config.named_assertions then
      let fs = List.rev_map unique_names fs in
      let fs = List.rev_map name_unnamed fs in
      fs
    else fs
  in
  (*let terms_from_neg_assert fs =
    let has_label = List.exists (function Label _ -> true | _ -> false) in
    let rec process_form terms = function
      | Atom (_, anns) as f ->
          if has_label anns then
            ground_terms ~include_atoms:true f |> TermSet.union terms
          else terms
      | BoolOp (_, fs) -> process_forms terms fs
      | Binder (_, _, f1, anns) as f ->
          if has_label anns then
            ground_terms ~include_atoms:true f |> TermSet.union terms
          else process_form terms f1
    and process_forms terms fs = List.fold_left process_form terms fs
    in
    process_forms TermSet.empty fs
  in*)
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
  let fs1, generators = open_axioms isFunVar fs1 in
  let btwn_gen = btwn_field_generators fs in
  let gts = ground_terms ~include_atoms:true (mk_and fs) in
  let gts1 = generate_terms (btwn_gen @ generators) gts in
  let classes = CongruenceClosure.congr_classes fs gts1 in
  let round1 fs_inst gts_inst classes =
    let equations = List.filter (fun f -> is_horn false [f]) fs_inst in
    let ground_fs = List.filter is_ground fs_inst in
    let eqs = instantiate_with_terms true equations classes in
    let gts1 = TermSet.union (ground_terms ~include_atoms:true (mk_and eqs)) gts_inst in 
    let classes = CongruenceClosure.congr_classes (List.rev_append eqs fs) gts1 in
    let implied =
      List.fold_left
        (fun acc -> function
        | c :: cls when sort_of c <> Bool && sort_of c <> Pat -> 
            let eq = List.map (fun t -> GrassUtil.mk_eq c t) cls in
            List.rev_append eq acc
        | _ -> acc)
        []
      classes
    in
    rev_concat [eqs; ground_fs; implied], gts1, classes
  in
  let round2 fs_inst gts_inst classes =
    (* the following seemingly redundant instantiation round is a workaround for not using the -fullep option *)
    let fs2 = instantiate_with_terms ~stratify:false true fs1 classes in
    let gts_inst = generate_terms generators (TermSet.union gts_inst (ground_terms ~include_atoms:true (mk_and fs2))) in
    let core_terms =
      let gts_a = (*terms_from_neg_assert*) ground_terms (mk_and fs) in
      TermSet.fold (fun t acc ->
        match sort_of t with
        | Loc _ | Int -> TermSet.add (mk_known t) acc
        | _ -> acc)
        gts_a TermSet.empty
    in
    let gts2 = generate_terms (btwn_gen @ generators) (TermSet.union gts_inst core_terms) in
    let _ =
      if Debug.is_debug 1 then
        begin
          print_endline "ground terms:";
          TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) gts;
          print_endline "generated terms:";
        TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) (TermSet.diff gts2 gts)
      end
    in
    if TermSet.subset gts2 gts_inst
    then fs2, gts_inst, classes
    else
    let classes = CongruenceClosure.congr_classes (rev_concat [fs_inst; fs]) gts2 in
    instantiate_with_terms ~stratify:true true fs1 classes, gts2, classes
  in
  let round3 fs_inst gts_inst classes =
    let generators =
      List.map (fun (ms, ts) ->
        let ms1 =
          List.filter (function
            | Match (App (Known, [t], _), _) ->
                (match sort_of t with
                | Int | Loc _ -> false
                | _ -> true)
            | _ -> true)
            ms
        in (ms1, ts))
        generators
    in
    let gts_inst = generate_terms (btwn_gen @ generators) (TermSet.union (ground_terms ~include_atoms:true (mk_and fs_inst)) gts_inst) in
    let classes = CongruenceClosure.congr_classes (rev_concat [fs_inst; fs]) gts_inst in
    instantiate_with_terms true fs1 classes, gts_inst, classes
  in
  let do_rounds rounds =
    let dr (k, result, fs_asserted, fs_inst, gts_inst, classes) r =
    match result with
    | Some true | None ->
        let fs_inst1, gts_inst1, classes1 = r fs_inst gts_inst classes in
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
        SmtLibSolver.assert_forms session fs_inst1_assert;
        Debug.debug (fun () -> Printf.sprintf "Calling SMT solver in instantiation round %d...\n" k);
        let result1 = SmtLibSolver.is_sat session in
        Debug.debug (fun () -> "Solver done.\n");
        k + 1, result1, fs_asserted1, fs_inst1, gts_inst1, classes1
    | _ -> k, result, fs_asserted, fs_inst, gts_inst, classes
    in List.fold_left dr (1, None, FormSet.empty, fs1, gts1, classes) rounds
  in
  let _, result, _, fs_inst, _, _ = do_rounds [round1; round2(*; round3*)] in
  result, session, fs_inst


let prove name sat_means f = 
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
      Model.output_html model_chan (Model.complete model) gts
    else
      Model.output_graph model_chan (Model.complete model) gts;
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
        let signature = overloaded_sign (mk_and core) in
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
      let config = !Config.dump_smt_queries in
      Config.dump_smt_queries := true;
      let s = SmtLibSolver.start core_name session.SmtLibSolver.sat_means in
      let signature = overloaded_sign (mk_and core) in
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
