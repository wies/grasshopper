open Grass
open GrassUtil
open Util
open Axioms

let inst_num = ref 0

let dump_model session f =
  if !Config.model_file <> "" then begin
    let gts = ground_terms ~include_atoms:true f in
    let model = Opt.get (SmtLibSolver.get_model session) in
    let model_chan = open_out !Config.model_file in
    (*Model.print_model2 model;*)
    Model.output_graphviz model_chan (Model.complete model) gts;
    close_out model_chan;
  end;
  if !Config.model_txt_file <> "" then
    begin
      let gts = ground_terms f in
      let model = Model.complete (Opt.get (SmtLibSolver.get_model session)) in
      let model_chan = open_out !Config.model_txt_file in
      Model.output_txt model_chan model gts;
      close_out model_chan;

      (* Also output the dot file *)
      Config.model_null_edge := true;
      let model_chan = open_out (!Config.model_txt_file ^ ".dot") in
      Model.output_graphviz model_chan model gts;
      close_out model_chan;

      (* Try to get more models *)
      let equalities_list = Model.find_equalities model gts in
      Printf.printf "\n\nDumping models to file:\nOriginal model in file %s\n"
		    !Config.model_txt_file;

      let get_model_for_equality (model_num, session) eq =
	let session = SmtLibSolver.push session in
	Printf.printf "Trying to get a model for %s..." (string_of_form (mk_not eq));
	SmtLibSolver.assert_form session (mk_not eq);
	let result = Opt.get (SmtLibSolver.is_sat session) in
	if result then
	  begin
	    let file_name = (!Config.model_txt_file ^ (string_of_int model_num)) in
	    Printf.printf "found. Model in %s\n" file_name;
	    let model = Model.complete (Opt.get (SmtLibSolver.get_model session)) in
	    let model_chan = open_out file_name in
	    Model.output_txt model_chan model gts;
	    close_out model_chan;

	    (* Also output the dot file *)
	    let model_chan = open_out (file_name ^ ".dot") in
	    Model.output_graphviz model_chan model gts;
	    close_out model_chan;

	    (model_num+1, SmtLibSolver.pop session)
	  end
	else
	  begin
	    Printf.printf "nope.\n";
	    (model_num, SmtLibSolver.pop session)
	  end
      in
      let _ = List.fold_left get_model_for_equality (1, session) equalities_list in
      (* Check sat again, otherwise next call to get_model fails *)
      let _ = SmtLibSolver.is_sat session in
      ()
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

let print_query name sat_means f =
  let f_inst = Reduction.reduce f in
  let f_inst =
    if !Config.named_assertions then
      let f_inst = List.rev_map unique_names f_inst in
      let f_inst = List.rev_map name_unnamed f_inst in
      f_inst
    else f_inst
  in
  let signature = overloaded_sign (mk_and f_inst) in
  let session = SmtLibSolver.start name sat_means in
  Debug.debug (fun () -> "Sending to prover...\n");
  let session = SmtLibSolver.declare session signature in
  SmtLibSolver.assert_forms session f_inst;
  session, f_inst


let start_session name sat_means f = 
  let session, f_inst = print_query name sat_means f in
  let prove session =
    let result = SmtLibSolver.is_sat session in
    Debug.debug (fun () -> "prover done\n");
    (result, session)
  in
  (*Util.measure_call "prove" prove session*)
  let result, session = prove session in
  result, session, mk_and f_inst

let check_sat ?(session_name="form") ?(sat_means="sat") f =
  let result, session, f_inst = start_session session_name sat_means f in
  (match result with
  | Some true -> dump_model session f_inst
  | Some false -> dump_core session
  | _ -> ());
  SmtLibSolver.quit session;
  result

let get_model ?(session_name="form") ?(sat_means="sat") f =
  let result, session, f_inst = start_session session_name sat_means f in
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
