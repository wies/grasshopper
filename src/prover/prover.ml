open Form
open FormUtil
open Util
open Axioms

let inst_num = ref 0

let dump_model session =
  if !Config.model_file <> "" then begin
    let _model = unopt (SmtLibSolver.get_model session) in
    let model = Model.empty in
    let model_chan = open_out !Config.model_file in
    Model.print_model2 model;
    Model.output_graphviz model_chan model;
    close_out model_chan;
  end

let dump_core session =
  if !Config.unsat_cores then
    begin
      let core_name = session.SmtLibSolver.name ^ ".core" in
      (*repeat in a fixed point in order to get a smaller core*)
      let rec minimize core =
        Debug.info (fun () -> "minimizing core " ^ (string_of_int (List.length core)) ^ "\n");
        let s = SmtLibSolver.start core_name session.SmtLibSolver.sat_means in
        let signature = overloaded_sign (mk_and core) in
        let s = SmtLibSolver.declare s signature in
        SmtLibSolver.assert_forms s core;
        let core2 = unopt (SmtLibSolver.get_unsat_core s) in
        SmtLibSolver.quit s;
        if List.length core2 < List.length core
        then minimize core2
        else core
      in
      let core = unopt (SmtLibSolver.get_unsat_core session) in
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
  let f_inst = List.rev (List.rev_map comment_uncommented f_inst) in
  let f_inst = List.rev (List.rev_map unique_comments f_inst) in
  let signature = overloaded_sign (mk_and f_inst) in
  let session = SmtLibSolver.start name sat_means in
    Debug.debug (fun () -> "sending to prover...\n");
    let session = SmtLibSolver.declare session signature in
    SmtLibSolver.assert_forms session f_inst;
    session


let start_session name sat_means f = 
  let session = print_query name sat_means f in
  let prove session =
    let result = SmtLibSolver.is_sat session in
    Debug.debug (fun () -> "prover done\n");
    (result, session)
  in
    Util.measure_call "prove" prove session

let check_sat ?(session_name="form") ?(sat_means="sat") f =
  let result, session = start_session session_name sat_means f in
  (match result with
  | Some true -> dump_model session
  | Some false -> dump_core session
  | _ -> ());
  SmtLibSolver.quit session;
  result

