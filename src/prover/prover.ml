open Form
open FormUtil
open Util
open Axioms

let inst_num = ref 0

let dump_model session =
  if !Config.model_file <> "" then begin
    let model = unopt (SmtLib.get_model session) in
    let model_chan = open_out !Config.model_file in
    Model.print_model2 model;
    Model.output_graphviz model_chan model;
    close_out model_chan;
  end

let dump_core session =
  if !Config.unsat_cores then
    begin
      let core = unopt (SmtLib.get_unsat_core session) in
      let core_name = session.SmtLib.name ^ ".core" in
      let config = !Config.dump_smt_queries in
      Config.dump_smt_queries := true;
      let s = SmtLib.start core_name in
      let signature = overloaded_sign (mk_and core) in
      let s = SmtLib.declare s signature in
      SmtLib.assert_forms s core;
      SmtLib.quit s;
      Config.dump_smt_queries := config
    end

let print_query name f =
  let f_inst = Reduction.reduce f in
  let f_inst = List.rev (List.rev_map comment_uncommented f_inst) in
  let f_inst = List.rev (List.rev_map unique_comments f_inst) in
  let signature = overloaded_sign (mk_and f_inst) in
  let session = SmtLib.start name in
    Debug.debug (fun () -> "sending to prover...\n");
    let session = SmtLib.declare session signature in
    SmtLib.assert_forms session f_inst;
    session


let start_session name f = 
  let session = print_query name f in
  let prove session =
    let result = SmtLib.is_sat session in
    Debug.debug (fun () -> "prover done\n");
    (result, session)
  in
    Util.measure_call "prove" prove session

let check_sat ?(session_name="form") f =
  let result, session = start_session session_name f in
  (match result with
  | Some true -> dump_model session
  | Some false -> dump_core session
  | _ -> ());
  SmtLib.quit session;
  result

