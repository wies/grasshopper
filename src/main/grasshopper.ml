(** Main module of GRASShopper *)

open Util
    
let greeting =
  "GRASShopper version " ^ Config.version ^ "\n"
                                              
let usage_message =
  greeting ^
  "\nUsage:\n  " ^ Sys.argv.(0) ^ 
  " <input file> [options]\n"

let cmd_line_error msg =
  Arg.usage (Arg.align Config.cmd_options) usage_message;
  failwith ("Command line option error: " ^ msg)

(** Output JSON file with error trace *)
let output_trace prog proc (pp, model) =
  if !Config.trace_file = "" then () else
  begin
    let trace = Verifier.get_trace prog proc (pp, model) in
    (* print trace to trace file in JSON format *)
    let trace_chan = open_out !Config.trace_file in
    let print_pos (pos, state) =
      Printf.fprintf trace_chan 
        "{\"position\": {\"line_no\": %d, \"column_no_start\": %d, \"column_no_stop\": %d}, \"state\": "
        pos.Grass.sp_start_line pos.Grass.sp_start_col pos.Grass.sp_end_col;
      Model.output_json trace_chan state;
      output_string trace_chan "}"
    in
    output_string trace_chan "[";
    Util.output_list trace_chan print_pos ",\n" trace;
    output_string trace_chan "]\n";
    close_out trace_chan     
  end

(** Parse compilation unit in file [file] using parsing function [parse_fct] *)
let parse_cu parse_fct file =
  let input = read_file file in
  ParseError.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  SplLexer.set_file_name lexbuf file; 
  parse_fct lexbuf

(** normalize the filenames to avoid double inclusion *)
let normalizeFilename file_name =
  let sep = Str.regexp_string Filename.dir_sep in
  let parts = Str.split sep file_name in
  let rec simplify parts = match parts with
    | x :: ".." :: xs when x <> ".." -> simplify xs
    | x :: xs -> x :: (simplify xs)
    | [] -> []
  in
  let remaining = simplify parts in
  String.concat Filename.dir_sep remaining

(** Parse SPL program in main file [main_file] *)
let parse_spl_program main_file =
  let rec parse parsed to_parse spl_prog =
    match to_parse with
    | (file, pos) :: to_parse1 ->
        let file = normalizeFilename file in
        if not (StringSet.mem file parsed) then
          begin
            Debug.debug (fun () -> "parsing: " ^ file ^ "\n");
            let cu = 
              try 
                parse_cu (fun lexbuf -> SplParser.main SplLexer.token lexbuf) file 
              with Sys_error _ ->
                ProgError.error pos ("Could not find file " ^ file)
            in
            let dir = 
              if file = main_file
              then !Config.base_dir
              else Filename.dirname file 
            in
            let parsed1 = StringSet.add file parsed in
            let to_parse2 =
              List.fold_left (fun acc (incl, pos) -> 
                let file = dir ^ Filename.dir_sep ^ incl in
                if StringSet.mem file parsed1 then acc else (file, pos) :: acc)
                to_parse1 cu.SplSyntax.includes 
            in
            parse parsed1 to_parse2 (SplSyntax.merge_spl_programs spl_prog cu)
          end
        else
          begin
            Debug.debug (fun () -> "already included: " ^ file ^ "\n");
            parse parsed to_parse1 spl_prog
          end
    | [] -> spl_prog
  in
  let prog =
    parse
      StringSet.empty
      [(main_file, GrassUtil.dummy_position)]
      SplSyntax.empty_spl_program
  in
  SplSyntax.add_alloc_decl prog

(** Locust: work in progress *)
let locust spl_prog simple_prog proc errors =
  let process_error (error_pos, error_msg, model) =
    let error_msg = List.hd (Str.split (Str.regexp "\n") error_msg) in
    Locust.print_debug ("Found error on line "
			^ (string_of_int error_pos.Grass.sp_start_line)
			^ ": " ^ error_msg);
    (* If error is inside loop then neg sample *)
    if Locust.is_auto_loop_proc proc
    then begin
	Locust.print_debug "Geting negative model from inside loop";
	let neg_model =
	  Locust.get_model_at_src_pos simple_prog proc (error_pos, model) !Locust.loop_pos
	in
	let out_filename = Locust.get_new_model_filename false in
	let out_chan = open_out out_filename in
	Model.output_txt out_chan neg_model;
	close_out out_chan;
	Locust.print_debug ("Dumped model in file " ^ out_filename);
      end
    else
      if error_pos.Grass.sp_start_line < !Locust.loop_pos.Grass.sp_start_line
      then
	begin
	  (* Assuming precondition =/> invariant. get positive model *)
	  Locust.print_debug "Geting positive model";
	  (* TODO need session or something to get multiple models *)
	  (* TODO what format to get the model in? TODO store models in ref *)
	  (* For now dumping model to file and storing filename in ref *)
	  let out_filename = Locust.get_new_model_filename true in
	  let out_chan = open_out out_filename in
	  Model.output_txt out_chan model;
	  close_out out_chan;
	  Locust.print_debug ("Dumped model in file " ^ out_filename);
	end
      else
	begin
	  (* Error occured after loop, get negative model *)
	  Locust.print_debug "Geting negative model";
	  let neg_model =
	    Locust.get_model_at_src_pos
	      simple_prog proc (error_pos, model)
	      {!Locust.loop_pos with
		Grass.sp_start_line = !Locust.loop_pos.Grass.sp_start_line + 1}
	  in
	  let out_filename = Locust.get_new_model_filename false in
	  let out_chan = open_out out_filename in
	  Model.output_txt out_chan neg_model;
	  close_out out_chan;
	  Locust.print_debug ("Dumped model in file " ^ out_filename);
	end
    (* TODO what to do if it's not inductive *)
  in
  process_error (List.hd errors)
  (* TODO fix model bug and do this instead: List.iter process_error errors *)
  (* Learn invariant from samples (call predictor, filter results, etc) *)

  (* Instrument program and call check_prog again *)

(** Check SPL program in main file [file] and procedure [proc] *)
let check_spl_program file proc =
  let spl_prog = parse_spl_program file in
  let prog = SplTranslator.to_program spl_prog in
  let simple_prog = Verifier.simplify prog in
  let check simple_prog proc =
    if !Config.locust then
      if not (Locust.is_auto_loop_proc proc) then
	begin
	  Locust.print_debug ("starting on procedure "
			      ^ (Grass.string_of_ident proc.Prog.proc_name));
	  (* First find source pos of loop/loop invariant *)
	  Locust.init_refs spl_prog proc;
	end;
    let errors = Verifier.check_proc simple_prog proc in
    if !Config.locust
    then locust spl_prog simple_prog proc errors
    else
    List.iter 
      (fun (pp, error_msg, model) ->
        output_trace simple_prog proc (pp, model);
        if !Config.robust 
        then ProgError.print_error pp error_msg
        else ProgError.error pp error_msg;
      )
      errors
  in
  match proc with
  | None -> Prog.iter_procs check simple_prog
  | Some p ->
    let procs =
      Prog.find_proc_with_deps simple_prog (p, 0)
    in
    if procs = [] then begin
      let available =
        Prog.fold_procs 
          (fun acc proc -> "\t" ^ Grass.string_of_ident proc.Prog.proc_name ^ "\n" ^ acc) 
          "" prog
      in
      failwith ("Could not find a procedure named " ^ p ^ 
                ". Available procedures are:\n" ^ available)
    end;
    List.iter (check simple_prog) procs


(** Get current time *)
let current_time () =
  let ptime = Unix.times () in
  ptime.Unix.tms_utime +. ptime.Unix.tms_cutime  

(** Print statistics *)
let print_stats start_time =
  if !Config.print_stats then
    let end_time = current_time () in
    let total_time = end_time -. start_time in
    print_endline "Statistics: ";
    Printf.printf "  running time for analysis: %.2fs\n" total_time;
    Printf.printf "  # VCs: %d\n" !SmtLibSolver.num_of_sat_queries;
    Printf.printf "  measured time: %.2fs\n" !Util.measured_time;
    Printf.printf "  # measured calls: %.2d\n" !Util.measured_calls

(** Main entry of GRASShopper *)
let _ =
  let main_file = ref "" in
  let set_main_file s =
    main_file := s;
    if !Config.base_dir = "" 
    then Config.base_dir := Filename.dirname s
  in
  let start_time = current_time () in
  try
    Arg.parse Config.cmd_options set_main_file usage_message;
    Debug.info (fun () -> greeting);
    SmtLibSolver.select_solver (String.uppercase !Config.smtsolver);
    if !main_file = ""
    then cmd_line_error "input file missing"
    else begin
      check_spl_program !main_file !Config.procedure;
      print_stats start_time 
    end
  with  
  | Sys_error s -> 
      let bs = if Debug.is_debug 0 then Printexc.get_backtrace () else "" in
      output_string stderr ("Error: " ^ s ^ "\n" ^ bs); exit 1
  | Failure s ->
      let bs = if Debug.is_debug 0 then Printexc.get_backtrace () else "" in
      output_string stderr ("Error: " ^ s ^ "\n" ^ bs); exit 1
  | Parsing.Parse_error -> 
      print_endline "parse error"; 
      exit 1
  | ProgError.Prog_error _ as e ->
      output_string stderr (ProgError.to_string e ^ "\n");
      exit 1


(** Given a model and an SL formula, constructs an spl program that checks if the assertion holds for the given model *)
let assert_formula_about_model () =
  let store, heap = Locust.read_heap_from_chan stdin in

  (* Temp hack to include the linked list definitions *)
  let spl_prog = parse_spl_program "tests/spl/include/sllist.spl" in

  (* add model and TODO assertion procedure to this program *)
  let spl_prog = Locust.add_model_to_prog (store, heap) spl_prog in


  (* This part copied from Grasshopper.check_spl_program: *)
  let prog = SplTranslator.to_program spl_prog in
  (* DEBUG print and check *)
  if (Debug.is_debug (-1)) then
    Prog.print_prog stdout prog;

  let simple_prog = Verifier.simplify prog in
  let check simple_prog proc =
    let errors = Verifier.check_proc simple_prog proc in
    List.iter
      (fun (pp, error_msg, model) ->
	ProgError.error pp error_msg;
      )
      errors
  in
  Prog.iter_procs check simple_prog
