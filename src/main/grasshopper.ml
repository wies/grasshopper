(** Main module of GRASShopper *)

open Util
open SplCompiler
    
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
      ModelPrinting.output_json trace_chan state;
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
let normalizeFilename base_dir file_name =
  let fullname =
    if Filename.is_relative file_name then
      base_dir ^ Filename.dir_sep ^ file_name
    else
      file_name
  in
  let sep = Str.regexp_string Filename.dir_sep in
  let parts = Str.split_delim sep fullname in
  let remaining =
    List.fold_left
      (fun acc -> function
        | "" when acc <> [] -> acc
        | ".." -> List.tl acc
        | x -> x :: acc
      )
      []
      parts
  in
  String.concat Filename.dir_sep (List.rev remaining)

(** Parse SPL program in main file [main_file] *)
let parse_spl_program main_file =
  let rec parse parsed to_parse spl_prog =
    match to_parse with
    | (dir, file, pos) :: to_parse1 ->
        if not (StringSet.mem file parsed) then
          begin
            Debug.debug (fun () -> "parsing: " ^ file ^ "\n");
            let cu = 
              try 
                parse_cu (fun lexbuf -> SplParser.main SplLexer.token lexbuf) file 
              with Sys_error _ ->
                ProgError.error pos ("Could not find file " ^ file)
            in
            let parsed1 = StringSet.add file parsed in
            let to_parse2 =
              List.fold_left
                (fun acc (incl, pos) ->
                  let incl2 = normalizeFilename dir incl in
                  let dir2 = Filename.dirname incl2 in
                  (dir2, incl2, pos) :: acc)
                to_parse1
                cu.SplSyntax.includes 
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
  let norm_dir = normalizeFilename (Unix.getcwd ()) !Config.base_dir in
  let main_file = normalizeFilename norm_dir main_file in
  let main_dir  =
    if !Config.base_dir <> "" then norm_dir
    else Filename.dirname main_file
  in
  let prog =
    parse
      StringSet.empty
      [(main_dir, main_file, GrassUtil.dummy_position)]
      SplSyntax.empty_spl_program
  in
  SplChecker.check (SplSyntax.add_alloc_decl prog)

   
(** Check SPL program in main file [file] and procedure [proc] *)
let check_spl_program spl_prog proc =
  let prog = SplTranslator.to_program spl_prog in
  let simple_prog = Verifier.simplify prog in
  let check simple_prog first proc =
    let errors =
      if !Config.typeonly then []
      else Verifier.check_proc simple_prog proc
    in
    List.fold_left
      (fun first (pp, error_msg, model) ->
        output_trace simple_prog proc (pp, model);
        let _ =
          if !Config.robust
          then begin
            (if not first then print_newline ());
            ProgError.print_error pp error_msg
          end
          else ProgError.error pp error_msg
        in
        false
      )
      first errors
  in
  match proc with
  | None -> Prog.fold_procs (check simple_prog) true simple_prog
  | Some p ->
    let procs =
      Prog.find_proc_with_deps simple_prog (p, 0)
    in
    if procs = [] then begin
      let available =
        Prog.fold_procs 
          (fun acc proc ->
            let name = Prog.name_of_proc proc in
            "\t" ^ Grass.string_of_ident name ^ "\n" ^ acc) 
          "" prog
      in
      failwith ("Could not find a procedure named " ^ p ^ 
                ". Available procedures are:\n" ^ available)
    end;
    List.fold_left (check simple_prog) true procs


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

(** Print C program equivalent *)
let print_c_program spl_prog =
  if !Config.compile_to <> "" then begin
    let oc = open_out !Config.compile_to in
    SplCompiler.compile oc spl_prog;
    close_out oc;
  end else 
    ()

(** Main entry of GRASShopper *)
let _ =
  let main_file = ref "" in
  let set_main_file s =
    main_file := s;
  in
  let start_time = current_time () in
  try
    Arg.parse Config.cmd_options set_main_file usage_message;
    if !Config.unsat_cores then Config.named_assertions := true;
    Debug.info (fun () -> greeting);
    SmtLibSolver.select_solver (String.uppercase_ascii !Config.smtsolver);
    if !main_file = ""
    then cmd_line_error "input file missing"
    else begin
      let spl_prog = parse_spl_program !main_file in
      let res = check_spl_program spl_prog !Config.procedure in
      print_stats start_time; 
      print_c_program spl_prog;
      if !Config.verify && res then
        Debug.info (fun () -> "Program successfully verified.\n")
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
	
