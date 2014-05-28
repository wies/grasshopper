(** SMT-LIB 2 interface *)

open Logger
open Form
open FormUtil
open ParseSmtLibAux

let logger = Logging.smtlib_log

let num_of_sat_queries = ref 0

(* Todo: add proper error handling *)

(** Solvers *)

type solver_version = 
    { number : int;
      subnumber : int;
      smt_options : (string * bool) list;
      args : string
    }

type solver = 
    { name : string;
      cmnd : string;
      version : solver_version
    }
      

let z3_v3 = { number = 3;
	      subnumber = 2;
	      smt_options = [":mbqi", true;
			 ":MODEL_V2", true;
			 ":MODEL_PARTIAL", true;
			 ":MODEL_HIDE_UNUSED_PARTITIONS", true];
	      args = "-smt2 -in"
	    }

let z3_v4 = { number = 4;
	      subnumber = 3;
	      smt_options = 
              (if not !Config.instantiate then [(":auto-config", false)] else []) @
              [":smt.mbqi", true;
               ":smt.ematching", true;
               ":model.v2", true;
	       ":model.partial", true];
	      args = "-smt2 -in"
	    }

let z3_versions = [z3_v4; z3_v3]

let z3 = 
  let cmnd = "z3" in
  let version = 
    try 
      let in_chan = Unix.open_process_in (cmnd ^ " -version") in
      let version_regexp = Str.regexp "^Z3[^0-9]*\\([0-9]*\\).\\([0-9]*\\)" in
      let version_string = input_line in_chan in
      ignore (Str.string_match version_regexp version_string 0);
      let number = int_of_string (Str.matched_group 1 version_string) in
      let subnumber = int_of_string (Str.matched_group 2 version_string) in
      let _ = Unix.close_process_in in_chan in
      List.find (fun v -> v.number < number || (v.number = number && v.subnumber <= subnumber)) z3_versions
    with _ -> log logger WARN (fun () -> "No supported version of Z3 found.", []);
      z3_v3	
  in 
  { name = "Z3";
    cmnd = cmnd;
    version = version }

let cvc4_v1 = {	number = 1;
		subnumber = 0;
		smt_options = [];
		args = "--lang=smt2";
	      } 

let cvc4 = 
  { name = "CVC4";
    cmnd = "cvc4";
    version = cvc4_v1 }

let mathsat_v5 = { number = 5;
		   subnumber = 1;
		   smt_options = [];
		   args = "-verbosity=0";
	         }

let mathsat = 
  { name = "MathSAT";
    cmnd = "mathsat";
    version = mathsat_v5
   }
 
let solvers = [z3; cvc4; mathsat]

let selected_solver = ref z3

let select_solver name = 
  try
    selected_solver := List.find (fun s -> s.name = name) solvers
  with Not_found -> failwith ("Unsupported SMT solver '" ^ name ^ "'")

(** SMT-LIB2 Sessions *)
   
type session = { name: string;
                 sat_means: string;
		 in_chan: in_channel;
		 out_chan: out_channel;
		 replay_chan: out_channel option;
		 mutable assert_count: int;
		 mutable sat_checked: bool option;
		 stack_height: int;
                 signature: (arity list SymbolMap.t) option;
                 named_clauses: (string, form) Hashtbl.t option
	       }

exception SmtLib_error of session * string
    
let fail session msg = raise (SmtLib_error (session, "SmtLib: " ^ msg))
      
let write session cmd =
  if !Config.verify then output_string session.out_chan cmd;
  match session.replay_chan with
  | Some chan -> output_string chan cmd; flush chan
  | None -> ()	

let writefn session fn =
  if !Config.verify then fn session.out_chan;
  match session.replay_chan with
  | Some chan -> fn chan; flush chan
  | None -> ()

let writeln session cmd = 
  write session (cmd ^ "\n")  
   
let read session = 
  if !Config.verify then begin
    flush session.out_chan;
    let lexbuf = Lexing.from_channel session.in_chan in
    ParseSmtLib.main LexSmtLib.token lexbuf
  end
  else SmtUnsat

let set_option session opt_name opt_value =
  writeln session (Printf.sprintf "(set-option %s %b)" opt_name opt_value)

let set_logic session logic =
  writeln session ("(set-logic " ^ logic ^ ")")

let declare_fun session sym_name arg_sorts res_sort =
  let arg_sorts_str = String.concat " " (List.map (fun srt -> string_of_sort srt) arg_sorts) in
  writeln session ("(declare-fun " ^ sym_name ^ " (" ^ arg_sorts_str ^ ") " ^ string_of_sort res_sort ^ ")")

let declare_sort session sort_name num_of_params =
  writeln session (Printf.sprintf "(declare-sort %s %d)" sort_name num_of_params)
    
let declare_sorts has_int session =
  declare_sort session loc_sort_string 0;
  if !Config.backend_solver_has_set_theory then begin
    writeln session ("(define-sort " ^ set_sort_string ^ loc_sort_string ^ " () (Set " ^ loc_sort_string ^ "))");
    if has_int then 
      writeln session ("(define-sort " ^ set_sort_string ^ int_sort_string ^ " () (Set " ^ int_sort_string ^ "))")
  end else begin
    declare_sort session (set_sort_string ^ loc_sort_string) 0;
    if has_int then declare_sort session (set_sort_string ^ int_sort_string) 0
  end;
  if !Config.encode_fields_as_arrays then
    writeln session ("(define-sort " ^ fld_sort_string ^ " (X) (Array Loc X))")
  else 
    begin
      declare_sort session (fld_sort_string ^ bool_sort_string) 0;
      declare_sort session (fld_sort_string ^ loc_sort_string) 0;
      if has_int then declare_sort session (fld_sort_string ^ int_sort_string) 0
    end

let start_with_solver = 
  let get_replay_chan name =
    if !Config.dump_smt_queries then
      (* these files should probably go into the tmp directory *)
      let with_version = fresh_ident name in
      let replay_file =  (str_of_ident with_version) ^ ".smt2" in
      Some (open_out replay_file)
    else None
  in
  fun session_name sat_means solver produce_models produce_unsat_cores ->
  let smt_cmd = solver.cmnd ^ " " ^ solver.version.args in
  let in_chan, out_chan = Unix.open_process smt_cmd in
  let names_tbl: (string, form) Hashtbl.t option =
    if produce_unsat_cores then Some (Hashtbl.create 0) else None
  in
  let session = { name = session_name;
                  sat_means = sat_means;
		  in_chan = in_chan; 
		  out_chan = out_chan;
		  replay_chan = get_replay_chan session_name;
		  assert_count = 0;
                  sat_checked = None;
		  stack_height = 0;
                  signature = None;
                  named_clauses = names_tbl }
  in
  set_option session ":print-success" false;
  if produce_models then 
    set_option session  ":produce-models" true;
  List.iter 
    (fun (opt, b) -> set_option session opt b)
    solver.version.smt_options;
  if produce_unsat_cores then
    set_option session ":produce-unsat-cores" true;
  session


let init_session session sign =
  let has_int = 
    let rec hi = function
      | Int -> true
      | Set srt
      | Fld srt -> hi srt
      | _ -> false
    in
    SymbolMap.exists 
      (fun _ variants -> 
        List.exists (fun (arg_srts, res_srt) -> List.exists hi (res_srt :: arg_srts))
          variants)
      sign
  in
  let logic_str = 
    if !Config.encode_fields_as_arrays then "A" else "" ^
    "UF" ^
    if has_int then "LIA" else "" ^
    if !Config.backend_solver_has_set_theory then "_SETS" else ""
  in set_logic session logic_str;
  if !Config.dump_smt_queries then begin
    writeln session ("(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:\n  " ^ session.sat_means ^ "
  |)");
    writeln session ("(set-info :smt-lib-version 2.0)");
    writeln session ("(set-info :category \"crafted\")");
    writeln session ("(set-info :status \"unknown\")");
  end;
  writeln session "";
  declare_sorts has_int session

let start session_name sat_means =
  start_with_solver
    session_name
    sat_means
    !selected_solver
    (!Config.model_file <> "")
    !Config.unsat_cores
        
let quit session = 
  writeln session "(exit)";
  close_out session.out_chan;
  close_in session.in_chan;
  (match session.replay_chan with
  | Some chan -> close_out chan
  | None -> ());
  ignore (Unix.close_process (session.in_chan, session.out_chan))
    
let pop session = 
  if session.stack_height <= 0 then fail session "pop on empty stack" else
  writeln session "(pop 1)";
  let new_session = { session with stack_height = session.stack_height - 1 } in
  new_session

let push session = 
  writeln session "(push 1)";
  let new_session = { session with stack_height = session.stack_height + 1 } in
  new_session

let is_interpreted sym = match sym with
  | Read | Write -> !Config.encode_fields_as_arrays
  | Empty | SetEnum | Union | Inter | Diff | Elem | SubsetEq ->
      !Config.backend_solver_has_set_theory
  | Eq | Gt | Lt | GtEq | LtEq | IntConst _ | BoolConst _
  | Plus | Minus | Mult | Div | UMinus -> true
  | _ -> false

let string_of_symbol sym idx =
  (str_of_symbol sym) ^ "$" ^ (string_of_int idx)

let declare session sign =
  let declare sym idx (arg_sorts, res_sort) = 
    let sym_str = string_of_symbol sym idx in
    declare_fun session sym_str arg_sorts res_sort
  in
  let write_decl sym overloaded_variants = 
    if not (is_interpreted sym) then
      begin
        match overloaded_variants with
        | [] -> failwith ("missing sort for symbol " ^ str_of_symbol sym)
        | _ -> Util.iteri (declare sym) overloaded_variants
      end
  in
  init_session session sign;
  SymbolMap.iter write_decl sign;
  writeln session "";
  { session with signature = Some sign }

let disambiguate_overloaded_symbols signs f =
  let osym sym sign =
    if is_interpreted sym 
    then sym
    else
      let versions = 
        try SymbolMap.find sym signs 
        with Not_found -> [] 
      in
      try
        let version = Util.find_index sign versions in
        FreeSym (mk_ident (string_of_symbol sym version))
      with Not_found -> sym
  in
  let rec over t = match t with
    | Var _ as v -> v
    | App (sym, ts, srt) ->
      let ts = List.map over ts in
      let args_srt = List.map sort_of ts in
        App (osym sym (List.map Util.unopt args_srt, Util.unopt srt), ts, srt)
  in
  map_terms over f

let assert_form session f =
  let _ = match f with
    | Binder (_, _, _, ann) ->
      begin
        let name = extract_comments true ann in
          match session.named_clauses with
          | Some tbl -> Hashtbl.add tbl name f
          | None -> ()
      end
    | _ -> ()
  in
  session.assert_count <- session.assert_count + 1;
  session.sat_checked <- None;
  write session "(assert ";
  let cf = 
    match session.signature with
    | None -> failwith "tried to assert formula before declaring symbols"
    | Some sign -> disambiguate_overloaded_symbols sign f 
  in
  writefn session (fun chan -> print_smtlib_form chan cf);
  writeln session ")\n"
    
(*let assert_form session f = Util.measure (assert_form session) f*)
    
let assert_forms session fs =
  List.iter (fun f -> assert_form session f) fs

    
let is_sat session = 
  incr num_of_sat_queries;
  writeln session "(check-sat)";
  match read session with
  | SmtSat -> 
    session.sat_checked <- Some true;
    Some true
  | SmtUnsat ->
    session.sat_checked <- Some false;
    Some false
  | SmtUnknown ->
    session.sat_checked <- Some true;
    None
  | SmtError e -> fail session e
  | _ -> fail session "unexpected response of prover"
	
let get_model session = 
  let gm () =
    writeln session "(get-model)";
    match read session with
    | SmtModel m -> Some m
    | SmtError e -> fail session e
    | _ -> None
  in
    if session.sat_checked = Some true then gm ()
    else
      match is_sat session with
      | Some true | None -> gm ()
      | Some false -> None

let get_unsat_core session =
  let resolve_names names =
    let find_name tbl n =
      try [Hashtbl.find tbl n]
      with Not_found ->
        try [Hashtbl.find tbl (n ^ "_0")]
        with Not_found ->
          Debug.info (fun () -> "cannot find clause '"^n^"' for unsat core\n"); []
    in
    match session.named_clauses with
      | Some tbl -> Some (Util.flat_map (find_name tbl) names)
      | None -> None
  in
  let gc () =
    writeln session "(get-unsat-core)";
    match read session with
    | SmtCore c -> resolve_names c
    | SmtError e -> fail session e
    | _ -> None
  in
    if session.sat_checked = Some false then gc ()
    else
      match is_sat session with
      | Some false -> gc ()
      | Some true | None -> None
	  
