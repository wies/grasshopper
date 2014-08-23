(** SMT-LIB v2 solver interface *)

open SmtLibSyntax
open Form
open FormUtil
open Unix
open Util

let num_of_sat_queries = ref 0

(** Solvers *)

type solver_kind =
  | Process of string * string list
  | Logger

type solver_info = 
    { version: int;
      subversion: int;
      has_set_theory: bool;
      smt_options: (string * bool) list;
      kind: solver_kind; 
    }

type solver = 
    { name : string;
      info : solver_info
    }

let logger_info = 
  { version = 0;
    subversion = 0;
    has_set_theory = true;
    smt_options = [];
    kind = Logger;
  }

let logger =
  { name = "LOGGER";
    info = logger_info }


let z3_v3 = { version = 3;
	      subversion = 2;
              has_set_theory = false;
	      smt_options = [":mbqi", true;
			 ":MODEL_V2", true;
			 ":MODEL_PARTIAL", true;
			 ":MODEL_HIDE_UNUSED_PARTITIONS", true];
              kind = Process ("z3", ["-smt2"; "-in"]);
	    }

let z3_v4 = { version = 4;
	      subversion = 3;
              has_set_theory = false;
	      smt_options = 
              (if not !Config.instantiate then [(":auto-config", false)] else []) @
              [(*":smt.mbqi", true;
               ":smt.ematching", true;
               ":model.v2", true;*)
	       ":model.partial", true];
              kind = Process ("z3", ["-smt2"; "-in"]);
	    }

let z3_versions = [z3_v4; z3_v3]

let z3 = 
  let version = 
    try 
      let in_chan = Unix.open_process_in ("z3 -version") in
      let version_regexp = Str.regexp "^Z3[^0-9]*\\([0-9]*\\).\\([0-9]*\\)" in
      let version_string = input_line in_chan in
      ignore (Str.string_match version_regexp version_string 0);
      let version = int_of_string (Str.matched_group 1 version_string) in
      let subversion = int_of_string (Str.matched_group 2 version_string) in
      let _ = Unix.close_process_in in_chan in
      List.find (fun v -> v.version < version || (v.version = version && v.subversion <= subversion)) z3_versions
    with _ -> Debug.warn (fun () -> "No supported version of Z3 found.");
      z3_v4 
  in 
  { name = "Z3";
    info = version }

let cvc4_v1 = 
  { version = 1;
    subversion = 3;
    has_set_theory = true;
    smt_options = [];
    kind = Process ("cvc4", ["--lang=smt2"; "--quant-cf"; "--inst-max-level=0"]);
  }

let cvc4mf_v1 = 
  let options = 
    ["--lang=smt2"; 
     "--finite-model-find"; 
     "--mbqi=none"; 
     "--inst-max-level=0"; 
     "--fmf-inst-engine"]
  in
  { cvc4_v1 with
    kind = 
    Process ("cvc4", options);
  }


let cvc4 = 
  { name = "CVC4";
    info = cvc4_v1 }

let cvc4mf =
  { name = "CVC4MF";
    info = cvc4mf_v1 }

let mathsat_v5 = 
  { version = 5;
    subversion = 1;
    has_set_theory = false;
    smt_options = [];
    kind = Process ("mathsat", ["-verbosity=0"]);
  }

let mathsat = 
  { name = "MathSAT";
    info = mathsat_v5
   }

  
 
let available_solvers = [logger; z3; cvc4; cvc4mf; mathsat]

let selected_solvers = ref [z3]

let select_solver name = 
  let selected = Str.split (Str.regexp "+") name in
  selected_solvers := 
    List.filter 
      (fun s -> List.mem s.name selected && !Config.verify || 
      s.info.kind = Logger && !Config.dump_smt_queries) available_solvers;
  Debug.info (fun () ->
    "Selected solvers: " ^
    String.concat ", " (List.map (fun s -> s.name) !selected_solvers) ^
   "\n")
    
      

(** Solver State *)

type solver_state = 
    { out_chan: out_channel;
      in_chan: in_channel option;
      pid: int;     
    }

(** Sessions *)
   
type session = { log_file_name: string;
                 sat_means: string;
		 mutable assert_count: int;
		 mutable sat_checked: (solver_state option * response) option;
		 stack_height: int;
                 signature: (arity list SymbolMap.t) option;
                 named_clauses: (string, form) Hashtbl.t option;
                 solvers: (solver * solver_state) list
	       }

let dummy_session =
  { log_file_name = "dummy_session";
    sat_means = "";
    assert_count = 0;
    sat_checked = None;
    stack_height = 0;
    signature = None;
    named_clauses = None;
    solvers = [];
  }

exception SmtLib_error of session * string
    
let fail session msg = raise (SmtLib_error (session, "SmtLib: " ^ msg))
      
let write session cmd =
  List.iter 
    (fun (_, state) -> output_string state.out_chan cmd)
    session.solvers

let writefn session fn =
  List.iter 
    (fun (solver, state) -> 
      let cmd = fn solver in
      output_string state.out_chan cmd) 
    session.solvers

let writeln session cmd = 
  write session (cmd ^ "\n")  

let iter_solvers session fn =
  List.iter 
    (fun (solver, state) -> fn solver state)
    session.solvers

let read_from_chan session chan =
  let lexbuf = Lexing.from_channel chan in
  SmtLibLexer.set_file_name lexbuf session.log_file_name; 
  SmtLibParser.output SmtLibLexer.token lexbuf

let read session = 
  let in_descrs = 
    Util.flat_map 
      (fun (_, state) -> 
        flush state.out_chan;
        Opt.to_list (Opt.map descr_of_in_channel state.in_chan))
      session.solvers 
  in
  if in_descrs = [] then 
    (if !Config.verify then None, Unknown else None, Unsat)
  else
  let ready, _, _ = Unix.select in_descrs [] [] (-1.) in
  let in_descr = List.hd ready in
  let in_chan = in_channel_of_descr in_descr in
  let result = read_from_chan session in_chan in
  let state = 
    snd (List.find
           (fun (_, state) -> 
             Opt.get_or_else false 
               (Opt.map (fun c -> descr_of_in_channel c = in_descr) state.in_chan))
           session.solvers)
  in
  Some state, result

let set_option chan opt_name opt_value =
  Printf.fprintf chan "(set-option %s %b)\n" opt_name opt_value

let set_logic chan logic =
  output_string chan ("(set-logic " ^ logic ^ ")\n")

let declare_fun session sym_name arg_sorts res_sort =
  let arg_sorts_str = String.concat " " (List.map (fun srt -> string_of_sort srt) arg_sorts) in
  writeln session ("(declare-fun " ^ sym_name ^ " (" ^ arg_sorts_str ^ ") " ^ string_of_sort res_sort ^ ")")

let declare_sort session sort_name num_of_params =
  writeln session (Printf.sprintf "(declare-sort %s %d)" sort_name num_of_params)
    
let declare_sorts has_int session =
  declare_sort session loc_sort_string 0;
  writefn session (fun solver ->
    if !Config.use_set_theory && solver.info.has_set_theory
    then "(define-sort " ^ set_sort_string ^ loc_sort_string ^ " () (Set " ^ loc_sort_string ^ "))"
    else "(declare-sort " ^ set_sort_string ^ loc_sort_string ^ " 0)");
  if has_int then
    writefn session (fun solver ->
      if !Config.use_set_theory && solver.info.has_set_theory
      then "(define-sort " ^ set_sort_string ^ int_sort_string ^ " () (Set " ^ int_sort_string ^ "))"
      else "(declare-sort " ^ set_sort_string ^ int_sort_string ^ " 0)");
  if !Config.encode_fields_as_arrays 
  then writeln session ("(define-sort " ^ fld_sort_string ^ " (X) (Array Loc X))")
  else 
    begin
      declare_sort session (fld_sort_string ^ bool_sort_string) 0;
      declare_sort session (fld_sort_string ^ loc_sort_string) 0;
      if has_int then declare_sort session (fld_sort_string ^ int_sort_string) 0
    end

let start_with_solver session_name sat_means solver produce_models produce_unsat_cores = 
  let log_file_name = (string_of_ident (fresh_ident session_name)) ^ ".smt2" in
  let start_solver solver =
    let state =
      match solver.info.kind with
      | Process (cmnd, args) ->
          let aargs = Array.of_list (cmnd :: args) in
          let in_read, in_write = Unix.pipe () in
          let out_read, out_write = Unix.pipe () in
          let pid = Unix.create_process cmnd aargs out_read in_write in_write in
          { in_chan = Some (in_channel_of_descr in_read);
            out_chan = out_channel_of_descr out_write;
            pid = pid;
          }
          (*let cmd = String.concat " " (cmnd :: args) in
          let in_chan, out_chan = open_process cmd in
          { in_chan = Some in_chan;
            out_chan = out_chan;
            pid = 0;
          }*)
      | Logger ->
        (* these files should probably go into the tmp directory *)
          { in_chan = None;
            out_chan = open_out log_file_name;
            pid = 0;
          }
    in 
    let options = 
      (if produce_models then [":produce-models", true] else []) @
      solver.info.smt_options @
      (if produce_unsat_cores then [":produce-unsat-cores", true] else [])
    in
    let info = { solver.info with smt_options = options } in
    { solver with info = info },
    state
  in
  let solver_states = List.map start_solver !selected_solvers in
  let names_tbl: (string, form) Hashtbl.t option =
    if produce_unsat_cores then Some (Hashtbl.create 0) else None
  in
  let session = 
    { log_file_name = log_file_name;
      sat_means = sat_means;
      assert_count = 0;
      sat_checked = None;
      stack_height = 0;
      signature = None;
      named_clauses = names_tbl;
      solvers = solver_states;
    }
  in
  session

let init_session session sign =
  (* is int sort anywhere in the signature? *)
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
  (* set all options *)
  List.iter (fun (solver, state) ->
    List.iter 
      (fun (opt, b) -> set_option state.out_chan opt b)
      solver.info.smt_options)
    session.solvers;
  (* set the logic *)
  let set_logic solver state = 
    let logic_str =
      (if !Config.encode_fields_as_arrays then "A" else "") ^
      "UF" ^
      (if has_int then "LIA" else "") ^
      (if solver.info.has_set_theory && !Config.use_set_theory then "FS" else "")
    in
    set_logic state.out_chan logic_str;
  in
  iter_solvers session set_logic;
  (* write benchmark description *)
  if !Config.dump_smt_queries then begin
    writeln session ("(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:\n  " ^ session.sat_means ^ "
  |)")
  end;
  writeln session ("(set-info :smt-lib-version 2.0)");
  writeln session ("(set-info :category \"crafted\")");
  writeln session ("(set-info :status \"unknown\")");
  (* desclare all sorts *)
  declare_sorts has_int session

let start session_name sat_means =
  start_with_solver
    session_name
    sat_means
    !selected_solvers
    true
    !Config.unsat_cores
        
let quit session = 
  writeln session "(exit)";
  (* clean up resources *)
  iter_solvers session (fun solver state ->
    flush state.out_chan;
    (match solver.info.kind with
    | Process _ -> 
        (try Unix.kill state.pid Sys.sigkill 
        with Unix.Unix_error _ -> ())
        (*ignore (Unix.close_process (Opt.get state.in_chan, state.out_chan))*)
    | _ -> ());
    close_out state.out_chan;
    Opt.iter close_in state.in_chan);
  iter_solvers session (fun solver state ->
    if state.pid <> 0 then ignore (Unix.waitpid [] state.pid))

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
      !Config.use_set_theory
  | Eq | Gt | Lt | GtEq | LtEq | IntConst _ | BoolConst _
  | Plus | Minus | Mult | Div | UMinus -> true
  | _ -> false

let string_of_overloaded_symbol sym idx =
  (string_of_symbol sym) ^ "$" ^ (string_of_int idx)

let declare session sign =
  let declare sym idx (arg_sorts, res_sort) = 
    let sym_str = string_of_overloaded_symbol sym idx in
    declare_fun session sym_str arg_sorts res_sort
  in
  let write_decl sym overloaded_variants = 
    if not (is_interpreted sym) then
      begin
        match overloaded_variants with
        | [] -> fail session ("missing sort for symbol " ^ string_of_symbol sym)
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
        FreeSym (mk_ident (string_of_overloaded_symbol sym version))
      with Not_found -> sym
  in
  let rec over t = match t with
    | Var _ as v -> v
    | App (sym, ts, srt) ->
      let ts = List.map over ts in
      let args_srt = List.map sort_of ts in
        App (osym sym (args_srt, srt), ts, srt)
  in
  map_terms over f

let assert_form session f =
  let _ = match f with
    | Binder (_, _, _, ann) ->
      begin
        let name = extract_name true ann in
          match session.named_clauses with
          | Some tbl -> Hashtbl.add tbl name f
          | None -> ()
      end
    | _ -> ()
  in
  session.assert_count <- session.assert_count + 1;
  session.sat_checked <- None;
  let cf = 
    match session.signature with
    | None -> fail session "tried to assert formula before declaring symbols"
    | Some sign -> disambiguate_overloaded_symbols sign f 
  in
  iter_solvers session
    (fun _ state -> 
      output_string state.out_chan "(assert ";
      print_smtlib_form state.out_chan cf;
      output_string state.out_chan ")\n")
    
(*let assert_form session f = Util.measure (assert_form session) f*)
    
let assert_forms session fs =
  List.iter (fun f -> assert_form session f) fs

    
let is_sat session = 
  incr num_of_sat_queries;
  writeln session "(check-sat)";
  let response = read session in
  session.sat_checked <- Some response;
  match snd response with
  | Sat -> Some true
  | Unsat -> Some false
  | Unknown -> None
  | Error e -> fail session e
  | _ -> fail session "unexpected response from prover"
	
(** Covert SMT-LIB model to GRASS model *)
let convert_model session smtModel =
  (* convert SMT-LIB sort to GRASS sort *)
  let rec convert_sort = function
    | IntSort -> Int
    | BoolSort -> Bool
    | FreeSort ((name, num), srts) ->
        let csrts = List.map convert_sort srts in
        match name with
        | "Loc" -> Loc
        | "FldLoc" -> Fld Loc
        | "FldInt" -> Fld Int
        | "FldBool" -> Fld Bool
        | "SetLoc" -> Set Loc
        | "SetInt" -> Set Int
        | "Set" -> Set (List.hd csrts)
        | "Fld" -> Fld (List.hd csrts)
        | _ -> FreeSrt (name, num)
  in
  (* detect Z3/CVC4 identifiers that represent values of uninterpreted sorts *)
  let to_val (name, num) =
    let id = name ^ "_" ^ string_of_int num in
    let z3_val_re = Str.regexp "\\([^!]*\\)!val!\\([0-9]*\\)" in
    let cvc4_val_re = Str.regexp "@uc_\\([^_]*\\)_\\([0-9]*\\)" in
    if Str.string_match z3_val_re id 0 || 
       Str.string_match cvc4_val_re id 0
    then 
      let srt = convert_sort (FreeSort ((Str.matched_group 1 id, 0), [])) in
      let index = int_of_string (Str.matched_group 2 id) in
      Some (srt, index)
    else None
  in
  (* remove suffix from overloaded identifiers *)
  let normalize_ident =
    let name_re = Str.regexp "\\([^\\$]*\\)\\$[0-9]+$" in
    let num_re = Str.regexp "\\(.*\\)_\\([0-9]+\\)$" in
    fun ((name, num) as id) -> 
      if Str.string_match name_re name 0 then
        let nname = Str.matched_group 1 name in
        if Str.string_match num_re nname 0 then
          (Str.matched_group 1 nname, int_of_string (Str.matched_group 2 nname))
        else (nname, 0)
      else id
  in
  (* start model construction *)
  let model0 = Model.empty in
  (* declare cardinalities of GRASS sorts *)
  let model1 =
    let idents =
      List.fold_left (fun idents -> function
        | DefineFun (_, _, _, t, _) 
        | Assert (t, _) -> IdSet.union idents (idents_in_term t)
        | _ -> idents) IdSet.empty smtModel
    in
    let cards = 
      IdSet.fold 
        (fun id cards ->
          match to_val id with
          | Some (Fld _ as srt, index)
          | Some (Set _ as srt, index)
          | Some (Loc as srt, index) -> 
              let card = try SortMap.find srt cards with Not_found -> 0 in
              SortMap.add srt (max card (index + 1)) cards
          | _ -> cards
        )
        idents SortMap.empty
    in
    SortMap.fold 
      (fun srt card model -> Model.add_card model srt card) 
      cards model0
  in
  (* define all symbols *)
  let process_def model sym arity args def =
    let fail pos_opt = 
      let pos = match pos_opt with
      | Some pos -> pos
      | None -> dummy_position
      in
      let msg = 
        ProgError.error_to_string pos
          "Encountered unexpected definition during model conversion" 
      in fail session msg
    in
    let add_val pos model arg_map v =
      try
        let arg_vals = List.map (fun (x, _) -> IdMap.find x arg_map) args in
        Model.add_def model sym arity arg_vals v
      with Not_found -> 
        Model.add_default_val model sym arity v
    in
    let add_term pos model arg_map t =
      if IdMap.is_empty arg_map 
      then Model.add_default_term model sym arity args t
      else fail pos
    in
    let add_form pos model arg_map t =
      if IdMap.is_empty arg_map 
      then Model.add_default_form model sym arity args t
      else fail pos
    in
    let rec convert_term bvs = function
      | SmtLibSyntax.App (SmtLibSyntax.BoolConst b, [], _) -> 
          mk_bool_term b
      | SmtLibSyntax.App (SmtLibSyntax.IntConst i, [], _) -> 
          mk_int i
      | SmtLibSyntax.App (Ident id, ts, pos) ->
          let cts = List.map (convert_term bvs) ts in
          let id = normalize_ident id in
          let sym = symbol_of_ident id in
          let ts_srts = List.map sort_of cts in
          let res_srt = 
            match Model.get_result_sort model sym ts_srts with
            | Some res_srt -> res_srt
            | None -> 
                try List.assoc id args with Not_found -> 
                  try List.assoc id bvs with Not_found -> fail pos
          in
          if List.exists (fun (id2, _) -> id = id2) bvs 
          then mk_var res_srt id
          else mk_app res_srt sym cts
      | SmtLibSyntax.Annot (t, _, _) ->
          convert_term bvs t
      | SmtLibSyntax.App (_, _, pos)
      | SmtLibSyntax.Binder (_, _, _, pos) -> fail pos
    in
    let rec convert_form bvs = function
      | SmtLibSyntax.App (SmtLibSyntax.BoolConst b, [], _) -> 
          mk_bool b
      | SmtLibSyntax.App (SmtLibSyntax.And, fs, _) ->
          let cfs = List.map (convert_form bvs) fs in
          mk_and cfs
      | SmtLibSyntax.App (SmtLibSyntax.Or, fs, _) ->
          let cfs = List.map (convert_form bvs) fs in
          mk_or cfs
      | SmtLibSyntax.App (SmtLibSyntax.Not, [f], _) ->
          mk_not (convert_form bvs f)
      | SmtLibSyntax.App (SmtLibSyntax.Impl, [f1; f2], _) ->
          mk_implies (convert_form bvs f1) (convert_form bvs f2)
      | SmtLibSyntax.App (Ident id, ts, _) ->
          let cts = List.map (convert_term bvs) ts in
          let id = normalize_ident id in
          let sym = symbol_of_ident id in
          mk_atom sym cts
      | SmtLibSyntax.App (SmtLibSyntax.Eq, [t1; t2], pos) -> 
          (try 
            let ct1, ct2 = convert_term bvs t1, convert_term bvs t2 in
            if sort_of ct1 = Bool
            then mk_iff (Atom (ct1, [])) (Atom (ct2, []))
            else mk_eq ct1 ct2
          with _ ->
            let cf1, cf2 = convert_form bvs t1, convert_form bvs t2 in
            mk_iff cf1 cf2)
      | SmtLibSyntax.App (sym, [t1; t2], pos) ->
          let mk_form = match sym with
          | SmtLibSyntax.Gt -> mk_gt
          | SmtLibSyntax.Lt -> mk_lt
          | SmtLibSyntax.Geq -> mk_geq 
          | SmtLibSyntax.Leq -> mk_leq
          | _ -> fail pos
          in
          let ct1 = convert_term bvs t1 in
          let ct2 = convert_term bvs t2 in
          mk_form ct1 ct2
      | SmtLibSyntax.App (_, _, pos) -> fail pos
      | SmtLibSyntax.Binder (SmtLibSyntax.Forall, ids, f, _) ->
          let cids = List.map (fun (id, srt) -> normalize_ident id, convert_sort srt) ids in
          mk_forall cids (convert_form (cids @ bvs) f)
      | SmtLibSyntax.Binder (SmtLibSyntax.Exists, ids, f, _) ->
          let cids = List.map (fun (id, srt) -> normalize_ident id, convert_sort srt) ids in
          mk_exists cids (convert_form (cids @ bvs) f)
      | SmtLibSyntax.Annot (t, _, _) ->
          convert_form bvs t
    in
    let rec pcond arg_map = function
      | SmtLibSyntax.App 
          (SmtLibSyntax.Eq, [SmtLibSyntax.App (Ident id1, [], _); 
                             SmtLibSyntax.App (Ident id2, [], _)], pos) ->
          (match to_val id1, to_val id2 with
          | Some (_, index), None ->
              IdMap.add id2 (Model.value_of_int index) arg_map
          | None, Some (_, index) ->
              IdMap.add id1 (Model.value_of_int index) arg_map
          | _ -> fail pos)
      | SmtLibSyntax.App
          (SmtLibSyntax.Eq, [SmtLibSyntax.App (Ident id, [], _); 
                             SmtLibSyntax.App (SmtLibSyntax.IntConst i, [], _)], pos) ->
          IdMap.add id (Model.value_of_int i) arg_map
      | SmtLibSyntax.App (SmtLibSyntax.And, conds, _) ->
          List.fold_left pcond arg_map conds
      | SmtLibSyntax.Annot (def, _, _) -> 
          pcond arg_map def
      | SmtLibSyntax.App (_, _, pos) 
      | SmtLibSyntax.Binder (_, _, _, pos) -> fail pos
    in 
    let rec p model arg_map = function
      | SmtLibSyntax.App (Ident (name, _), [], pos) when name = "#unspecified" ->
          model
      | SmtLibSyntax.App (Ident id, [], pos) ->
          (match to_val id with
          | Some (_, index) -> 
              add_val pos model arg_map (Model.value_of_int index)
          | _ -> print_endline ("Failed to match " ^ name id); fail pos)
      | SmtLibSyntax.App (SmtLibSyntax.BoolConst b, [], pos) ->
          add_val pos model arg_map (Model.value_of_bool b)
      | SmtLibSyntax.App (SmtLibSyntax.IntConst i, [], pos) -> 
          add_val pos model arg_map (Model.value_of_int i)
      | SmtLibSyntax.App (SmtLibSyntax.Ite, [cond; t; e], _) ->
          let arg_map1 = pcond arg_map cond in
          let model1 = p model arg_map e in
          p model1 arg_map1 t
      | SmtLibSyntax.App (SmtLibSyntax.Eq, _, pos) as cond ->
          let t = SmtLibSyntax.App (SmtLibSyntax.BoolConst true, [], pos) in
          let e = SmtLibSyntax.App (SmtLibSyntax.BoolConst false, [], pos) in
          p model arg_map (SmtLibSyntax.App (SmtLibSyntax.Ite, [cond; t; e], pos))
      | SmtLibSyntax.App (asym, _, pos) as t ->
          (match asym with
          | SmtLibSyntax.And
          | SmtLibSyntax.Or 
          | SmtLibSyntax.Not
          | SmtLibSyntax.Impl -> 
              let f = convert_form [] t in
              add_form pos model arg_map f
          | _ ->
              (* Z3-specific work around *)
              (match convert_term [] t with
              | App (FreeSym (id2, _) as sym2, ts, srt) as t1 ->
                  let re = Str.regexp (string_of_symbol sym ^ "\\$[0-9]+![0-9]+") in
                  if Str.string_match re id2 0 &&
                    List.fold_left2 (fun acc (id1, _) -> function
                      | App (FreeSym _, [App (FreeSym id2, [], _)], _)
                      | App (FreeSym id2, [], _) -> acc && id1 = id2
                      | _ -> false) true args ts
                  then 
                    let def = Model.get_interp model sym2 arity in
                    Model.add_interp model sym arity def
                  else add_term pos model arg_map t1
              | t1 -> add_term pos model arg_map t1))
      | SmtLibSyntax.Annot (def, _, _) -> 
          p model arg_map def
      | SmtLibSyntax.Binder (_, _, _, pos) as t ->
          let f = convert_form [] t in
          add_form pos model arg_map f
    in p model IdMap.empty def
  in
  let model2 =
    List.fold_left 
      (fun model cmd ->
        match cmd with
        | DefineFun (id, args, res_srt, def, _) -> 
            let cres_srt = convert_sort res_srt in
            let cargs = List.map (fun (x, srt) -> x, convert_sort srt) args in
            let carg_srts = List.map snd cargs in
            let sym = symbol_of_ident (normalize_ident id) in
            process_def model sym (carg_srts, cres_srt) cargs def 
        | _ -> model)
      model1 smtModel 
  in
  Model.finalize_values model2

let rec get_model session = 
  let gm state =
    output_string state.out_chan "(get-model)\n";
    flush state.out_chan;
    match read_from_chan session (Opt.get state.in_chan) with
    | Model m -> 
        let cm = convert_model session m in
        (match session.signature with
        | Some sign -> Some (Model.restrict_to_sign cm sign)
        | None -> Some cm)
    | Error e -> fail session e
    | _ -> None
  in
  match session.sat_checked with
  | None -> 
      ignore (is_sat session);
      get_model session
  | Some (Some state, Sat) -> gm state
  | _ -> None

let rec get_unsat_core session =
  let resolve_names names =
    let find_name tbl n =
      try [Hashtbl.find tbl n]
      with Not_found ->
        try [Hashtbl.find tbl (n ^ "_0")]
        with Not_found ->
          Debug.info (fun () -> "cannot find clause '" ^ n ^ "' for unsat core\n"); []
    in
    match session.named_clauses with
      | Some tbl -> Some (Util.flat_map (find_name tbl) names)
      | None -> None
  in
  let gc state =
    output_string state.out_chan "(get-unsat-core)\n";
    flush state.out_chan;
    match read_from_chan session (Opt.get state.in_chan) with
    | UnsatCore c -> resolve_names c
    | Error e -> fail session e
    | _ -> None
  in
  match session.sat_checked with
  | None -> 
      ignore (is_sat session); 
      get_unsat_core session
  | Some (Some state, Unsat) -> gc state
  | _ -> None
	  
