(** SMT-LIB v2 solver interface *)

open SmtLibSyntax
open Grass
open GrassUtil
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
      has_inst_closure: bool;
      smt_options: (string * string) list;
      kind: solver_kind; 
    }

type solver = 
    { name : string;
      info : solver_info
    }
    
let get_version name cmd vregexp versions =
  try
    let in_chan = Unix.open_process_in cmd in
    let version_regexp = Str.regexp vregexp in
    let version_string = input_line in_chan in
    let _ = Unix.close_process_in in_chan in
    if Str.string_match version_regexp version_string 0 then
      let version = int_of_string (Str.matched_group 1 version_string) in
      let subversion = int_of_string (Str.matched_group 2 version_string) in
      let v =
        List.find (fun v ->
          let v = v () in
          v.version < version || (v.version = version && v.subversion <= subversion)) versions
      in
      Some (fun () -> { name = name; info = v (); })
    else (print_endline "no match"; raise Not_found)
    with _ -> None

let z3_v3 () =
  { version = 3;
    subversion = 2;
    has_set_theory = false;
    has_inst_closure = false;
    smt_options = [":mbqi", "true";
		   ":MODEL_V2", "true";
		   ":MODEL_PARTIAL", "true";
		   ":MODEL_HIDE_UNUSED_PARTITIONS", "true"];
    kind = Process ("z3", ["-smt2"; "-in"]);
  }

let z3_v4_options () = 
  (if not !Config.instantiate then
    [(":auto-config", "false");
     (":smt.mbqi", "false")] else
    [":smt.mbqi", "true"])
  @ [":smt.ematching", "true"]
  
let z3_v4 () =
  { version = 4;
    subversion = 3;
    has_set_theory = false;
    has_inst_closure = false;
    smt_options = z3_v4_options ();
    kind = Process ("z3", ["-smt2"; "-in"]);
  }

let z3_versions = [z3_v4; z3_v3]

let z3 = get_version "Z3" "z3 -version" "^Z3[^0-9]*\\([0-9]*\\).\\([0-9]*\\)" z3_versions

let cvc4_v1 () = 
  let options =
    ["--lang=smt2"; 
     "--quant-cf"; 
     "--inst-max-level=0"; 
     "--simplification=none"]
  in
  { version = 1;
    subversion = 5;
    has_set_theory = true;
    has_inst_closure = true;
    smt_options = [];
    kind = Process ("cvc4", options);
  }

let cvc4 = get_version "CVC4" "cvc4 --version" ".*CVC4[^0-9]*\\([0-9]*\\).\\([0-9]*\\)" [cvc4_v1]

let cvc4mf_v1 () = 
  let options = 
    ["--lang=smt2"; 
     "--finite-model-find"; 
     "--mbqi=none"; 
     "--inst-max-level=0"; 
     "--fmf-inst-engine";
     "--simplification=none"]
  in
  let solver = cvc4_v1 () in
  { solver with
    kind = Process ("cvc4", options);
  }

let cvc4mf = get_version "CVC4MF" "cvc4 --version" ".*CVC4 version \\([0-9]*\\).\\([0-9]*\\)" [cvc4mf_v1]

let mathsat_v5 = 
  { version = 5;
    subversion = 1;
    has_set_theory = false;
    has_inst_closure = false;
    smt_options = [];
    kind = Process ("mathsat", ["-verbosity=0"]);
  }

let mathsat () = 
  { name = "MathSAT";
    info = mathsat_v5
  }


let logger_info = 
  { version = 0;
    subversion = 0;
    has_set_theory = false;
    has_inst_closure = false;
    smt_options = [];
    kind = Logger;
  }

let z3logger () =
  { name = "Z3LOG";
    info = { logger_info with smt_options = z3_v4_options () } }

let cvc4logger () =
  { name = "CVC4LOG";
    info = { logger_info with has_set_theory = true; has_inst_closure = true }}


let available_solvers = 
  z3logger :: cvc4logger :: Util.flat_map Util.Opt.to_list [z3; cvc4; cvc4mf]

let selected_solvers = ref []

let select_solver name = 
  let selected = Str.split (Str.regexp "+") name in
  selected_solvers := 
    List.filter 
      (fun s -> List.mem s.name selected && (!Config.verify || s.info.kind = Logger))
      (List.map (fun s -> s ()) available_solvers);
  if List.for_all (fun s -> s.info.kind <> Logger) !selected_solvers && !Config.dump_smt_queries then
    selected_solvers := z3logger () :: !selected_solvers;
  Debug.info (fun () ->
    "Selected SMT solvers: " ^
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


(** Register signal handlers for cleaning up running processes *)
let add_running_pid,
    remove_running_pids =
  let open Sys in
  let running_pids = ref IntSet.empty in
  let handlers = Hashtbl.create 8 in
  let handle sig_num =
    Debug.info (fun () -> "Aborting.\n");
    IntSet.iter 
      (fun pid -> kill pid sig_num) !running_pids;
    try 
      match Hashtbl.find handlers sig_num with
      | Signal_handle handler -> handler sig_num
      | Signal_ignore -> ()
      | Signal_default -> exit 1
    with Not_found -> exit 1
  in
  let add_handler sig_num = 
    let old_handler = signal sig_num (Signal_handle handle) in
    Hashtbl.add handlers sig_num old_handler
  in
  add_handler sigint;
  let add_running_pid pid = 
    running_pids := IntSet.add pid !running_pids
  in
  let remove_running_pids session =
    let pids = 
      List.fold_left 
        (fun pids (solver, state) -> 
          match solver.info.kind with
          | Process _ -> IntSet.add state.pid pids
          | _ -> pids)
        IntSet.empty session.solvers
    in
    running_pids := IntSet.diff !running_pids pids
  in
  add_running_pid,
  remove_running_pids
    
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
  Printf.fprintf chan "(set-option %s %s)\n" opt_name opt_value

let set_logic chan logic =
  output_string chan ("(set-logic " ^ logic ^ ")\n")

let declare_fun session sym_name arg_sorts res_sort =
  let arg_sorts_str = String.concat " " (List.map (fun srt -> string_of_sort srt) arg_sorts) in
  writeln session ("(declare-fun " ^ sym_name ^ " (" ^ arg_sorts_str ^ ") " ^ string_of_sort res_sort ^ ")")

let declare_sort session sort_name num_of_params =
  writeln session (Printf.sprintf "(declare-sort %s %d)" sort_name num_of_params)

let smtlib_sort_of_grass_sort srt =
  let rec csort = function
  | Int -> IntSort
  | Bool -> BoolSort
  | Set srt ->
      FreeSort ((set_sort_string, 0), [csort srt])
  | Map (dsrt, rsrt) ->
      FreeSort ((map_sort_string, 0), [csort dsrt; csort rsrt])
  | Array srt ->
      FreeSort (("G" ^ array_sort_string, 0), [csort srt])
  | ArrayCell srt ->
      FreeSort ((array_cell_sort_string, 0), [csort srt])
  | Loc srt ->
      FreeSort ((loc_sort_string, 0), [csort srt])
  | FreeSrt id -> FreeSort (id, [])
  in
  csort srt
    
let declare_sorts has_int session structs =
  SortSet.iter
    (function FreeSrt id -> declare_sort session (string_of_ident id) 0 | _ -> ())
    structs;
  declare_sort session ("G" ^ array_sort_string) 1;
  declare_sort session array_cell_sort_string 1;
  declare_sort session loc_sort_string 1;
  if not !Config.use_set_theory
  then declare_sort session set_sort_string 1;
  if !Config.encode_fields_as_arrays 
  then writeln session ("(define-sort " ^ map_sort_string ^ " (X Y) (Array X Y))")
  else declare_sort session map_sort_string 2

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
          add_running_pid pid;
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
      (if produce_models then [":produce-models", "true"] else []) @
      solver.info.smt_options @
      (if produce_unsat_cores then [":produce-unsat-cores", "true"] else [])
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
  (* is Int sort anywhere in the signature? *)
  let has_int = 
    let rec hi = function
      | Int -> true
      | Set srt
      | Array srt -> hi srt
      | Map (dsrt, rsrt) -> hi dsrt || hi rsrt
      | _ -> false
    in
    SymbolMap.exists 
      (fun _ variants -> 
        List.exists (fun (arg_srts, res_srt) -> List.exists hi (res_srt :: arg_srts))
          variants)
      sign
  in
  (* collect the struct types *)
  let structs =
    let rec add acc srt = match srt with
    | Loc (FreeSrt _ as srt) -> SortSet.add srt acc
    | Set srt | ArrayCell srt | Array srt | Loc srt -> add acc srt
    | Map (srt1, srt2) -> add (add acc srt1) srt2
    | _ -> acc
    in
    SymbolMap.fold
      (fun _ funSig acc ->
        List.fold_left
          (fun acc (args,ret) ->
            List.fold_left (add) (add acc ret) args
          )
          acc
          funSig
      )
      sign
      SortSet.empty
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
  declare_sorts has_int session structs

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
    if state.pid <> 0 then ignore (Unix.waitpid [] state.pid));
  remove_running_pids session

let pop session = 
  if session.stack_height <= 0 then fail session "pop on empty stack" else
  writeln session "(pop 1)";
  let new_session = { session with stack_height = session.stack_height - 1 } in
  new_session

let push session = 
  writeln session "(push 1)";
  let new_session = { session with stack_height = session.stack_height + 1 } in
  new_session

let grass_smtlib_prefix = "grass_" 

let smtlib_symbol_of_grass_symbol solver_info sym = match sym with 
  | FreeSym id -> SmtLibSyntax.Ident id
  | Plus -> SmtLibSyntax.Plus
  | Minus | UMinus -> SmtLibSyntax.Minus
  | Mult -> SmtLibSyntax.Mult
  | Div -> SmtLibSyntax.Div
  | Eq -> SmtLibSyntax.Eq
  | LtEq -> SmtLibSyntax.Leq
  | GtEq -> SmtLibSyntax.Geq
  | Lt -> SmtLibSyntax.Lt
  | Gt -> SmtLibSyntax.Gt
  | (Read | Write) when !Config.encode_fields_as_arrays -> SmtLibSyntax.Ident (string_of_symbol sym, 0)
  | (IntConst _ | BoolConst _) as sym -> SmtLibSyntax.Ident (string_of_symbol sym, 0)
  | sym -> SmtLibSyntax.Ident (grass_smtlib_prefix ^ (string_of_symbol sym), 0)

let grass_symbol_of_smtlib_symbol solver_info =
  let to_string sym = SmtLibSyntax.string_of_symbol (smtlib_symbol_of_grass_symbol solver_info sym) in
  let symbol_map = List.map (fun sym -> (to_string sym, sym)) symbols in
  function (name, _) as id ->
    try List.assoc name symbol_map
    with Not_found -> FreeSym id

let is_interpreted solver_info sym = match sym with
  | Read | Write -> !Config.encode_fields_as_arrays
  | Empty | SetEnum | Union | Inter | Diff | Elem | SubsetEq ->
      !Config.use_set_theory && solver_info.has_set_theory
  | Eq | Gt | Lt | GtEq | LtEq | IntConst _ | BoolConst _
  | Plus | Minus | Mult | Div | UMinus -> true
  | FreeSym id -> id = ("inst-closure", 0) && solver_info.has_inst_closure
  | _ -> false

let string_of_overloaded_symbol solver_info sym idx =
  match smtlib_symbol_of_grass_symbol solver_info sym with
  | SmtLibSyntax.Ident id ->
    (string_of_ident id) ^
    if solver_info.has_inst_closure && sym = FreeSym ("inst-closure", 0)
    then ""
    else "$" ^ (string_of_int idx)
  | _ -> 
    failwith "string_of_overloaded_symbol"


let declare session sign =
  let declare solver_info out_chan sym idx (arg_sorts, res_sort) = 
    let sym_str = string_of_overloaded_symbol solver_info sym idx in
    let decl =
      mk_declare_fun (sym_str, 0) (List.map smtlib_sort_of_grass_sort arg_sorts) (smtlib_sort_of_grass_sort res_sort)
    in
    SmtLibSyntax.print_command out_chan decl 
  in
  let write_decl sym overloaded_variants =
    iter_solvers session
      (fun solver state -> 
        if not (is_interpreted solver.info sym) then
          begin
            match overloaded_variants with
            | [] -> fail session ("missing sort for symbol " ^ string_of_symbol sym)
            | _ ->
                Util.iteri (declare solver.info state.out_chan sym) overloaded_variants
          end)
  in
  init_session session sign;
  SymbolMap.iter write_decl sign;
  writeln session "";
  { session with signature = Some sign }

let extract_name ann =
  let names = Util.filter_map 
      (function Name _ -> !Config.named_assertions | _ -> false) 
      (function Name id -> string_of_ident id | _ -> "")
      ann 
  in
  Str.global_replace (Str.regexp " \\|(\\|)") "_" (String.concat "_" (List.rev names))

let smtlib_form_of_grass_form solver_info signs f =
  let osym sym sign =
    if is_interpreted solver_info sym 
    then smtlib_symbol_of_grass_symbol solver_info sym
    else
      let versions = 
        try SymbolMap.find sym signs 
        with Not_found -> [] 
      in
      try
        let version = Util.find_index sign versions in
        SmtLibSyntax.Ident (mk_ident (string_of_overloaded_symbol solver_info sym version))
      with Not_found ->
        smtlib_symbol_of_grass_symbol solver_info sym
  in
  let rec cterm t = match t with
  | Var (id, _) -> SmtLibSyntax.mk_app (SmtLibSyntax.Ident id) []
  | App (Empty as sym, [], srt) when solver_info.has_set_theory && !Config.use_set_theory ->
      let sym = osym sym ([], srt) in
      SmtLibSyntax.mk_annot (SmtLibSyntax.mk_app sym []) (As (smtlib_sort_of_grass_sort srt))
  | App (sym, ts, srt) ->
      let args_srt = List.map sort_of ts in
      let ts = List.map cterm ts in
      SmtLibSyntax.mk_app (osym sym (args_srt, srt)) ts
  in
  let rec is_pattern below_app = function
    | App (_, ts, _) -> List.exists (is_pattern true) ts
    | Var _ -> below_app
  in
  let rec find_patterns acc = function
    | BoolOp (_, fs) ->
        List.fold_left find_patterns acc fs
    | Binder (_, _, f, _) -> find_patterns acc f
    | Atom (App (_, ts, _), _) ->
        let pts = List.filter (is_pattern false) ts in
        List.fold_left (fun acc t -> TermSet.add t acc) acc pts
    | Atom _ -> acc
  in
  let name t a =
    match extract_name a with
    | "" -> t
    | n -> SmtLibSyntax.mk_annot t (Name (n, 0))
  in
  let rec cform f = match f with
  | BoolOp (And, []) -> SmtLibSyntax.mk_app (BoolConst true) []
  | BoolOp (Or, []) -> SmtLibSyntax.mk_app (BoolConst false) []
  | BoolOp (op, fs) ->
      let fs = List.map cform fs in
      let sym = match op with
      | Not -> SmtLibSyntax.Not
      | And -> SmtLibSyntax.And
      | Or -> SmtLibSyntax.Or
      in
      SmtLibSyntax.mk_app sym fs
  | Atom (t, a) -> name (cterm t) a
  | Binder (_, [], f, a) -> name (cform f) a
  | Binder (b, vs, f, a) ->
      let fun_patterns = find_patterns TermSet.empty f in
      let patterns =
        let pvs = 
          TermSet.fold 
            (fun t pvs -> IdSet.union (fv_term t) pvs)
            fun_patterns IdSet.empty
        in 
        List.fold_left
          (fun patterns (id, srt) ->
            let p =
              if solver_info.has_inst_closure
              then Var (id, srt)
              else App (FreeSym ("inst-closure", 0), [Var (id, srt)], Bool)
            in
            if IdSet.mem id pvs 
            then patterns 
            else TermSet.add p patterns)
          fun_patterns vs
      in
      let vs = List.map (fun (id, srt) -> (id, smtlib_sort_of_grass_sort srt)) vs in
      let b = match b with
      | Forall -> SmtLibSyntax.Forall
      | Exists -> SmtLibSyntax.Exists
      in
      let f =
        if not !Config.smtpatterns && !Config.instantiate || TermSet.is_empty patterns
        then SmtLibSyntax.mk_binder b vs (cform f)
        else
          let annot =
            SmtLibSyntax.Pattern (List.map cterm (TermSet.elements patterns))
          in
          SmtLibSyntax.mk_binder b vs (SmtLibSyntax.mk_annot (cform f) annot)
      in
      name f a
  in
  cform f

let assert_form session f =
  let _ = match f with
    | Binder (_, _, _, ann) ->
      begin
        let name = extract_name ann in
          match session.named_clauses with
          | Some tbl -> Hashtbl.add tbl name f
          | None -> ()
      end
    | _ -> ()
  in
  session.assert_count <- session.assert_count + 1;
  session.sat_checked <- None;
  iter_solvers session
    (fun solver state -> 
      let cf = 
        match session.signature with
        | None -> fail session "tried to assert formula before declaring symbols"
        | Some sign -> smtlib_form_of_grass_form solver.info sign f 
      in
      SmtLibSyntax.print_command state.out_chan (mk_assert cf))
    
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
        match name, csrts with
        | "Loc", [esrt] -> Loc esrt
        | "Set", [esrt] -> Set esrt
        | "GArray", [esrt] -> Array esrt
        | "ArrayCell", [esrt] -> ArrayCell esrt
        | "Map", [dsrt; rsrt] -> Map (dsrt, rsrt)
        | _, [] -> FreeSrt (name, num)
        | srt, _ -> fail session ("encountered unexpected sort " ^ srt ^ " in model conversion")
  in
  (* solver_info for symbol conversion *)
  let solver_info = (fst (List.hd session.solvers)).info in
  let to_sym = grass_symbol_of_smtlib_symbol solver_info in
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
          | Some (Map _ as srt, index)
          | Some (Set _ as srt, index)
          | Some (Loc _ as srt, index) -> 
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
          let sym = to_sym id in
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
      | SmtLibSyntax.App (SmtLibSyntax.Plus as op, [t1; t2], _)
      | SmtLibSyntax.App (SmtLibSyntax.Mult as op, [t1; t2], _)
      | SmtLibSyntax.App (SmtLibSyntax.Minus as op, [t1; t2], _)
      | SmtLibSyntax.App (SmtLibSyntax.Div as op, [t1; t2], _) ->
          let ct1 = convert_term bvs t1 in
          let ct2 = convert_term bvs t2 in
          let mk_term = match op with
          | SmtLibSyntax.Plus -> mk_plus
          | SmtLibSyntax.Minus -> mk_minus
          | SmtLibSyntax.Mult -> mk_mult
          | SmtLibSyntax.Div -> mk_div
          | _ -> failwith "unexpected match case"
          in mk_term ct1 ct2          
      | SmtLibSyntax.Annot (t, _, _) ->
          convert_term bvs t
      | SmtLibSyntax.App (_, _, pos)
      | SmtLibSyntax.Binder (_, _, _, pos) 
      | SmtLibSyntax.Let (_, _, pos) -> fail pos
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
          let sym = to_sym id in
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
      | SmtLibSyntax.Let (_, _, pos) -> fail pos
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
      | SmtLibSyntax.Binder (_, _, _, pos)
      | SmtLibSyntax.Let (_, _, pos) -> fail pos
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
                  let re1 = Str.regexp (string_of_symbol sym ^ "\\$[0-9]+![0-9]+") in
                  let re2 = Str.regexp (grass_smtlib_prefix ^ (string_of_symbol sym) ^ "\\$[0-9]+![0-9]+") in
                  if (Str.string_match re1 id2 0 || Str.string_match re2 id2 0) &&
                    List.fold_left2 (fun acc (id1, _) -> function
                      | App (FreeSym _, [App (FreeSym id2, [], _)], _)
                      | App (FreeSym id2, [], _) -> acc && id1 = id2
                      | _ -> false) true args ts
                  then 
                    let def = Model.get_interp model sym2 arity in
                    Model.add_interp model sym arity def
                  else
                    add_term pos model arg_map t1
              | t1 -> add_term pos model arg_map t1))
      | SmtLibSyntax.Annot (def, _, _) -> 
          p model arg_map def
      | SmtLibSyntax.Binder (_, _, _, pos) as t ->
          let f = convert_form [] t in
          add_form pos model arg_map f
      | SmtLibSyntax.Let (_, _, pos) -> fail pos
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
            let sym = to_sym (normalize_ident id) in
            process_def model sym (carg_srts, cres_srt) cargs (SmtLibSyntax.unletify def) 
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
  | Some (Some state, Sat) 
  | Some (Some state, Unknown) -> gm state
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
	  
