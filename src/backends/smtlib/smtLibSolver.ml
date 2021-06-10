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
      dt_logic_string: string;
      smt_options: (string * string) list;
      kind: solver_kind; 
    }

type solver = 
    { name : string;
      info : solver_info
    }
    
let get_version name cmd vregexp versions =
  try
    let in_chan, out_chan, err_chan = Unix.open_process_full cmd (Unix.environment ()) in
    let version_regexp = Str.regexp vregexp in
    let version_string = input_line in_chan in
    let _ = Unix.close_process_full (in_chan, out_chan, err_chan) in
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
    dt_logic_string = "";
    smt_options = [":mbqi", "true";
		   ":MODEL_V2", "true";
		   ":MODEL_PARTIAL", "true";
		   ":MODEL_HIDE_UNUSED_PARTITIONS", "true"];
    kind = Process ("z3", ["-smt2"; "-in"]);
  }

let z3_v4_options () =
  if not !Config.instantiate then [(":auto-config", "false"); (":smt.mbqi", "false"); (":smt.ematching", "true")]
  else []
  
let z3_v4 () =
  { version = 4;
    subversion = 3;
    has_set_theory = false;
    has_inst_closure = false;
    dt_logic_string = "";
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
     "--incremental";
     "--simplification=none"]
  in
  { version = 1;
    subversion = 5;
    has_set_theory = true;
    has_inst_closure = true;
    dt_logic_string = "DT";
    smt_options = [];
    kind = Process ("cvc4", options);
  }

let cvc4 = get_version "CVC4" "cvc4 --version" ".*CVC4 version \\([0-9]*\\).\\([0-9]*\\)" [cvc4_v1]

let cvc4mf_v1 () = 
  let options = 
    ["--lang=smt2"; 
     "--finite-model-find"; 
     "--mbqi=none"; 
     "--inst-max-level=0"; 
     "--fmf-inst-engine";
     "--incremental";
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
    dt_logic_string = "DT";
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
    dt_logic_string = "";
    smt_options = [];
    kind = Logger;
  }

let z3logger () =
  { name = "Z3LOG";
    info = { logger_info with smt_options = z3_v4_options () } }

let cvc4logger () =
  { name = "CVC4LOG";
    info = { logger_info with has_set_theory = true; has_inst_closure = true; dt_logic_string = "DT" }}


let available_solvers = 
  z3logger :: cvc4logger :: Util.flat_map Util.Opt.to_list [z3; cvc4; cvc4mf]

let selected_solvers = ref []

let select_solver name =
  let available_solvers =
    List.map (fun s -> s ()) available_solvers
  in
  let selected = Str.split (Str.regexp "+") name in
  let _ =
    List.iter (fun name ->
      if List.for_all (fun s -> s.name <> name) available_solvers then
        failwith ("SMT solver '" ^ name ^ "' is not supported."))
      selected
  in
  selected_solvers := 
    List.filter 
      (fun s -> List.mem s.name selected && (!Config.verify || s.info.kind = Logger))
      available_solvers;
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
      mutable response_count: int;
    }

(** Sessions *)
   
type session = { log_file_name: string;
                 sat_means: string;
		 mutable assert_count: int;
                 mutable response_count: int;
		 mutable sat_checked: (solver_state option * response) option;
		 stack_height: int;
                 signature: (arity list SymbolMap.t) option;
                 user_sorts: sort IdMap.t;
                 named_clauses: (string, form) Hashtbl.t option;
                 solvers: (solver * solver_state) list
	       }

let dummy_session =
  { log_file_name = "dummy_session";
    sat_means = "";
    assert_count = 0;
    response_count = 0;
    sat_checked = None;
    stack_height = 0;
    signature = None;
    user_sorts = IdMap.empty;
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
      | Signal_default ->
          Debug.warn (fun () -> Printf.sprintf "Received signal %d from SMT solver. Aborting.\n" sig_num);
          exit (128 - sig_num)
    with Not_found -> exit (128 - sig_num)
  in
  let add_handler sig_num = 
    let old_handler = signal sig_num (Signal_handle handle) in
    Hashtbl.add handlers sig_num old_handler
  in
  add_handler sigint;
  add_handler sigpipe;
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
  try
    SmtLibParser.output SmtLibLexer.token lexbuf
  with ProgError.Prog_error (pos, _) ->
    let tok = Lexing.lexeme lexbuf in
    let tail = SmtLibLexer.ruleTail "" lexbuf in
    let msg = 
      "failed to parse SMT solver response while parsing: " ^ tok ^ tail
    in
    ProgError.syntax_error pos (Some msg)
      
let read session = 
  let in_descrs = 
    Util.flat_map 
      (fun (_, state) -> 
        flush state.out_chan;
        Opt.to_list (Opt.map descr_of_in_channel state.in_chan))
      session.solvers 
  in
  let rec loop () =
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
    state.response_count <- state.response_count + 1;
    if state.response_count > session.response_count
    then begin
      session.response_count <- session.response_count + 1;
      Some state, result
    end
    else loop ()
  in
  if in_descrs = [] then 
    (if !Config.verify then None, Unknown else None, Unsat)
  else loop ()
 

let set_option chan opt_name opt_value =
  Printf.fprintf chan "(set-option %s %s)\n" opt_name opt_value

let set_logic chan logic =
  output_string chan ("(set-logic " ^ logic ^ ")\n")

let declare_fun session sym_name arg_sorts res_sort =
  let arg_sorts_str = String.concat " " (List.map (fun srt -> string_of_sort srt) arg_sorts) in
  writeln session ("(declare-fun " ^ sym_name ^ " (" ^ arg_sorts_str ^ ") " ^ string_of_sort res_sort ^ ")")

let declare_sort session sort_name num_of_params =
  writeln session (Printf.sprintf "(declare-sort %s %d)" sort_name num_of_params)

let declare_datatypes =
  let rec free_srts acc = function
    | FreeSort (id, srts) -> 
        List.fold_left free_srts (IdSet.add id acc) srts
    | _ -> acc
  in
  fun session adts ->
    (* compute strongly connected components of ADT definitions *)
    let g =
      List.fold_left
        (fun g (id, _) -> IdGraph.add_vertex g id)
        IdGraph.empty adts 
    in
    let g =
      List.fold_left
        (fun g (src, cnstrs) ->
          List.fold_left (fun g (_, args) ->
            List.fold_left (fun g (_, srt) ->
              let srts = free_srts IdSet.empty srt in
              IdGraph.add_edges g src (IdSet.inter (IdGraph.vertices g) srts))
              g args)
            g cnstrs)
        g adts
    in
    let adt_sscs = IdGraph.topsort g in
    List.iter (fun ids ->
      let adt_defs = List.map (fun id -> (id, List.assoc id adts)) ids in
      iter_solvers session
        (fun solver state ->
          SmtLibSyntax.print_command state.out_chan (mk_declare_datatypes adt_defs)))
      adt_sscs
    
let smtlib_sort_of_grass_sort srt =
  let rec csort = function
  | Byte -> if !Config.use_bitvector then BvSort 8 else FreeSort(("GrassByte",0), [])
  | Int ->  if !Config.use_bitvector then BvSort 32 else IntSort
  | Bool -> BoolSort
  | Pat -> FreeSort (("GrassPat", 0), [])
  | Set srt ->
      FreeSort ((set_sort_string, 0), [csort srt])
  | Map (dsrts, rsrt) ->
      let k = List.length dsrts - 1 in
      FreeSort ((map_sort_string, k), List.map csort dsrts @ [csort rsrt])
  | Adt (id, adts) ->
      let adts1 =
        List.map
          (fun (id, cnsts) ->
            (id, List.map (fun (id, args) ->
              (id, List.map (fun (id, srt) -> (id, csort srt)) args)) cnsts))
          adts
      in
      AdtSort (id, adts1)
  | Array srt ->
      FreeSort (("Grass" ^ array_sort_string, 0), [csort srt])
  | ArrayCell srt ->
      FreeSort ((array_cell_sort_string, 0), [csort srt])
  | Loc srt ->
      FreeSort ((loc_sort_string, 0), [csort srt])
  | FreeSrt id -> FreeSort (id, [])
  in
  csort srt
    
let declare_sorts has_int session =
  declare_sort session ("Grass" ^ pat_sort_string) 0;
  declare_sort session ("Grass" ^ array_sort_string) 1;
  declare_sort session array_cell_sort_string 1;
  declare_sort session loc_sort_string 1;
  if not !Config.use_set_theory
  then declare_sort session set_sort_string 1;
  if !Config.encode_fields_as_arrays 
  then writeln session ("(define-sort " ^ map_sort_string ^ " (X Y) (Array X Y))")
  else begin
    declare_sort session (map_sort_string) 2;
    declare_sort session (map_sort_string ^ "^1") 3
  end;
  if not !Config.use_bitvector
  then declare_sort session ("GrassByte") 0;
    IdMap.iter
    (fun _ -> function
      | FreeSrt id -> declare_sort session (string_of_ident id) 0
      | _ -> ())
    session.user_sorts;
  let adts = 
    IdMap.fold
      (fun _ srt adts -> match srt with
      | Adt (id, adts) ->
          let adts =
            List.map (fun (id, cnstrs) ->
              (id, List.map (fun (id, args) ->
                (id, List.map (fun (id, srt) -> (id, smtlib_sort_of_grass_sort srt)) args))
                 cnstrs)) adts
          in
          Some adts
      | _ -> adts)
      session.user_sorts None
  in
  Opt.iter (declare_datatypes session) adts



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
          close out_read;
          close in_write;
          { in_chan = Some (in_channel_of_descr in_read);
            out_chan = out_channel_of_descr out_write;
            pid = pid;
            response_count = 0;
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
            response_count = 0;
          }
    in 
    let options = 
      (if produce_models then [":produce-models", "true"] else []) @
      solver.info.smt_options @
      (if produce_unsat_cores then [":produce-unsat-cores", "true"; ":smt.core.minimize", "true"] else [])
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
      response_count = 0;
      sat_checked = None;
      stack_height = 0;
      signature = None;
      user_sorts = IdMap.empty;
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
      | Set srt | Loc srt | Array srt | ArrayCell srt -> hi srt
      | Map (dsrts, rsrt) -> List.exists hi dsrts || hi rsrt
      | Adt (_, adts) ->
          List.exists
            (fun (_, cnsts) ->
              List.exists
                (fun (_, args) ->
                  List.exists (fun (_, srt) -> hi srt) args)
                cnsts) adts
      | _ -> false
    in
    SymbolMap.exists 
      (fun _ variants -> 
        List.exists (fun (arg_srts, res_srt) -> List.exists hi (res_srt :: arg_srts))
          variants)
      sign
  in
  (* collect the user-defined sorts *)
  let user_srts =
    let rec add seen acc srt = match srt with
    | FreeSrt id when not @@ IdSet.mem id seen -> IdMap.add id srt acc
    | Adt (id, adts) when not @@ IdSet.mem id seen ->
        let acc1 = IdMap.add id (Adt (id, adts)) acc in
        let seen1 = List.fold_left (fun seen1 (id, _) -> IdSet.add id seen1) seen adts in
        List.fold_left (fun acc (id, cnstrs) ->
          let acc1 = IdMap.add id (Adt (id, adts)) acc in
          List.fold_left (fun acc (_, args) ->
            List.fold_left
              (fun acc (_, srt) -> add seen1 acc srt)
              acc args)
            acc1 cnstrs)
          acc1 adts
    | Set srt | ArrayCell srt | Array srt | Loc srt -> add seen acc srt
    | Map (dsrts, rsrt) -> List.fold_left (add seen) acc (rsrt :: dsrts)
    | _ -> acc
    in
    SymbolMap.fold
      (fun _ funSig acc ->
        List.fold_left
          (fun acc (args, ret) ->
            List.fold_left (add IdSet.empty) (add IdSet.empty acc ret) args
          )
          acc
          funSig
      )
      sign
      IdMap.empty
  in
  (* Add implicit ADT constructors to signature *)
  let sign =
    let add_to_sign sym tpe sign =
      let old = SymbolMap.find_opt sym sign |> Opt.get_or_else [] in
      if List.mem tpe old then sign
      else SymbolMap.add sym (tpe :: old) sign
    in
    let subst_sort = function
      | FreeSrt id -> IdMap.find id user_srts
      | srt -> srt
    in
    IdMap.fold (fun _ srt sign -> match srt with
    | Adt (id, adts) ->
        let cnsts = List.assoc id adts in
        List.fold_left
          (fun sign (id, args) ->
            let arg_srts = List.map (fun (_, srt) -> subst_sort srt) args in
            add_to_sign (Constructor id) (arg_srts, srt) sign)
          sign cnsts
    | _ -> sign)
      user_srts sign
  in
  (* Is there an ADT sort anywhere in the signature? *)
  let has_adt = IdMap.exists (fun  _ -> function Adt _ -> true | _ -> false) user_srts in
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
      (if has_adt then solver.info.dt_logic_string else "") ^
      (if !Config.use_bitvector then "BV" else
       if has_int then if has_adt then "LIA" else "NIA" else "") ^
      (if solver.info.has_set_theory && !Config.use_set_theory then "FS" else "")
    in
    set_logic state.out_chan logic_str;
  in
  iter_solvers session set_logic;
  (* write benchmark description *)
  if !Config.dump_smt_queries then begin
    writeln session ("(set-info :source |
  GRASShopper benchmarks.
  Authors: Siddharth Krishna, Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:\n  " ^ session.sat_means ^ "
  |)")
  end;
  writeln session ("(set-info :smt-lib-version 2.0)");
  writeln session ("(set-info :category \"crafted\")");
  writeln session ("(set-info :status \"unknown\")");
  (* declare all sorts *)
  let session =
    { session with
      signature = Some sign;
      user_sorts = user_srts
    }
  in
  declare_sorts has_int session;
  session

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
    close_out state.out_chan;
    Opt.iter close_in state.in_chan;
    (match solver.info.kind with
    | Process _ -> 
        (try Unix.kill state.pid Sys.sigkill 
        with Unix.Unix_error _ -> ())
        (*ignore (Unix.close_process (Opt.get state.in_chan, state.out_chan))*)
    | _ -> ()));
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

let string_of_symbol = function
  | Div -> "div"
  | Mod -> "mod"
  | Empty -> "emptyset"
  | Elem -> "member"
  | SubsetEq -> "subset"
  | Union -> "union"
  | Inter -> "intersection"
  | Diff -> "setminus"
  | sym -> Grass.string_of_symbol sym
    
let smtlib_symbol_of_grass_symbol_no_bv solver_info sym = match sym with 
  | FreeSym id -> SmtLibSyntax.Ident id
  | Plus -> SmtLibSyntax.Plus
  | Minus | UMinus -> SmtLibSyntax.Minus
  | Mult -> SmtLibSyntax.Mult
  | Div -> SmtLibSyntax.Div
  | Mod -> SmtLibSyntax.Mod
  | Eq -> SmtLibSyntax.Eq
  | LtEq -> SmtLibSyntax.Leq
  | GtEq -> SmtLibSyntax.Geq
  | Lt -> SmtLibSyntax.Lt
  | Gt -> SmtLibSyntax.Gt
  | Ite -> SmtLibSyntax.Ite
  | Constructor id | Destructor id -> SmtLibSyntax.Ident id
  | BitAnd -> failwith "bitwise and requires bitvector theory."
  | BitOr -> failwith "bitwise or requires bitvector theory."
  | BitNot -> failwith "bitwise not requires bitvector theory."
  | ShiftLeft -> failwith "shift left requires bitvector theory."
  | ShiftRight -> failwith "shift right requires bitvector theory."
  | ByteToInt -> failwith "Byte to Int requires bitvector theory."
  | IntToByte -> failwith "Int to Byte requires bitvector theory."
  | (Read | Write) when !Config.encode_fields_as_arrays -> SmtLibSyntax.Ident (string_of_symbol sym, 0)
  | (IntConst _ | BoolConst _) as sym -> SmtLibSyntax.Ident (string_of_symbol sym, 0)
  | sym -> SmtLibSyntax.Ident (grass_smtlib_prefix ^ (string_of_symbol sym), 0)

let smtlib_symbol_of_grass_symbol_bv solver_info sym = match sym with 
  | FreeSym id -> SmtLibSyntax.Ident id
  | Plus -> SmtLibSyntax.BvAdd
  | Minus -> failwith "bitvector theory does not have subtraction."
  | UMinus -> SmtLibSyntax.BvNeg
  | Mult -> SmtLibSyntax.BvMul
  | Div -> SmtLibSyntax.BvSdiv
  | Eq -> SmtLibSyntax.Eq
  | LtEq -> SmtLibSyntax.BvSle
  | GtEq -> SmtLibSyntax.BvSge
  | Lt -> SmtLibSyntax.BvSlt
  | Gt -> SmtLibSyntax.BvSgt
  | Ite -> SmtLibSyntax.Ite
  | Constructor id | Destructor id -> SmtLibSyntax.Ident id
  | BitAnd -> SmtLibSyntax.BvAnd
  | BitOr -> SmtLibSyntax.BvOr
  | BitNot -> SmtLibSyntax.BvNot
  | ShiftLeft -> SmtLibSyntax.BvShl
  | ShiftRight -> SmtLibSyntax.BvShr
  | ByteToInt -> SmtLibSyntax.BvConcat
  | IntToByte -> SmtLibSyntax.BvExtract (7, 0)
  | (Read | Write) when !Config.encode_fields_as_arrays -> SmtLibSyntax.Ident (string_of_symbol sym, 0)
  | (IntConst _ | BoolConst _) as sym -> SmtLibSyntax.Ident (string_of_symbol sym, 0)
  | sym -> SmtLibSyntax.Ident (grass_smtlib_prefix ^ (string_of_symbol sym), 0)

let smtlib_symbol_of_grass_symbol solver_info sym =
  if !Config.use_bitvector then smtlib_symbol_of_grass_symbol_bv solver_info sym
  else smtlib_symbol_of_grass_symbol_no_bv solver_info sym

let grass_symbol_of_smtlib_symbol signs solver_info =
  let to_string sym =
    SmtLibSyntax.string_of_symbol
      (smtlib_symbol_of_grass_symbol solver_info sym)
  in
  let symbol_map =
    List.fold_left
      (fun acc sym ->
        try (to_string sym, sym) :: acc
        with _ -> acc)
      []
      symbols
  in
  function (name, _) as id ->
    List.assoc_opt name symbol_map |>
    (* ADT constructor/destructor? *)
    Opt.lazy_or_else (fun () ->
      if SymbolMap.mem (Constructor id) signs
      then Some (Constructor id)
      else if SymbolMap.mem (Destructor id) signs
      then Some (Destructor id)
      else None) |>
    Opt.get_or_else (FreeSym id)

let bitvectorize_grass_formula formula =
  let rec process_term t = match t with
    | Var _ -> t
    | App (sym, ts, srt) ->
      begin
        match App (sym, List.map process_term ts, srt) with
        | App (Minus, [a;b], srt) -> App (Plus, [a; mk_uminus b], srt)
        | App (ShiftLeft, [a;b], Byte) -> App (ShiftLeft, [a; mk_int_to_byte b], Byte)
        | App (ShiftRight, [a;b], Byte) -> App (ShiftRight, [a; mk_int_to_byte b], Byte)
        | other -> other
      end
  in
  let rec process_form t = match t with
    | BoolOp (bop, fs) -> BoolOp (bop, List.map process_form fs)
    | Binder (a, b, f, c) -> Binder(a, b, process_form f, c)
    | Atom (a, annot) ->
      match process_term a with
      | App (LtEq, [a;b], srt) -> mk_not (Atom ((App (Lt, [b;a], srt)), annot))
      | App (GtEq, [a;b], srt) -> mk_not (Atom ((App (Lt, [a;b], srt)), annot))
      | App (Gt, [a;b], srt) -> Atom(App (Lt, [b;a], srt), annot)
      | other -> Atom (other, annot)
  in
    process_form formula

let is_interpreted solver_info sym = match sym with
  | Read | Write -> !Config.encode_fields_as_arrays
  | Empty | SetEnum | Union | Inter | Diff | Elem | SubsetEq | Disjoint ->
      !Config.use_set_theory && solver_info.has_set_theory
  | Eq | Gt | Lt | GtEq | LtEq | IntConst _ | BoolConst _
  | Plus | Minus | Mult | Div | Mod | UMinus | Ite
  | BitNot | BitAnd | BitOr | ShiftLeft | ShiftRight
  | Constructor _ | Destructor _
  | IntToByte | ByteToInt -> true
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
  let session = init_session session sign in
  SymbolMap.iter write_decl sign;
  writeln session "";
  session

let extract_name ann =
  let names = Util.filter_map 
      (function Name _ -> !Config.named_assertions | _ -> false) 
      (function Name id -> string_of_ident id | _ -> "")
      ann 
  in
  Str.global_replace (Str.regexp " \\|,\\|(\\|)\\|<\\|>") "_" (String.concat "-" (List.rev names))

let smtlib_form_of_grass_form solver_info signs f =
  let f = if !Config.use_bitvector then bitvectorize_grass_formula f else f in
  let osym sym sign =
    if is_interpreted solver_info sym 
    then smtlib_symbol_of_grass_symbol solver_info sym
    else
      SymbolMap.find_opt sym signs |>
      Opt.get_or_else [] |>
      Util.find_index sign |>
      Opt.map
        (fun version -> SmtLibSyntax.Ident (mk_ident (string_of_overloaded_symbol solver_info sym version))) |>
      Opt.lazy_get_or_else (fun () -> smtlib_symbol_of_grass_symbol solver_info sym)
  in
  let bv_lit w i = SmtLibSyntax.mk_app (BvConst (w,i)) [] in
  let rec cterm t = match t with
  | Var (id, _) -> SmtLibSyntax.mk_app (SmtLibSyntax.Ident id) []
  | App (IntConst i, [], Int) when !Config.use_bitvector -> bv_lit 32 i
  | App (IntConst i, [], Byte) when !Config.use_bitvector -> bv_lit 8 i
  | App (ByteToInt, [a], srt) -> SmtLibSyntax.mk_app BvConcat  [bv_lit 24 Int64.zero; cterm a]
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
  let rec has_no_plus = function
    | App ((Plus | Mult), ts, _) -> not @@ List.exists (is_pattern true) ts
    | App (_, ts, _) -> List.for_all has_no_plus ts
    | _ -> true
  in
  let find_annot_patterns acc a =
    List.fold_left (fun acc -> function Pattern (t, []) -> TermSet.add t acc | _ -> acc) acc a
  in
  let rec find_patterns acc = function
    | BoolOp (_, fs) ->
        List.fold_left find_patterns acc fs
    | Binder (_, [], f, a) ->
        let acc = find_annot_patterns acc a in
        find_patterns acc f
    | Binder (_, vs, f, _) -> acc
    | Atom (App (_, ts, _), a) ->
        let acc = find_annot_patterns acc a in
        let pts = List.filter (is_pattern false &&& has_no_plus) ts in
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
      let is_term_gen_axiom =
        List.exists (function Comment "term_generator" -> true | _ -> false) a
      in
      let fun_patterns =
        if is_term_gen_axiom
        then TermSet.empty
        else find_patterns TermSet.empty f
      in
      let annot_patterns =
        List.fold_left (fun patterns -> function
          | Pattern (t, _) -> TermSet.add t patterns
          | _ -> patterns) fun_patterns a
      in
      let patterns =
        let pvs = 
          TermSet.fold 
            (fun t pvs -> IdSet.union (fv_term t) pvs)
            annot_patterns IdSet.empty
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
          annot_patterns vs
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
    | Atom (_, ann)
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
  (* get result sort of symbol *)
  let signs = Opt.get_or_else SymbolMap.empty session.signature in
  let sort_map = session.user_sorts in
  let get_result_sort model sym arg_srts =
    SymbolMap.find_opt sym signs |>
    Opt.flat_map (List.assoc_opt arg_srts) |>
    Opt.lazy_or_else (fun () -> Model.get_result_sort model sym arg_srts)
  in
  (* convert SMT-LIB sort to GRASS sort *)
  let rec convert_sort = function
    | IntSort -> Int
    | BoolSort -> Bool
    | BvSort i ->
      if i = 8 then Byte
      else if i = 32 then Int
      else failwith ("no equivalent for bitvector of size " ^ (string_of_int i))
    | AdtSort (id, adts) ->
        let adts1 =
          List.map (fun (id, cs) ->
            (id, List.map
               (fun (id, args) ->
                 (id, List.map (fun (id, srt) -> (id, convert_sort srt)) args))
               cs)) adts
        in
        Adt (id, adts1)
    | FreeSort ((name, num), srts) ->
        let csrts = List.map convert_sort srts in
        match name, csrts with
        | "Loc", [esrt] -> Loc esrt
        | "Set", [esrt] -> Set esrt
        | "GrassArray", [esrt] -> Array esrt
        | "GrassPat", [] -> Pat
        | "ArrayCell", [esrt] -> ArrayCell esrt
        | "Map", (_ :: _ as srts) ->
            let srts_rev = List.rev srts in
            let rsrt = List.hd srts_rev in
            let dsrts = List.rev (List.tl srts_rev) in
            Map (dsrts, rsrt)
        | _ ->
            try
              IdMap.find (name, num) sort_map
            with Not_found ->
              fail session ("encountered unexpected sort " ^ name ^ " in model conversion")
  in
  (* solver_info for symbol conversion *)
  let solver_info = (fst (List.hd session.solvers)).info in
  let to_sym = grass_symbol_of_smtlib_symbol signs solver_info in
  (* remove suffix from overloaded identifiers *)
  let normalize_ident =
    let name_re = Str.regexp "\\([^\\$]*\\)\\$[0-9]+$" in
    let num_re = Str.regexp "\\(.*\\)\\^\\([0-9]+\\)$" in
    fun ((name, num) as id) -> 
      if Str.string_match name_re name 0 then
        let nname = Str.matched_group 1 name in
        if Str.string_match num_re nname 0 then
          (Str.matched_group 1 nname, int_of_string (Str.matched_group 2 nname))
        else (nname, 0)
      else id
  in
  let fail pos_opt = 
    let pos = match pos_opt with
    | Some pos -> pos
    | None -> dummy_position
    in
    let msg = 
      ProgError.error_to_string pos
        "Encountered unexpected definition during model conversion" 
    in failwith msg
  in
  (* convert SMT-LIB term to GRASS term *)
  let rec convert_term model res_srt bvs t =
    let ct = match t with
    | SmtLibSyntax.App (SmtLibSyntax.And as op, ts, _)
    | SmtLibSyntax.App (SmtLibSyntax.Or as op, ts, _) ->
        let cts = List.map (convert_term model res_srt bvs) ts in
        (match op with
        | SmtLibSyntax.And -> mk_app Bool AndTerm cts
        | SmtLibSyntax.Or -> mk_app Bool OrTerm cts
        | _ -> failwith "unexpected match case")
    | SmtLibSyntax.App (SmtLibSyntax.BoolConst b, [], _) -> 
        mk_bool_term b
    | SmtLibSyntax.App (SmtLibSyntax.IntConst i, [], _) -> 
        mk_int i
    | SmtLibSyntax.App (Ident (name, _), [], pos) when name = "#unspecified" -> mk_undefined res_srt
    | SmtLibSyntax.App (Ident id, ts, pos) ->
        let cts = List.map (convert_term model res_srt bvs) ts in
        let id = normalize_ident id in
        let sym = to_sym id in
        let ts_srts = List.map sort_of cts in
        let res_srt = 
          get_result_sort model sym ts_srts |>
          Opt.lazy_or_else (fun () -> List.assoc_opt id bvs) |>
          Opt.lazy_get_or_else (fun () -> res_srt)
        in
        (match to_sym id with
        | Constructor id ->
            mk_constr res_srt id cts
        | sym ->
            (* detect Z3/CVC4 identifiers that represent values of uninterpreted sorts *)
            let name, num = id in
            let var_id = name ^ "_" ^ string_of_int num in
            let z3_val_re = Str.regexp "\\([^!]*\\)!val!\\([0-9]*\\)" in
            let cvc4_val_re = Str.regexp "@uc__\\(.*\\)__\\([0-9]*\\)$" in
            let cvc4_val_simple_re = Str.regexp "@uc_\\(.*\\)_\\([0-9]*\\)$" in
            if Str.string_match z3_val_re var_id 0 ||
               Str.string_match cvc4_val_re var_id 0 ||
               Str.string_match cvc4_val_simple_re var_id 0
            then begin
              let index = Int64.of_string (Str.matched_group 2 var_id) in 
              let v = mk_app res_srt (Value index) [] in
              Model.add_univ model v;
              v
            end
            else if List.exists (fun (id2, _) -> id = id2) bvs 
            then mk_var res_srt id
            else mk_app res_srt sym cts)
    | SmtLibSyntax.App (SmtLibSyntax.Eq, [t1; t2], _) ->
        let t1_srt =
          let open SmtLibSyntax in
          match t1 with
          | App ((Plus | Mult | Minus | Div | Mod | IntConst _), _, _) -> Some Int
          | App (Ident id, _, _)
          | App (Ite, [App (Eq, [App (Ident id, _, _); _], _); _; _], _) -> List.assoc_opt id bvs
          | _ -> None
        in
        let ct1 = convert_term model (t1_srt |> Opt.get_or_else res_srt) bvs t1 in
        let ct2 = convert_term model (sort_of ct1) bvs t2 in
        mk_eq_term ct1 ct2
    | SmtLibSyntax.App (SmtLibSyntax.Plus as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Mult as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Minus as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Div as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Mod as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Lt as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Gt as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Leq as op, [t1; t2], _)
    | SmtLibSyntax.App (SmtLibSyntax.Geq as op, [t1; t2], _) ->
        let ct1 = convert_term model Int bvs t1 in
        let ct2 = convert_term model Int bvs t2 in
        let mk_term = match op with
        | SmtLibSyntax.Plus -> mk_plus
        | SmtLibSyntax.Minus -> mk_minus
        | SmtLibSyntax.Mult -> mk_mult
        | SmtLibSyntax.Div -> mk_div
        | SmtLibSyntax.Mod -> mk_mod
        | SmtLibSyntax.Lt -> (fun s t -> mk_app (sort_of s) Lt [s; t])
        | SmtLibSyntax.Gt -> (fun s t -> mk_app (sort_of s) Gt [s; t])
        | SmtLibSyntax.Leq -> (fun s t -> mk_app (sort_of s) LtEq [s; t])
        | SmtLibSyntax.Geq -> (fun s t -> mk_app (sort_of s) GtEq [s; t])
        | _ -> failwith "unexpected match case"
        in mk_term ct1 ct2          
    | SmtLibSyntax.App (SmtLibSyntax.Ite, [cond; t; e], _) ->
        let cond1 = convert_term model Bool bvs cond in
        let t1 = convert_term model res_srt bvs t in
        let e1 = convert_term model res_srt bvs e in
        mk_ite cond1 t1 e1
    | SmtLibSyntax.Annot (t, _, _) ->
        convert_term model res_srt bvs t
    | SmtLibSyntax.App (_, _, pos)
    | SmtLibSyntax.Binder (_, _, _, pos) 
    | SmtLibSyntax.Let (_, _, pos) -> fail pos
    in
    match ct with
    | App (FreeSym (id2, _) as sym2, ts, srt) as t1 ->
        (* Z3-specific work around *)
        let re = Str.regexp "k![0-9]+" in
        if Str.string_match re id2 0 then
          let args, def = Model.get_interp model sym2 (List.map sort_of ts, srt) in
          let sm = List.fold_left2 (fun sm (id, _) t -> IdMap.add id t sm) IdMap.empty args ts in
          subst_term sm def
        else t1
    | ct -> ct
  in
  (* Construct model by converting all predicate and function definitions *)
  let model1 =
    List.fold_left 
      (fun model cmd ->
        match cmd with
        | DefineFun (id, args, res_srt, def, _) ->
            let sym = to_sym (normalize_ident id) in
            if sym = Known then model else
            let cres_srt = convert_sort res_srt in
            let cargs = List.map (fun (x, srt) -> x, convert_sort srt) args in
            let carg_srts = List.map snd cargs in
            (try
              let cdef =  convert_term model cres_srt cargs (SmtLibSyntax.unletify def) in
              Model.add_interp model sym (carg_srts, cres_srt) cargs cdef
            with Failure s -> 
              if !Config.model_file <> "" then Debug.warn (fun () -> "Warning: " ^ s ^ "\n\n");
              model)
        | _ -> model)
      Model.empty smtModel 
  in
  let model2 = 
    match session.signature with
    | Some signature ->
      { model1 with sign = signature }
    | None -> failwith "convert_model: expected session to have a signature"
  in
  Model.complete model2
    
let rec get_model session = 
  let gm state =
    writeln session "(get-model)";
    flush state.out_chan;
    match snd (read session) with
    | Model m -> 
        let cm = convert_model session m in
        (match session.signature with
        | Some sign -> Some (Model.restrict_to_sign cm sign)
        | None -> Some cm)
    | Unsat -> None
    | Error e -> fail session e
    | Unknown -> fail session "unexpected solver response: unknown"
    | Sat -> fail session "unexpected solver response: sat"
    | UnsatCore _ -> fail session "unexpected solver response: unsatcore"
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
        try [Hashtbl.find tbl (n ^ "^0")]
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
	  
