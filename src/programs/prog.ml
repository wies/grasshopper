open Util
open Grass
open GrassUtil
open Axioms

(** Alloc sets *)

(* when building the axioms it will be good to use this name generator to generate names for struct sort functions *)
let mk_name_generator base_name =
  let set_ids = Hashtbl.create 0 in
  fun ?(aux_name="") srt ->
    let name = base_name ^ aux_name ^ "_" ^ (name_of_sort srt) in
    try Hashtbl.find set_ids (name, srt)
    with Not_found ->
      let id = fresh_ident name in
      Hashtbl.replace set_ids (name, srt) id;
      id
  
let alloc_id = mk_name_generator "Alloc"
        
let alloc_set struct_srt = mk_loc_set struct_srt (alloc_id struct_srt)

(** Specification formulas *)

type spec_form =
  | SL of Sl.form 
  | FOL of form 
   
type spec_kind =
  | Free | Checked

(** Predicate fold/unfold enum *)
type pred_exchange =
  | Unfold | Fold

(** Assume or assert of pure formula *)
type spec = {
    spec_form: spec_form;
    spec_kind: spec_kind;
    spec_name: string;
    spec_msg: (ident -> (string * string)) option;
    spec_pos: source_position;
  } 
      
(** Commands *)

(** Assignment, x_1,...,x_n := e_1,...,e_n *)
type assign_command = {
    assign_lhs: ident list; (** name of the assigned variables *)
    assign_rhs: term list; (** assigned values *)
  }

(** Havoc, havoc x_1, ..., x_n *)
type havoc_command = {
    havoc_args: ident list;
  } 

(** Allocation, x := new T(t_1, ..., t_n) *)
type new_command = {
    new_lhs: ident;
    new_sort: sort;
    new_args: term list;
  }

(** Deallocation, free x *)
type dispose_command = {
    dispose_arg: term;
  }

(** Procedure call, x_1,..., x_n := p(e_1,...,e_m) *)
type call_command = {
    call_lhs: ident list; (** x_1,...,x_n *)
    call_name: ident; (** p *)
    call_args: term list; (** e_1,...,e_m *)
    call_modifies: IdSet.t;
    call_accesses: IdSet.t;
  } 

(** Return from procedure *)
and return_command = {
    return_args: term list;
  }

(** predicate unfold/fold, unfold q(e_1,...,e_m) *)
type predicate_command = {
  pred_action: pred_exchange; (** unfold/fold *)
  pred_name: ident;
  pred_args: term list; (** e_1,...,e_m *)
}

(** Basic commands *)
type basic_command =
  | Assign of assign_command
  | Havoc of havoc_command
  | New of new_command
  | Dispose of dispose_command
  | Assume of spec
  | Assert of spec
  | Split of spec
  | Call of call_command
  | Return of return_command
  | Unfold of predicate_command
  | Fold of predicate_command

(** Program point *)
type program_point = {
    pp_pos: source_position; (** the source position of the program fragment *)
    pp_modifies: IdSet.t; (** the set of modified variables of the program fragment *)
    pp_accesses: IdSet.t; (** the set of accessed variables of the program fragment *)
  }

(** Loop *)
type loop_command = {
    loop_inv: spec list; (** the loop invariant *)
    loop_prebody: command; (** the command executed before each test of the loop condition *)
    loop_test: form; (** the loop condition *)
    loop_test_pos: source_position; (** source code position of loop condition *)
    loop_postbody: command; (** the actual loop body *)
  }

(** Compound commands *)
and command =
  | Loop of loop_command * program_point
  | Choice of command list * program_point
  | Seq of command list * program_point
  | Basic of basic_command * program_point

(** Variable declaration *)
type var_decl = {
    var_name: ident; (** variable name *)
    var_orig_name: string; (** original name *)
    var_sort: sort; (** variable type *)
    var_is_ghost: bool; (** whether the variable is ghost *)
    var_is_implicit: bool; (** whether the variable is implicit *)
    var_is_aux: bool; (** whether the variable is an auxiliary variable *)
    var_pos: source_position; (** position of the variable declaration *)
    var_scope: source_position; (** scope of the variable *)
  }

(** Procedure/predicate contract *)
type contract = {
    contr_name: ident; (** name of procedure/contract *)
    contr_formals: ident list;  (** formal parameter list *)
    contr_returns: ident list; (** return parameter list *)
    contr_locals: var_decl IdMap.t; (** all local variables *)    
    contr_precond: spec list; (** precondition *)
    contr_postcond: spec list; (** postcondition *)
    contr_footprint_sorts: SortSet.t; (** footprint sorts *)
    contr_is_pure: bool; (** has no state dependencies *)
    contr_pos: source_position; (** position of declaration *)
  }
      
(** Procedure declaration *)
type proc_decl = {
    proc_contract: contract; (** contract *)
    proc_body: command option; (** procedure body *)
    proc_deps: ident list; (** names of dependent procedures *)
    proc_is_tailrec: bool; (** whether the procedure is tail recursive *)
    proc_is_lemma: bool;  (** whether this procedure is a lemma *)
    proc_is_auto: bool; (** whether this lemma should be automatically applied *)
  }

(** Predicate declaration *)
type pred_decl = {
    pred_contract: contract; (** contract *)
    pred_body: spec option; (** predicate body *)
    pred_accesses: IdSet.t; (** accessed variables *)
    pred_is_self_framing: bool; (** predicate is a footprint function *)
    pred_was_sl_pred: bool; (** predicate is a translated SL predicate *)
  } 

(** Program *)
type program = {
    prog_axioms: spec list; (** background axioms *)
    (* fields are stored in this global var map, map<Loc<T>> *)
    prog_vars: var_decl IdMap.t; (** global variables *)
    prog_preds: pred_decl IdMap.t; (** predicates *)
    prog_procs: proc_decl IdMap.t; (** procedures *)
    prog_state_vars: IdSet.t (** names of all state-dependent variables *)
  } 

(** Auxiliary functions for program points *)

let start_pos pos = 
  { pos with
    sp_end_line = pos.sp_start_line;
    sp_end_col = pos.sp_start_col;
  }

let end_pos pos = 
  { pos with
    sp_start_line = pos.sp_end_line;
    sp_start_col = pos.sp_end_col;
  }

let mk_ppoint pos = 
  { pp_pos = pos; 
    pp_modifies = IdSet.empty;
    pp_accesses = IdSet.empty;
  }

let update_ppoint pp = function
  | Loop (lc, _) -> Loop (lc, pp)
  | Choice (cs, _) -> Choice (cs, pp)
  | Seq (cs, _) -> Seq (cs, pp)
  | Basic (bc, _) -> Basic (bc, pp)

let prog_point = function
  | Loop (_, pp) | Choice (_, pp) | Seq (_, pp) | Basic (_, pp) -> pp

let source_pos c = (prog_point c).pp_pos


(** Auxiliary functions for programs and declarations *)

let mk_loc_set_decl struct_srt id pos =
  { var_name = id;
    var_orig_name = name id;
    var_sort = Set (Loc struct_srt);
    var_is_ghost = true;
    var_is_implicit = false;
    var_is_aux = true;
    var_pos = pos;
    var_scope = global_scope
  }

let alloc_decl struct_id =
  mk_loc_set_decl struct_id (alloc_id struct_id) dummy_position

let alloc_all struct_id =
  alloc_decl struct_id,
  alloc_set struct_id,
  alloc_id struct_id
    
let empty_prog = 
  { prog_axioms = [];
    prog_vars = IdMap.empty;
    prog_preds = IdMap.empty;
    prog_procs = IdMap.empty;
    prog_state_vars = IdSet.empty;
  }

let trivial_contract name =
  { contr_name = name;
    contr_formals = [];
    contr_returns = [];
    contr_locals = IdMap.empty;
    contr_pos = dummy_position;
    contr_precond = [];
    contr_postcond = [];
    contr_is_pure = false;
    contr_footprint_sorts = SortSet.empty;
  }
    
let dummy_proc name = 
  { proc_contract = trivial_contract name;
    proc_body = None;
    proc_deps = [];
    proc_is_tailrec = false;
    proc_is_lemma = false;
    proc_is_auto = false;
  }

let name_of_pred decl = decl.pred_contract.contr_name
let name_of_proc decl = decl.proc_contract.contr_name

let locals_of_pred decl = decl.pred_contract.contr_locals
let locals_of_proc decl = decl.proc_contract.contr_locals

let formals_of_pred decl = decl.pred_contract.contr_formals
let formals_of_proc decl = decl.proc_contract.contr_formals

let returns_of_pred decl = decl.pred_contract.contr_returns
let returns_of_proc decl = decl.proc_contract.contr_returns

let pos_of_pred decl = decl.pred_contract.contr_pos
let pos_of_proc decl = decl.proc_contract.contr_pos

let precond_of_pred decl = decl.pred_contract.contr_precond
let precond_of_proc decl = decl.proc_contract.contr_precond

let postcond_of_pred decl = decl.pred_contract.contr_postcond
let postcond_of_proc decl = decl.proc_contract.contr_postcond

    
let declare_global prog var =
  { prog with prog_vars = IdMap.add var.var_name var prog.prog_vars }

let declare_pred prog pred =
  { prog with prog_preds = IdMap.add (name_of_pred pred) pred prog.prog_preds }

let declare_proc prog proc =
  { prog with prog_procs = IdMap.add (name_of_proc proc) proc prog.prog_procs }


let procs prog = IdMap.fold (fun _ proc procs -> proc :: procs) prog.prog_procs []

let preds prog = IdMap.fold (fun _ pred preds -> pred :: preds) prog.prog_preds []

let vars prog = IdMap.fold (fun _ var vars -> var :: vars) prog.prog_vars []

let var_ids prog = IdMap.fold (fun id _ ids -> IdSet.add id ids) prog.prog_vars IdSet.empty 
    
let find_proc prog name =
  try IdMap.find name prog.prog_procs 
  with Not_found -> 
    failwith ("find_proc: Could not find procedure " ^ (string_of_ident name))

let find_proc_with_deps prog name =
  let rec find names procs =
    let new_procs = 
      Util.flat_map 
        (fun name -> 
          try [IdMap.find name prog.prog_procs] 
          with Not_found -> [])
        names
    in
    let new_deps =
      Util.flat_map (fun proc -> proc.proc_deps) new_procs 
    in
    match new_deps with
    | [] -> new_procs @ procs
    | _ -> find new_deps (new_procs @ procs)
  in
  find [name] []
    
let find_pred prog name =
  try IdMap.find name prog.prog_preds
  with Not_found -> 
    failwith ("find_proc: Could not find predicate " ^ (string_of_ident name))

let find_global prog name = 
  try IdMap.find name prog.prog_vars
  with Not_found -> 
    failwith ("find_proc: Could not find global variable " ^ (string_of_ident name))

let find_var prog proc name =
  try
    try IdMap.find name (locals_of_proc proc)
    with Not_found -> IdMap.find name prog.prog_vars
  with Not_found ->
    failwith ("find_var: Could not find variable " ^ (string_of_ident name))

let find_local_var proc name =
  try IdMap.find name (locals_of_proc proc)
  with Not_found ->
    failwith ("find_local_val: Could not find variable " ^ string_of_ident name)
      
let mk_fresh_var_decl decl =
  let id = fresh_ident (name decl.var_name) in
  { decl with 
    var_name = id;
    var_orig_name = name id; 
  }

let fold_procs fn init prog =
  IdMap.fold (fun _ proc acc -> fn acc proc) prog.prog_procs init

let map_procs fn prog =
  { prog with prog_procs = IdMap.map fn prog.prog_procs }

let iter_procs fn prog =
  IdMap.iter (fun _ proc -> fn prog proc) prog.prog_procs

let fold_preds fn init prog =
  IdMap.fold (fun _ pred acc -> fn acc pred) prog.prog_preds init

let map_preds fn prog =
  { prog with prog_preds = IdMap.map fn prog.prog_preds }

let struct_sorts prog =
  let collect_srts decls =
    let rec cs struct_srts = function
      | Loc srt -> SortSet.add srt struct_srts
      | Map (dom_srts, res_srt) ->
          List.fold_left cs struct_srts (res_srt :: dom_srts)
      | Array srt | ArrayCell srt | Set srt ->
          cs struct_srts srt
      | _ -> struct_srts
    in
    IdMap.fold
      (fun _ decl struct_srts -> cs struct_srts decl.var_sort)
      decls 
  in
  let struct_srts = 
    collect_srts prog.prog_vars SortSet.empty
  in
  fold_procs (fun struct_srts proc ->
    collect_srts (locals_of_proc proc) struct_srts)
    struct_srts prog

let add_proc prog proc =
  { prog with prog_procs = IdMap.add (name_of_proc proc) proc prog.prog_procs }
    
(** Auxiliary functions for specifications *)

let mk_spec_form f name msg pos =
  { spec_form = f;
    spec_kind = Checked;
    spec_name = name;
    spec_msg = msg;
    spec_pos = pos;
  }

let mk_free_spec_form f name msg pos =
  { spec_form = f;
    spec_kind = Free;
    spec_name = name;
    spec_msg = msg;
    spec_pos = pos;
  } 


let fold_spec_form fol_fn sl_fn sf =
  match sf.spec_form with
  | FOL f -> fol_fn f
  | SL f -> sl_fn f

let map_spec_form fol_fn sl_fn sf =
  let sf1 = match sf.spec_form with
  | FOL f -> FOL (fol_fn f)
  | SL f -> SL (sl_fn f)
  in
  { sf with spec_form = sf1 }

let map_spec_fol_form fn sf =
  let sf1 = match sf.spec_form with
  | FOL f -> FOL (fn f)
  | f -> f
  in
  { sf with spec_form = sf1 }

let map_spec_sl_form fn sf =
  let sf1 = match sf.spec_form with
  | SL f -> fn f
  | f -> f
  in
  { sf with spec_form = sf1 }

let is_checked_spec sf =
  match sf.spec_kind with
  | Free -> false
  | Checked -> true

let is_free_spec sf =
  match sf.spec_kind with
  | Free -> true
  | Checked -> false

let is_sl_spec sf =
  match sf.spec_form with
  | SL _ -> true
  | FOL _ -> false

let is_pure_spec sf =
  match sf.spec_form with
  | FOL _ | SL (Sl.Pure _) -> true
  | _ -> false

let is_pure_pred pred =
  List.for_all is_pure_spec (Opt.to_list pred.pred_body @ precond_of_pred pred) &&
  (pred.pred_body <> None || pred.pred_contract.contr_returns <> [])

let is_sl_pred pred =
  not (Opt.get_or_else (pred.pred_contract.contr_returns <> []) (Opt.map is_pure_spec pred.pred_body))
        
let form_of_spec sf =
  match sf.spec_form with
  | FOL f -> f
  | SL _ -> failwith "expected FOL specification in Prog.form_of_spec"

let sl_of_spec sf =
  match sf.spec_form with
  | SL f -> f
  | FOL _ -> failwith "expected SL specification in Prog.sl_of_spec"
    
        
let map_terms_spec fn sf =
  match sf.spec_form with
  | FOL f -> { sf with spec_form = FOL (map_terms fn f) }
  | SL f -> { sf with spec_form = SL (SlUtil.map_terms fn f) }
        
(** Substitute all occurrences of identifiers in [sf] according to substitution map [sm] *)
let subst_id_spec sm sf =
  match sf.spec_form with
  | FOL f -> 
      { sf with 
        spec_form = FOL (subst_id sm f);      
      }
  | SL f -> 
      { sf with 
        spec_form = SL (SlUtil.subst_id sm f);
      }
  
let subst_spec sm sf =
  match sf.spec_form with
  | FOL f -> 
      { sf with 
        spec_form = FOL (subst_consts sm f);
      }
  | SL ssf ->
      { sf with 
        spec_form = SL (SlUtil.subst_consts sm ssf);
      }
        
let old_prefix = "$old_"

let oldify (name, num) = (old_prefix ^ name, num)

let oldify_term vars t =
  let subst_map = 
    IdSet.fold (fun var subst_map ->
      IdMap.add var (oldify var) subst_map)
      vars IdMap.empty
  in subst_id_term subst_map t


let oldify_form vars f =
  let subst_map = 
    IdSet.fold (fun var subst_map ->
      IdMap.add var (oldify var) subst_map)
      vars IdMap.empty
  in subst_id subst_map f


let oldify_sl_form vars f =
  let subst_map = 
    IdSet.fold (fun var subst_map ->
      IdMap.add var (oldify var) subst_map)
      vars IdMap.empty
  in SlUtil.subst_id subst_map f


let oldify_spec vars sf =
  let old_form =
    match sf.spec_form with
    | FOL f -> FOL (oldify_form vars f)
    | SL f -> SL (oldify_sl_form vars f)
  in 
  { sf with 
    spec_form = old_form;
  }


let elim_old_term vars t =
  let rec e = function
    | App (Old, [t], _) ->
        oldify_term vars t |> e
    | App (sym, ts, srt) ->
        App (sym, List.map e ts, srt)
    | Var _ as t -> t
  in e t
    

let elim_old_form vars f =
  map_terms (elim_old_term vars) f

let rec old_to_fun_term = function
  | App (FreeSym (name, num as id), [], srt) ->
      let old_name = Str.regexp (Str.quote old_prefix ^ "\\(.*\\)") in
      if Str.string_match old_name name 0 
      then
        let id1 = (Str.matched_group 1 name, num) in
        App (Old, [App (FreeSym id1, [], srt)], srt)
      else App (FreeSym id, [], srt)
  | App (sym, ts, srt) -> 
      App (sym, List.map old_to_fun_term ts, srt)
  | t -> t
    
let old_to_fun_form f = map_terms old_to_fun_term f

let old_to_fun_sl_form f = SlUtil.map_terms old_to_fun_term f

let unoldify =
  let old_name = Str.regexp (Str.quote old_prefix ^ "\\(.*\\)") in
  fun (name, num) ->
    if Str.string_match old_name name 0 
    then (Str.matched_group 1 name, num)
    else (name, num)
    
let unoldify_term t = 
  map_id_term unoldify t

let unoldify_form f =
  map_id unoldify f

let unoldify_spec sf =
  let unold_form =
    match sf.spec_form with
    | FOL f -> FOL (unoldify_form f)
    | SL f -> SL f (* TODO: unoldification for SL formulas *)
  in 
  { sf with 
    spec_form = unold_form;
  }

(** Auxiliary functions for commands *)

let modifies_cmd c = (prog_point c).pp_modifies
let accesses_cmd c = (prog_point c).pp_accesses

let modifies_proc prog proc = 
  match proc.proc_body with
  | Some cmd ->
      if !Config.opt_field_mod 
      then 
        IdSet.filter 
          (fun id -> IdMap.mem id prog.prog_vars) 
          (modifies_cmd cmd)
       else 
        IdMap.fold 
          (fun id _ mods -> IdSet.add id mods) 
          prog.prog_vars IdSet.empty
  | None ->
      if proc.proc_is_lemma then IdSet.empty else
      IdMap.fold (fun id decl acc ->
        match decl.var_sort with
        | Set (Loc srt) when id = alloc_id srt && not @@ SortSet.mem srt proc.proc_contract.contr_footprint_sorts ->
            acc
        | _ -> IdSet.add id acc) prog.prog_vars IdSet.empty

let modifies_basic_cmd = function
  | Assign ac -> id_set_of_list ac.assign_lhs
  | Havoc hc -> id_set_of_list hc.havoc_args
  | New nc ->
      let struct_sorts =
        match nc.new_sort with
        | Loc srt -> [srt]
        | Array srt -> [Array srt; ArrayCell srt]
        | _ -> []
      in
      List.fold_left
        (fun mods srt -> IdSet.add (alloc_id srt) mods)
        (IdSet.singleton nc.new_lhs)
        struct_sorts
  | Call cc ->
      IdSet.union (id_set_of_list cc.call_lhs) cc.call_modifies
  | Dispose dc ->
      let struct_sorts =
        match sort_of dc.dispose_arg with
        | Loc srt -> [srt]
        | Array srt -> [Array srt; ArrayCell srt]
        | _ -> []
      in
      List.fold_left
        (fun mods srt -> IdSet.add (alloc_id srt) mods)
        IdSet.empty
        struct_sorts
  | Assume _
  | Assert _
  | Split _
  | Unfold _
  | Fold _
  | Return _ -> IdSet.empty

let accesses_spec_form_acc acc sf =
  IdSet.union acc 
    (match sf.spec_form with
    | FOL f -> free_symbols f
    | SL f -> SlUtil.free_symbols f)

let accesses_spec_form sf = 
  accesses_spec_form_acc IdSet.empty sf

let accesses_contract_acc acc contr =
  List.fold_left accesses_spec_form_acc acc
    (contr.contr_precond @ contr.contr_postcond)
    
let accesses_proc prog proc = 
  let body_accs =
    match proc.proc_body with
    | Some cmd -> accesses_cmd cmd
    | None -> IdSet.empty
  in
  let auto_accs =
    IdMap.fold (fun id proc auto_accs ->
      if proc.proc_is_auto then
        IdSet.add id auto_accs
      else auto_accs)
      prog.prog_procs body_accs 
  in 
  let accs =
    IdSet.filter 
      (fun id ->
        IdMap.mem id prog.prog_vars ||
        IdMap.mem id prog.prog_procs ||
        IdMap.mem id prog.prog_preds)
      (accesses_contract_acc auto_accs proc.proc_contract)
  in
  IdMap.fold (fun id pred accs ->
    if IdSet.mem id accs
    then IdSet.union accs pred.pred_accesses
    else accs)
    prog.prog_preds accs
    
let accesses_pred pred =
  pred.pred_accesses

let accesses_basic_cmd = function
  | Assign ac -> 
      let rhs_accesses = 
        List.fold_left free_symbols_term_acc IdSet.empty ac.assign_rhs 
      in
      IdSet.union (id_set_of_list ac.assign_lhs) rhs_accesses
  | Havoc hc -> id_set_of_list hc.havoc_args
  | New nc ->
      let arg_accesses =
        List.fold_left free_symbols_term_acc IdSet.empty nc.new_args 
      in
      IdSet.add nc.new_lhs arg_accesses
  | Dispose dc -> free_symbols_term dc.dispose_arg
  | Assume sf
  | Assert sf
  | Split sf -> accesses_spec_form sf
  | Return rc -> List.fold_left free_symbols_term_acc IdSet.empty rc.return_args
  | Unfold pc
  | Fold pc ->  List.fold_left free_symbols_term_acc IdSet.empty pc.pred_args  
  | Call cc ->
      IdSet.union cc.call_accesses @@
      List.fold_left
        free_symbols_term_acc (id_set_of_list (cc.call_name :: cc.call_lhs)) cc.call_args

let rec footprint_sorts_acc acc = function
  | (Loc srt)
  | Set (Loc srt) -> SortSet.add srt acc
  | Map (srts, _) ->
      List.fold_left footprint_sorts_acc acc srts
  | _ -> acc

let footprint_sorts_pred pred = pred.pred_contract.contr_footprint_sorts
        
let footprint_sorts_term_acc prog acc t =
  let rec c acc = function
    | App (sym, ts, srt) ->
        let acc =
          match sym with
          | FreeSym id when IdMap.mem id prog.prog_preds ->
              let decl = find_pred prog id in
              SortSet.union (footprint_sorts_pred decl) acc
          | FreeSym id when IdSet.mem id prog.prog_state_vars ->
              footprint_sorts_acc acc srt
          | _ -> acc
        in
        (*let acc = footprint_sorts_acc acc srt in*)
        List.fold_left c acc ts
    | Var (_, srt) -> acc (*footprint_sorts_acc acc srt*)
  in
  c acc t

let footprint_sorts_term prog t = footprint_sorts_term_acc prog SortSet.empty t

let footprint_sorts_form_acc prog acc f = fold_terms (footprint_sorts_term_acc prog) acc f
    
let footprint_sorts_spec_form_acc prog acc sf =
  match sf.spec_form with
  | SL f ->
      let pids = SlUtil.preds f in
      let acc = IdSet.fold
          (fun id acc ->
            SortSet.union (footprint_sorts_pred (find_pred prog id)) acc)
          pids acc
      in
      let acc = SortSet.union acc (SlUtil.acc_srts f) in
      SlUtil.fold_terms (footprint_sorts_term_acc prog) acc f
  | FOL f -> footprint_sorts_form_acc prog acc f

let footprint_sorts_spec_form prog sf = footprint_sorts_spec_form_acc prog SortSet.empty sf

let footprint_sorts_proc proc =
  proc.proc_contract.contr_footprint_sorts
    
let footprint_sorts_basic_cmd prog = function
  | Assign ac -> 
      let rhs_fps = 
        List.fold_left (footprint_sorts_term_acc prog) SortSet.empty ac.assign_rhs 
      in
      rhs_fps
  | Havoc hc -> SortSet.empty
  | New nc ->
      List.fold_left (footprint_sorts_term_acc prog) SortSet.empty nc.new_args 
  | Dispose dc -> footprint_sorts_term prog dc.dispose_arg
  | Assume sf
  | Assert sf
  | Split sf -> footprint_sorts_spec_form prog sf
  | Unfold pc
  | Fold pc -> List.fold_left (footprint_sorts_term_acc prog) SortSet.empty pc.pred_args
  | Return rc -> List.fold_left (footprint_sorts_term_acc prog) SortSet.empty rc.return_args
  | Call cc ->
      let decl = find_proc prog cc.call_name in
      List.fold_left (footprint_sorts_term_acc prog) (footprint_sorts_proc decl) cc.call_args

let occuring_vars =
  let rec ov vars = function
    | Loop (lc, _) ->
        let vars1 = ov vars lc.loop_prebody in
        let vars2 = ov vars1 lc.loop_postbody in
        let vars3 = free_consts_acc vars2 lc.loop_test in
        List.fold_left (fun vars sf ->
          fold_spec_form (free_consts_acc vars) (SlUtil.free_consts_acc vars) sf)
          vars3 lc.loop_inv
    | Seq (cc, _) | Choice (cc, _) ->
        List.fold_left ov vars cc
    | Basic (bc, _) -> match bc with
      | Assign ac ->
          let vars1 = List.fold_left free_consts_term_acc vars ac.assign_rhs in
          List.fold_left (fun vars x -> IdSet.add x vars) vars1 ac.assign_lhs
      | Havoc hc ->
          List.fold_left (fun vars x -> IdSet.add x vars) vars hc.havoc_args
      | New nc ->
          List.fold_left free_consts_term_acc (IdSet.add nc.new_lhs vars) nc.new_args
      | Dispose dc ->
          free_consts_term_acc vars dc.dispose_arg
      | Assume sf | Assert sf | Split sf ->
          fold_spec_form (free_consts_acc vars) (SlUtil.free_consts_acc vars) sf
      | Return rc ->
          List.fold_left free_consts_term_acc vars rc.return_args
      | Unfold pc | Fold pc ->
          List.fold_left free_consts_term_acc vars pc.pred_args
      | Call cc ->
          let vars1 = List.fold_left free_consts_term_acc vars cc.call_args in
          List.fold_left (fun vars x -> IdSet.add x vars) vars1 cc.call_lhs
  in ov IdSet.empty
        
(** Smart constructors for commands *)

let mk_basic_cmd bcmd pos =
  let pp = mk_ppoint pos in
  Basic (bcmd, 
         { pp with 
           pp_modifies = modifies_basic_cmd bcmd;
           pp_accesses = accesses_basic_cmd bcmd;
         }
        )

let mk_assign_cmd lhs rhs pos = 
  let ac = { assign_lhs = lhs; assign_rhs = rhs } in
  mk_basic_cmd (Assign ac) pos

let mk_havoc_cmd args pos = 
  let hc = { havoc_args = args } in
  mk_basic_cmd (Havoc hc) pos

let mk_new_cmd lhs srt args pos = 
  let nc = { new_lhs = lhs; new_sort = srt; new_args = args } in
  mk_basic_cmd (New nc) pos

let mk_dispose_cmd t pos =
  let dc = { dispose_arg = t } in
  mk_basic_cmd (Dispose dc) pos

let mk_assume_cmd sf pos =
  mk_basic_cmd (Assume sf) pos

let mk_assert_cmd sf pos =
  mk_basic_cmd (Assert sf) pos

let mk_split_cmd sf pos =
  mk_basic_cmd (Split sf) pos

let mk_unfold_cmd name t pos =
  let pc =
    {
      pred_action = Unfold;
      pred_name = name;
      pred_args = t;

    }
  in
  mk_basic_cmd (Unfold pc) pos

let mk_fold_cmd name t pos =
  let pc =
    {
      pred_action = Fold;
      pred_name = name;
      pred_args = t;

    }
  in
  mk_basic_cmd (Fold pc) pos

let mk_return_cmd args pos = 
  let rc = { return_args = args } in
  mk_basic_cmd (Return rc) pos

let mk_call_cmd ?(prog=None) lhs name args pos =
  let cc =
    { call_lhs = lhs;
      call_name = name;
      call_args = args;
      call_modifies = IdSet.empty;
      call_accesses = IdSet.empty
    }
  in
  let accs = accesses_basic_cmd (Call cc) in
  let mods = modifies_basic_cmd (Call cc) in
  let pp = mk_ppoint pos in
  match prog with
  | None -> Basic (Call cc, { pp with pp_accesses = accs; pp_modifies = mods }) 
  | Some prog -> 
      let proc = find_proc prog name in
      let mods = IdSet.union (modifies_proc prog proc) mods in
      let accs = IdSet.union (accesses_proc prog proc) accs in
      let pp1 = 
        { pp with 
          pp_modifies = mods;
          pp_accesses = accs;
        }
      in
      Basic (Call cc, pp1)

let mk_seq_cmd cmds pos =
  let cmds1, mods, accs = 
    List.fold_right (function
      | Seq (cs, _) -> fun (cmds1, mods, accs) -> 
          List.fold_right (fun c (cmds1, mods, accs) ->
            c :: cmds1, 
            IdSet.union (modifies_cmd c) mods, 
            IdSet.union (accesses_cmd c) accs)
            cs (cmds1, mods, accs)
      | c -> fun (cmds1, mods, accs) -> 
          c :: cmds1, 
          IdSet.union (modifies_cmd c) mods, 
          IdSet.union (accesses_cmd c) accs)
      cmds ([], IdSet.empty, IdSet.empty)
  in
  let pp = mk_ppoint pos in
  let pp1 = 
    { pp with
      pp_modifies = mods;
      pp_accesses = accs;
    } 
  in
  match cmds1 with
  | [cmd] -> cmd
  | _ -> Seq (cmds1, pp1)

let mk_choice_cmd cmds pos =
  let cmds1, mods, accs = 
    List.fold_right (function
      | Choice (cs, _) -> fun (cmds1, mods, accs) -> 
          List.fold_right (fun c (cmds1, mods, accs) ->
            c :: cmds1, 
            IdSet.union (modifies_cmd c) mods, 
            IdSet.union (accesses_cmd c) accs)
            cs (cmds1, mods, accs)
      | c -> fun (cmds1, mods, accs) -> 
          c :: cmds1, 
          IdSet.union (modifies_cmd c) mods, 
          IdSet.union (accesses_cmd c) accs)
      cmds ([], IdSet.empty, IdSet.empty)
  in
  let pp = mk_ppoint pos in
  let pp1 = 
    { pp with
      pp_modifies = mods;
      pp_accesses = accs;
    } 
  in
  match cmds1 with
  | [cmd] -> cmd
  | _ -> Choice (cmds, pp1)

let mk_loop_cmd inv preb cond cond_pos postb pos =
  let loop = 
    { loop_inv = inv;
      loop_prebody = preb;
      loop_test = cond;
      loop_test_pos = cond_pos;
      loop_postbody = postb;
    } 
  in
  let pp = mk_ppoint pos in
  let mods = IdSet.union (modifies_cmd preb) (modifies_cmd postb) in
  let accs = 
    IdSet.union
      (IdSet.union (accesses_cmd preb) (accesses_cmd postb))
      (List.fold_left (accesses_spec_form_acc) (free_symbols cond) inv)
  in
  let pp1 = 
    { pp with
      pp_modifies = mods;
      pp_accesses = accs;
    } 
  in
  Loop (loop, pp1)

let mk_ite cond cond_pos then_cmd else_cmd then_msg else_msg pos =
  let mk_cond cmt =
    if cond_pos = dummy_position
    then cond
    else mk_error_msg (cond_pos, cmt) cond
  in
  let t_cond = 
    mk_spec_form 
      (FOL (mk_cond (ProgError.mk_trace_info then_msg)))
      "if_then" None cond_pos 
  in
  let e_cond = 
    mk_spec_form 
      (FOL (mk_not (mk_cond (ProgError.mk_trace_info else_msg))))
      "if_else" None cond_pos
  in
  let t_assume = mk_assume_cmd t_cond cond_pos in
  let e_assume = mk_assume_cmd e_cond cond_pos in
  let t_block = mk_seq_cmd [t_assume; then_cmd] (source_pos then_cmd) in
  let e_block = mk_seq_cmd [e_assume; else_cmd] (source_pos else_cmd) in
  mk_choice_cmd [t_block; e_block] pos

let rec map_terms_cmd fn =
  let map_terms_basic_cmd = function
    | Assign ac ->
        let ac1 =
          { ac with assign_rhs = List.map fn ac.assign_rhs }
        in
        Assign ac1
    | Return rc ->
        let rc1 =
          { return_args = List.map fn rc.return_args }
        in
        Return rc1
    | Call cc ->
        let cc1 =
          { cc with call_args = List.map fn cc.call_args }
        in
        Call cc1
    | New nc ->
        let nc1 =
          { nc with new_args = List.map fn nc.new_args }
        in
        New nc1
    | Dispose dc ->
        let dc1 = { dispose_arg = fn dc.dispose_arg } in
        Dispose dc1
    | Havoc hc -> Havoc hc
    | Assert sf ->
        Assert (map_terms_spec fn sf)
    | Assume sf ->
        Assume (map_terms_spec fn sf)
    | Split sf ->
        Split (map_terms_spec fn sf)
    | Unfold pc ->
        let pc1 = 
          { pc with pred_args = List.map fn pc.pred_args }
        in
        Unfold pc1
    | Fold pc -> 
        let pc2 = 
          { pc with pred_args = List.map fn pc.pred_args }
        in
        Fold pc2
  in
  function
  | Basic (bc, pp) -> mk_basic_cmd (map_terms_basic_cmd bc) pp.pp_pos
  | Seq (cs, pp) -> mk_seq_cmd (List.map (map_terms_cmd fn) cs) pp.pp_pos
  | Choice (cs, pp) -> mk_choice_cmd (List.map (map_terms_cmd fn) cs) pp.pp_pos
  | Loop (lc, pp) ->
      let loop_test = map_terms fn lc.loop_test in
      let loop_prebody = map_terms_cmd fn lc.loop_prebody in
      let loop_postbody = map_terms_cmd fn lc.loop_postbody in
      let loop_inv = List.map (map_terms_spec fn) lc.loop_inv in
      mk_loop_cmd loop_inv loop_prebody loop_test lc.loop_test_pos loop_postbody pp.pp_pos

 
let rec fold_basic_cmds f acc = function
  | Loop (lc, pp) ->
      let lpre, acc = fold_basic_cmds f acc lc.loop_prebody in
      let lpost, acc = fold_basic_cmds f acc lc.loop_postbody in
      mk_loop_cmd lc.loop_inv lpre lc.loop_test lc.loop_test_pos lpost pp.pp_pos, acc
  | Choice (cs, pp) ->
      let cs1, acc = 
        List.fold_right (fun c (cs1, acc) ->
          let c1, acc = fold_basic_cmds f acc c in
          c1 :: cs1, acc)
          cs ([], acc)
      in
      mk_choice_cmd cs1 pp.pp_pos, acc
  | Seq (cs, pp) ->
      let cs1, acc =
        List.fold_right (fun c (cs1, acc) ->
          let c1, acc = fold_basic_cmds f acc c in
          c1 :: cs1, acc)
          cs ([], acc)
      in 
      mk_seq_cmd cs1 pp.pp_pos, acc
  | Basic (bc, pp) ->
      f (bc, pp) acc

let map_basic_cmds f c =
  let c1, _ = fold_basic_cmds (fun c _ -> f c, ()) () c in
  c1

    
(** Auxiliary function for predicates *)

let subst_id_var_decl map vd =
  let try_subst id = try IdMap.find id map with Not_found -> id in
    { vd with var_name = try_subst vd.var_name }

let subst_id_pred map pred =
  let try_subst id = try IdMap.find id map with Not_found -> id in
  let name = try_subst (name_of_pred pred) in
  let formals = List.map try_subst (formals_of_pred pred) in
  let returns = List.map try_subst (returns_of_pred pred) in
  let locals =
    IdMap.fold
      (fun k v acc -> IdMap.add (try_subst k) (subst_id_var_decl map v) acc)
      (locals_of_pred pred)
      IdMap.empty
  in
  let body = Util.Opt.map (subst_id_spec map) pred.pred_body in
  let accesses =
    IdSet.fold
      (fun id acc -> IdSet.add (try_subst id) acc)
      pred.pred_accesses
      IdSet.empty
  in
  let contract =
    { pred.pred_contract with
      contr_name = name;
      contr_formals = formals;
      contr_returns = returns;
      contr_locals = locals;
    }
  in
  {pred with
   pred_contract = contract;
   pred_body = body;
   pred_accesses = accesses }

let result_sort_of_pred pred =
  match returns_of_pred pred with
  | [] -> Bool
  | id :: _ ->
      (IdMap.find id (locals_of_pred pred)).var_sort
    

(** Pretty printing *)

open Format

let pr_term ppf t =
  Grass.pr_term ppf (old_to_fun_term t)

let pr_term_list = Util.pr_list_comma pr_term

let pr_sl_form ppf f = Sl.pr_form ppf (old_to_fun_sl_form f)
    
let pr_form ppf f = Grass.pr_form ppf (old_to_fun_form f)

let pr_comment ppf c =
  match c with
  | "" -> ()
  | _ -> fprintf ppf "/* %s */@\n" c
    
let pr_spec_form ppf sf =
  match sf.spec_form with
  | SL f -> pr_sl_form ppf f
  | FOL f -> pr_form ppf f

let pr_sspec_form ppf sf =
  match sf with
  | SL f -> pr_sl_form ppf f
  | FOL f -> pr_form ppf f

let pr_basic_cmd ppf = function
  | Assign ac -> 
      fprintf ppf "@[<2>%a@ :=@ %a@]" 
        pr_ident_list ac.assign_lhs 
        pr_term_list ac.assign_rhs
  | Havoc hc -> 
      fprintf ppf "@[<2>havoc@ %a@]" pr_ident_list hc.havoc_args
  | New nc ->
      (match nc.new_args with
      | [] ->
          fprintf ppf "@[<2>%a@ :=@ new@ %a@]" 
            pr_ident nc.new_lhs 
            pr_sort nc.new_sort
      | args ->
          fprintf ppf "@[<2>%a@ :=@ new@ %a(%a)@]" 
            pr_ident nc.new_lhs 
            pr_sort nc.new_sort
            pr_term_list args)
  | Dispose dc -> 
      fprintf ppf "@[<2>free@ %a@]" pr_term dc.dispose_arg
  | Assume sf ->
      fprintf ppf "%a@[<2>%sassume@ %a@]"
        pr_comment sf.spec_name
        (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
        pr_spec_form sf
  | Assert sf ->
      fprintf ppf "%a@[<2>%sassert@ %a@]" 
        pr_comment sf.spec_name
        (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
        pr_spec_form sf
  | Split sf ->
      fprintf ppf "%a@[<2>split@ %a@]" 
        pr_comment sf.spec_name
        pr_spec_form sf
  | Unfold pc->
      fprintf ppf "@[unfold@ %a(@[%a@])@]" 
        pr_ident pc.pred_name 
        pr_term_list pc.pred_args 
  | Fold pc->
      fprintf ppf "@[fold@ %a(@[%a@])@]" 
        pr_ident pc.pred_name 
        pr_term_list pc.pred_args 
  | Return rc -> 
      fprintf ppf "@[<2>return@ %a@]" pr_term_list rc.return_args
  | Call cc -> 
      match cc.call_lhs with
      | [] ->
          fprintf ppf "@[call@ %a(@[%a@])@]" 
            pr_ident cc.call_name 
            pr_term_list cc.call_args
      | _ ->
          fprintf ppf "@[<2>%a@ :=@ @[%a(@[%a@])@]@]" 
            pr_ident_list cc.call_lhs 
            pr_ident cc.call_name 
            pr_term_list cc.call_args

let rec pr_invs ppf = function
  | [] -> ()
  | [sf] -> 
      fprintf ppf "%sinvariant@ @[<2>%a@]" 
        (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
        pr_spec_form sf
  | sf :: sfs -> 
      fprintf ppf "@<0>%s%s@[<2>@ %a@]@\n%a"
        (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
        "invariant" 
        pr_spec_form sf pr_invs sfs 

let rec pr_cmd ppf = function
  | Loop (lc, _) ->
      fprintf ppf "%awhile@ (%a)@ @,@[<2>@ @ %a@]@\n%a" 
        pr_cmd lc.loop_prebody 
        pr_form lc.loop_test 
        pr_invs lc.loop_inv 
        pr_cmd lc.loop_postbody
  | Choice (cs, _) ->
      fprintf ppf "@<-3>%s@ %a" "choose" pr_choice cs
  | Seq ([], _) -> ()
  | Seq (cs, _) ->
      fprintf ppf "{@[<1>@\n%a@]@\n}" pr_seq cs
  | Basic (bc, _) ->
      fprintf ppf "%a;" pr_basic_cmd bc

and pr_choice ppf = function
  | [] -> ()
  | [c] -> pr_cmd ppf c
  | c :: cs -> fprintf ppf "%a@ @<-3>%s@ %a" pr_cmd c "or" pr_choice cs

and pr_seq ppf = function
  | [] -> ()
  | [c] -> pr_cmd ppf c
  | c :: cs -> fprintf ppf "%a@\n%a" pr_cmd c pr_seq cs

let pr_spec_kind ppf = function
  | Free -> fprintf ppf "@<0>%s" "free "
  | Checked -> ()

let rec pr_precond ppf = function
  | [] -> ()
  | sf :: sfs -> 
      fprintf ppf "@\n%a@[<2>%a%srequires@ %a@]%a"
        pr_comment sf.spec_name
        pr_spec_kind sf.spec_kind
        (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
        pr_spec_form sf 
        pr_precond sfs 

let rec pr_postcond ppf = function
  | [] -> ()
  | sf :: sfs -> 
      fprintf ppf "@\n%a@[<2>%a%sensures@ %a@]%a"
        pr_comment sf.spec_name
        pr_spec_kind sf.spec_kind
        (fold_spec_form (fun _ -> "pure ") (fun _ -> "") sf)
        pr_spec_form sf 
        pr_postcond sfs 

let pr_ghost ppf = function
  | true -> fprintf ppf "ghost "
  | false -> ()

let pr_implicit ppf = function
  | true -> fprintf ppf "implicit "
  | false -> ()

let pr_id_srt implicit ghost ppf (id, srt) =
  fprintf ppf "%a%a%a: %a" 
    pr_implicit implicit
    pr_ghost ghost
    pr_ident id 
    pr_sort srt

let rec pr_id_srt_list ppf = function
  | [] -> ()
  | [implicit, ghost, is] -> pr_id_srt implicit ghost ppf is
  | (implicit, ghost, is) :: iss -> 
      fprintf ppf "%a,@ @,%a" 
        (pr_id_srt implicit ghost) is 
        pr_id_srt_list iss

let pr_var_decl ppf (id, decl) =
  fprintf ppf "@[<2>var@ %a@];@\n" 
    (pr_id_srt decl.var_is_implicit decl.var_is_ghost) (id, decl.var_sort)

let rec pr_var_decls ppf = function
  | [] -> ()
  | decl :: decls -> fprintf ppf "%a%a" pr_var_decl decl pr_var_decls decls

let pr_body locals ppf = function
  | None -> ()
  | Some c ->
      let cs = match c with
      | Seq (cs, _) -> cs
      | _ -> [c]
      in
      fprintf ppf "{@[<1>@\n%a%a@]@\n}"
        pr_var_decls locals
        pr_seq cs 

let pr_contract ppf contr =
  fprintf ppf "%a%a"
    pr_precond contr.contr_precond
    pr_postcond contr.contr_postcond

let pr_proc ppf proc =
  let add_srts = List.map (fun id -> 
    let decl = find_local_var proc id in
    (decl.var_is_implicit, decl.var_is_ghost, (id, decl.var_sort)))
  in
  let locals = IdMap.fold (fun id decl locals ->
    if List.mem id (returns_of_proc proc @ formals_of_proc proc)
    then locals
    else (id, decl) :: locals) (locals_of_proc proc) []
  in
  let intro =
    if proc.proc_is_lemma then
      if proc.proc_is_auto then "auto lemma" else "lemma"
    else "procedure"
  in
  let pr_returns ppf returns =
    if returns = [] then ()
    else fprintf ppf "@\nreturns (@[<0>%a@])" pr_id_srt_list (add_srts returns)
  in
  fprintf ppf "@\n@[<2>%s %a(@[<0>%a@])%a%a@]@\n%a"
    intro
    pr_ident (name_of_proc proc)
    pr_id_srt_list (add_srts (formals_of_proc proc))
    pr_returns (returns_of_proc proc)
    pr_contract proc.proc_contract
    (pr_body locals) proc.proc_body

let rec pr_procs ppf = function
  | [] -> ()
  | proc :: procs ->
      fprintf ppf "%a@\n%a" pr_proc proc pr_procs procs

let pr_pred ppf pred =
  let add_srts = List.map (fun id -> 
    let decl = IdMap.find id (locals_of_pred pred) in
    (decl.var_is_implicit, decl.var_is_ghost, (id, decl.var_sort)))
  in
  let pr_header ppf pred =
  match returns_of_pred pred with
  | [] ->
      fprintf ppf "@\n@[<2>%spredicate %a(@[<0>%a@])%a@]@ "
        (if pred.pred_contract.contr_is_pure then "pure " else "")
        pr_ident (name_of_pred pred)
        pr_id_srt_list (add_srts (formals_of_pred pred))
        pr_contract pred.pred_contract
  | _ ->
      fprintf ppf "@\n@[<2>%sfunction %a(@[<0>%a@])@\nreturns (@[<0>%a@])%a@]@\n"
        (if pred.pred_contract.contr_is_pure then "pure " else "")
        pr_ident (name_of_pred pred)
        pr_id_srt_list (add_srts (formals_of_pred pred))
        pr_id_srt_list (add_srts (returns_of_pred pred))
        pr_contract pred.pred_contract
  in
  let pr_body ppf pred =
    match pred.pred_body with
    | Some sf ->
        fprintf ppf "{@[<1>@\n%a@]@\n}" pr_spec_form sf
    | None -> fprintf ppf "@\n@\n"
  in
  fprintf ppf "%a%a" pr_header pred pr_body pred
    
let rec pr_preds ppf = function
  | [] -> ()
  | pred :: preds ->
      fprintf ppf "%a@\n%a" pr_pred pred pr_preds preds

let pr_axiom ppf sf =
  fprintf ppf "%a@[<2>axiom@ %a@];@\n"
    pr_comment sf.spec_name
    pr_spec_form sf 
    

let rec pr_axioms ppf = function
  | [] -> ()
  | axiom :: axioms ->
      fprintf ppf "%a@\n%a" pr_axiom axiom pr_axioms axioms

let pr_prog ppf prog =
  fprintf ppf "%a@\n%a%a%a" 
    pr_var_decls (IdMap.bindings prog.prog_vars)
    pr_axioms prog.prog_axioms
    pr_preds (List.map snd (IdMap.bindings prog.prog_preds))
    pr_procs (List.map snd (IdMap.bindings prog.prog_procs))

let print_prog out_ch prog = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_prog prog

let print_cmd out_ch cmd = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_cmd cmd

let dump_if n prog = 
  if !Config.dump_ghp == n 
  then (print_prog stdout prog; prog)
  else prog
