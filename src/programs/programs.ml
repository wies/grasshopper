open Form
open FormUtil
open Axioms
open Entails

let alloc_id = (mk_ident "Alloc")

let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

(** Source position *)

type source_position = {
    sp_file : string;
    sp_start_line : int;
    sp_start_col : int;
    sp_end_line : int;
    sp_end_col : int;
  }

(** Expressions *)

type expr = 
  | FormExpr of form
  | TermExpr of term

(** Specification formulas *)

type spec_form =
  | SL of Sl.form
  | FOL of form

(** Commands *)

(** Assignment, x_1,...,x_n := e_1,...,e_n *)
type assign_command = {
    assign_lhs : ident list; (** name of the assigned variables *)
    assign_rhs : expr list; (** assigned values *)
  }

(** Allocation, x := new T *)
type new_command = {
    new_lhs : ident;
    new_sort : sort;
    new_type : ident; (** original type *)
  }

(** Deallocation, free x *)
type dispose_command = {
    dispose_loc : term;
  }
     
(** Assume or assert of pure formula *)
type form_command = {
    fc_form : spec_form;
    fc_msg : string option;
  } 

(** Procedure call, x_1,..., x_n := p(e_1,...,e_m) *)
type call_command = {
    call_res : ident list; (** x_1,...,x_n *)
    call_name : ident; (** p *)
    call_args : expr list; (** e_1,...,e_m *)
  } 

(** Return from procedure *)
and return_command = 
    {
     return_args : expr list;
   }

(** Basic commands *)
type basic_command =
  | Assign of assign_command
  | New of new_command
  | Dispose of dispose_command
  | Assume of form_command
  | Assert of form_command
  | Call of call_command
  | Return of return_command

(** Program point *)
type program_point = {
    pp_pos : source_position;
    pp_modifies : IdSet.t;
  }

(** Loop *)
type loop_command = {
    loop_inv : spec_form list;
    loop_prebody : command;
    loop_test : form;
    loop_postbody : command;
  }

(** Compound commands *)
and command =
  | Loop of loop_command * program_point
  | Choice of command list * program_point
  | Seq of command list * program_point
  | Basic of basic_command * program_point

(** Variable declaration *)
type var_decl = {
    var_name : ident; (** variable name *)
    var_orig_name : string; (** original name *)
    var_sort : sort; (** variable type *)
    var_type : ident option; (** original type *)
    var_is_ghost : bool; (** whether the variable is ghost *)
    var_is_aux : bool; (** whether the variable is an auxiliary variable *)
    var_pos : source_position; (** position of declaration *)
  }

(** Procedure declaration *)
type proc_decl = {
    proc_name : ident; (** procedure name *)
    proc_formals : ident list;  (** formal parameter list *)
    proc_returns : ident list; (** return parameter list *)
    proc_locals : var_decl IdMap.t; (** all local variables *)
    proc_precond : spec_form list; (** precondition *)
    proc_postcond : spec_form list; (** postcondition *)
    proc_body : command option; (* procedure body *)
    proc_pos : source_position; (** position of declaration *)
  }

(** Predicate declaration *)
type pred_decl = {
    pred_name : ident; (** predicate name *)
    pred_formals : ident list; (** formal parameter list *)
    pred_locals : var_decl IdMap.t; (** local variables *)
    pred_body : Sl.form; (** predicate body *)
    pred_pos : source_position; (** position of declaration *)
  } 

(** Program *)
type program = {
    prog_globals : var_decl IdMap.t; (** global variables *)
    prog_preds : pred_decl IdMap.t; (** predicates *)
    prog_procs : proc_decl IdMap.t; (** procedures *)
  } 

(** Auxiliary functions for programs *)

let dummy_position = 
  { sp_file = "";
    sp_start_line = 0;
    sp_start_col = 0;
    sp_end_line = 0;
    sp_end_col = 0 
  }

let empty_prog = 
  { prog_globals = IdMap.empty;
    prog_preds = IdMap.empty;
    prog_procs = IdMap.empty 
  }
    
let dummy_proc name = 
  { proc_name = name;
    proc_formals = [];
    proc_returns = [];
    proc_locals = IdMap.empty;
    proc_precond = [];
    proc_postcond = [];
    proc_body = None;
    proc_pos = dummy_position;
  }

let mk_ppoint pos =
  { pp_pos = pos; pp_modifies = IdSet.empty }

let mk_basic_cmd bcmd pos =
  Basic (bcmd, mk_ppoint pos)

let mk_seq_cmd cmds pos =
  match cmds with
  | [cmd] -> cmd
  | _ -> Seq (cmds, mk_ppoint pos)

let mk_choice_cmd cmds pos =
  Choice (cmds, mk_ppoint pos)

let mk_loop_cmd loop pos =
  Loop (loop, mk_ppoint pos)


let declare_global prog global =
  { prog with prog_globals = IdMap.add global.var_name global prog.prog_globals }

let declare_pred prog pred =
  {prog with prog_preds = IdMap.add pred.pred_name pred prog.prog_preds}

let declare_proc prog proc =
  {prog with prog_procs = IdMap.add proc.proc_name proc prog.prog_procs}

let procs prog = IdMap.fold (fun _ proc procs -> proc :: procs) prog.prog_procs []

let find_proc prog name = IdMap.find name prog.prog_procs

let find_pred prog name = IdMap.find name prog.prog_preds

let find_global prog name = IdMap.find name prog.prog_globals

(** Auxiliary functions for commands *)

let prog_point = function
  | Loop (_, pp) | Choice (_, pp) | Seq (_, pp) | Basic (_, pp) -> pp

let rec modifies c = (prog_point c).pp_modifies
and basic_modifies prog = function
  | Assign ac -> id_set_of_list ac.assign_lhs
  | New nc -> IdSet.add alloc_id (IdSet.singleton nc.new_lhs)
  | Dispose _ -> IdSet.singleton alloc_id
  | Assume _
  | Assert _
  | Return _ -> IdSet.empty
  | Call cc -> proc_modifies (find_proc prog cc.call_name)
and proc_modifies proc = 
  match proc.proc_body with
  | Some cmd -> modifies cmd
  | None -> IdSet.empty

