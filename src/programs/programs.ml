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
    assign_rhs : term list; (** assigned values *)
  }

(** Havoc, havoc x_1, ..., x_n *)
type havoc_command = {
    havoc_args : ident list;
  } 

(** Allocation, x := new T *)
type new_command = {
    new_lhs : ident;
    new_sort : sort;
  }

(** Deallocation, free x *)
type dispose_command = {
    dispose_loc : term;
  }
     
(** Assume or assert of pure formula *)
type spec = {
    spec_form : spec_form;
    spec_free : bool;
    spec_msg : string option;
    spec_pos : source_position;
  } 

(** Procedure call, x_1,..., x_n := p(e_1,...,e_m) *)
type call_command = {
    call_lhs : ident list; (** x_1,...,x_n *)
    call_name : ident; (** p *)
    call_args : term list; (** e_1,...,e_m *)
  } 

(** Return from procedure *)
and return_command = 
    {
     return_args : expr list;
   }

(** Basic commands *)
type basic_command =
  | Assign of assign_command
  | Havoc of havoc_command
  | New of new_command
  | Dispose of dispose_command
  | Assume of spec
  | Assert of spec
  | Call of call_command
  | Return of return_command

(** Program point *)
type program_point = {
    pp_pos : source_position;
    pp_modifies : IdSet.t;
  }

(** Loop *)
type loop_command = {
    loop_inv : spec list;
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
    proc_precond : spec list; (** precondition *)
    proc_postcond : spec list; (** postcondition *)
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
    prog_axioms : spec list; (** background axioms *)
    prog_vars : var_decl IdMap.t; (** global variables *)
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
  { prog_axioms = [];
    prog_vars = IdMap.empty;
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

let mk_spec_form f free msg pos =
  { spec_form = f;
    spec_free = free;
    spec_msg = msg;
    spec_pos = pos;
  }

let mk_basic_cmd bcmd pos =
  Basic (bcmd, mk_ppoint pos)

let mk_pp pos = { pp_pos = pos; pp_modifies = IdSet.empty }

let mk_assign_cmd lhs rhs pos = 
  let ac = { assign_lhs = lhs; assign_rhs = rhs } in
  mk_basic_cmd (Assign ac) pos

let mk_havoc_cmd args pos = 
  let hc = { havoc_args = args } in
  mk_basic_cmd (Havoc hc) pos

let mk_new_cmd lhs srt pos = 
  let nc = { new_lhs = lhs; new_sort = srt } in
  mk_basic_cmd (New nc) pos

let mk_dispose_cmd t pos =
  let dc = { dispose_loc = t } in
  mk_basic_cmd (Dispose dc) pos

let mk_assume_cmd sf pos =
  mk_basic_cmd (Assume sf) pos

let mk_assert_cmd sf pos =
  mk_basic_cmd (Assert sf) pos

let mk_call_cmd lhs name args pos =
  let cc = {call_lhs = lhs; call_name = name; call_args = args} in
  mk_basic_cmd (Call cc) pos

let mk_seq_cmd cmds pos =
  match cmds with
  | [cmd] -> cmd
  | _ -> Seq (cmds, mk_ppoint pos)

let mk_choice_cmd cmds pos =
  Choice (cmds, mk_ppoint pos)

let mk_loop_cmd inv preb cond postb pos =
  let loop = 
    { loop_inv = inv;
      loop_prebody = preb;
      loop_test = cond;
      loop_postbody = postb;
    } 
  in
  Loop (loop, mk_ppoint pos)


let declare_global prog var =
  { prog with prog_vars = IdMap.add var.var_name var prog.prog_vars }

let declare_pred prog pred =
  {prog with prog_preds = IdMap.add pred.pred_name pred prog.prog_preds}

let declare_proc prog proc =
  {prog with prog_procs = IdMap.add proc.proc_name proc prog.prog_procs}

let procs prog = IdMap.fold (fun _ proc procs -> proc :: procs) prog.prog_procs []

let find_proc prog name = IdMap.find name prog.prog_procs

let find_pred prog name = IdMap.find name prog.prog_preds

let find_global prog name = IdMap.find name prog.prog_vars

(** Auxiliary functions for commands *)

let prog_point = function
  | Loop (_, pp) | Choice (_, pp) | Seq (_, pp) | Basic (_, pp) -> pp

let rec modifies c = (prog_point c).pp_modifies
and basic_modifies prog = function
  | Assign ac -> id_set_of_list ac.assign_lhs
  | Havoc hc -> id_set_of_list hc.havoc_args
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

