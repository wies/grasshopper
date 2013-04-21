open Form
open FormUtil
open Axioms
open Entails

let alloc_id = (mk_ident "Alloc")

let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

(** Commands *)

(** Assignment, x_1,...,x_n := e_1,...,e_n *)
type assign_command = {
    assign_lhs : ident list; (** name of the assigned variables *)
    assign_rhs : term list; (** assigned values *)
  }

(** Allocation, x := new T *)
type new_command = {
    new_lhs : ident;
    new_sort : sort;
    new_type : ident option; (** original type *)
  }

(** Deallocation, free x *)
type dispose_command = {
    dispose_var : ident;
  }
     
(** Assume or assert of SL formula *)
type sl_form_command = {
    slc_form : Sl.form;
    slc_msg : string option;
  } 

(** Assume or assert of pure formula *)
type form_command = {
    fc_form : form;
    fc_msg : string option;
  } 

(** Procedure call, x_1,..., x_n := p(e_1,...,e_m) *)
type call_command = {
    call_res : ident list; (** x_1,...,x_n *)
    call_name : ident; (** p *)
    call_args : term list; (** e_1,...,e_m *)
  } 

(** Return from procedure *)
and return_command = {
    return_args : term list;
}

(** Basic commands *)
type basic_command =
  | Assign of assign_command
  | New of new_command
  | Dispose of dispose_command
  | AssumeSL of sl_form_command
  | Assume of form_command
  | AssertSL of sl_form_command
  | Assert of form_command
  | Call of call_command
  | Return of return_command


(** Identification of the current program point. *)
type program_point = {
    pp_file : string;
    pp_proc : ident;
    pp_line : int;
    pp_column : int;
    pp_modifies : IdSet.t;
  }

(** Loop *)
type loop_command = {
    loop_ppoint : program_point;
    loop_inv : Sl.form;
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

(** Concrete or ghost variable. *)
type var_decl = {
    var_name : ident; (** variable name *)
    var_sort : sort; (** variable type *)
    var_type : ident option; (** original type *)
    var_is_ghost : bool; (** whether the variable is ghost *)
  }

(** Procedure declaration *)
type proc_decl = {
    proc_name : ident; (** procedure name *)
    proc_formals : ident list;  (** formal parameter list *)
    proc_returns : ident list; (** return parameter list *)
    proc_locals : var_decl IdMap.t; (** all local variables *)
    proc_precond : Sl.form; (** precondition *)
    proc_postcond : Sl.form; (** postcondition *)
    proc_body : command; (* procedure body *)
  }

(** Struct declaration *)
type struct_decl = {
    struct_name : ident; (** struct name *)
    struct_fields : var_decl list; (* fields *)
  } 

(** Program *)
type program = {
    prog_globals : var_decl IdMap.t; (** global variables *)
    prog_structs : struct_decl IdMap.t; (** structs *)
    prog_procs : proc_decl IdMap.t; (** procedures *)
  } 


let procs prog = IdMap.fold (fun _ proc procs -> proc :: procs) prog.prog_procs []

let find_proc prog name = IdMap.find name prog.prog_procs

let prog_point = function
  | Loop (_, pp) | Choice (_, pp) | Seq (_, pp) | Basic (_, pp) -> pp

let rec modifies c = (prog_point c).pp_modifies
and basic_modifies prog = function
  | Assign ac -> id_set_of_list ac.assign_lhs
  | New nc -> IdSet.add alloc_id (IdSet.singleton nc.new_lhs)
  | Dispose _ -> IdSet.singleton alloc_id
  | AssumeSL _ 
  | Assume _
  | AssertSL _
  | Assert _
  | Return _ -> IdSet.empty
  | Call cc -> proc_modifies (find_proc prog cc.call_name)
and proc_modifies proc = modifies proc.proc_body

