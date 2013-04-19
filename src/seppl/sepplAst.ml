open Form
open FormUtil
open Axioms
open Entails

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

(** Atomic commands *)
type atomic_command =
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
  | Loop of loop_command * program_point option
  | Choice of command list * program_point option
  | Seq of command_list * program_point option
  | Atom of atomic_command * program point option

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
    proc_formals : var_decl list;  (** formal parameter list *)
    proc_returns : var_decl list; (** return parameter list *)
    proc_locals : var_decl list; (** all local variables *)
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
    prog_globals : var_decl list; (** global variables *)
    prog_structs : struct_decl list; (** structs *)
    prog_procs : proc_decl list; (** procedures *)
  } 

