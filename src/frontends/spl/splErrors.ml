(** {5 Utility functions for generating error messages during the analysis of SPL programs } *)

open Grass
open SplSyntax
  
let unknown_ident_error id pos =
  ProgError.error pos ("Unknown identifier " ^ GrassUtil.name id ^ ".")

let not_a_struct_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct.")

let not_a_proc_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a procedure or predicate.")

let not_a_pred_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a procedure or predicate.")

let not_a_field_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct field.")

let redeclaration_error id pos =
  ProgError.error pos ("Identifier " ^ GrassUtil.name id ^ " has already been declared in this scope.")
    
let assignment_mismatch_error pos =
  ProgError.error pos 
    "Mismatch in number of expressions on left and right side of assignment"                

let abstract_initializer_error pos id =
  ProgError.error pos
    ("Unable to infer unique type from initializer of variable " ^ GrassUtil.name id ^ ". Type annotation required.")
    
let null_access_error pos =
  ProgError.error pos "Tried to dereference of access null."

let footprint_declaration_error id pos =
  ProgError.error pos ("Footprint parameter " ^ string_of_ident id ^ " has an unexpected type. Expected type " ^
                       string_of_type (SetType (StructType ("T", 0))) ^ " for some struct type T.")

let invalid_nested_proc_call_error id pos =
  ProgError.error pos 
    ("Procedure " ^ GrassUtil.name id ^ " has more than one return value.")

let return_in_loop_error pos =
  ProgError.error pos "A procedure cannot return from within a loop."
