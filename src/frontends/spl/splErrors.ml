(** {5 Utility functions for generating error messages during the analysis of SPL programs } *)

open Grass
open SplSyntax

let arguments_to_string d =
  if d = 1 then "one argument" else Printf.sprintf "%d arguments" d
  
let unknown_ident_error id pos =
  ProgError.error pos ("Unknown identifier " ^ string_of_ident id ^ ".")

let not_a_type_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a type.")

let not_a_struct_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct type.")

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

let illegal_side_effect_error pos source =
  ProgError.error pos ("Operations that may have side effects are not allowed in " ^ source)

    
let assignment_mismatch_error pos =
  ProgError.error pos 
    "Mismatch in number of expressions on left and right side of assignment"                

let assignment_multiple_error pos =
  ProgError.error pos (Printf.sprintf "Simultaneous assignment of the same variable is not allowed.")

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

let alloc_arg_mismatch_error pos expected =
  ProgError.error pos (Printf.sprintf "Constructor expects %s." (arguments_to_string expected))

let alloc_type_error pos ty =
  ProgError.type_error pos
    ("Expected an array or struct type but found " ^ string_of_type ty)
    
let pred_arg_mismatch_error pos id expected =
  ProgError.error pos (Printf.sprintf "Predicate %s expects %s." (GrassUtil.name id) (arguments_to_string expected))

let fun_arg_mismatch_error pos id expected =
  ProgError.error pos (Printf.sprintf "Function %s expects %s." (GrassUtil.name id) (arguments_to_string expected))

let proc_arg_mismatch_error pos id expected =
  ProgError.error pos 
    (Printf.sprintf "Procedure %s expects %s." 
       (GrassUtil.name id) (arguments_to_string @@ List.length expected))

let constr_arg_mismatch_error pos id expected =
  ProgError.error pos 
    (Printf.sprintf "Constructor %s expects %s." 
       (GrassUtil.name id) (arguments_to_string @@ List.length expected))

let destr_arg_mismatch_error pos id expected =
  ProgError.error pos 
    (Printf.sprintf "Expected destructor but found constructor %s." 
       (GrassUtil.name id))

    
let type_error pos exp_ty fnd_ty =
  let ty_str ty = "expression of type " ^ string_of_type ty in
  ProgError.type_error pos
    ("Expected an " ^ ty_str exp_ty ^ " but found an " ^ ty_str fnd_ty)
