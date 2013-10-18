open Form
open FormUtil
open Prog

(** Auxiliary variables for desugaring SL specifications *)
let alloc_id = fresh_ident "Alloc"
let alloc_set = mk_loc_set alloc_id

let footprint_id = fresh_ident "FP"
let footprint_set = mk_loc_set footprint_id

let footprint_caller_id = fresh_ident "FP_Caller"
let footprint_caller_set = mk_loc_set footprint_caller_id

let final_footprint_caller_id = fresh_ident "FP_Caller_final"
let final_footprint_caller_set = mk_loc_set final_footprint_caller_id

let pred_struct (name, num) = (name ^ "_struct", num)
let pred_domain (name, num) = (name ^ "_domain", num)

let mk_set_decl id pos =
  { var_name = id;
    var_orig_name = name id;
    var_sort = Set Loc;
    var_is_ghost = true;
    var_is_implicit = false;
    var_is_aux = true;
    var_pos = pos;
  }
  
let pred_to_form p args dom =
  mk_pred (pred_struct p) (args @ [dom]),
  mk_eq dom (mk_free_fun ~srt:(Set Loc) (pred_domain p) args)
