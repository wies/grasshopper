open Form
open FormUtil
open Prog

(** Auxiliary variables for desugaring SL specifications *)
let alloc_id = fresh_ident "Alloc"
let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

let init_alloc_id = fresh_ident "Alloc_init"
let init_alloc_set = mk_free_const ~srt:(Set Loc) init_alloc_id

let final_alloc_id = fresh_ident "Alloc_final"
let final_alloc_set = mk_free_const ~srt:(Set Loc) final_alloc_id

let final_alloc_callee_id = fresh_ident "AllocCallee_final"
let final_alloc_callee_set = mk_free_const ~srt:(Set Loc) final_alloc_callee_id

let init_alloc_callee_id = fresh_ident "AllocCallee_init"
let init_alloc_callee_set = mk_free_const ~srt:(Set Loc) init_alloc_callee_id

let frame_id = mk_ident "AllocCaller"
let frame_set = mk_free_const ~srt:(Set Loc) frame_id

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
