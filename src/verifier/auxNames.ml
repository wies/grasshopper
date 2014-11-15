open Grass
open GrassUtil
open Prog

(** Auxiliary variables for desugaring SL specifications *)
let footprint_id = fresh_ident "FP"
let footprint_set = mk_loc_set footprint_id

let footprint_caller_id = fresh_ident "FP_Caller"
let footprint_caller_set = mk_loc_set footprint_caller_id

let final_footprint_caller_id = fresh_ident "FP_Caller_final"
let final_footprint_caller_set = mk_loc_set final_footprint_caller_id
