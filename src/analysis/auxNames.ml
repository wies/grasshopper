open Form
open FormUtil
open Prog

(** Auxiliary variables for desugaring SL specifications *)
let footprint_id = fresh_ident "FP"
let footprint_set = mk_loc_set footprint_id

let footprint_caller_id = fresh_ident "FP_Caller"
let footprint_caller_set = mk_loc_set footprint_caller_id

let final_footprint_caller_id = fresh_ident "FP_Caller_final"
let final_footprint_caller_set = mk_loc_set final_footprint_caller_id

let pred_to_form p args dom =
  let def = Symbols.get_symbol p in
  let structure = mk_pred (Symbols.pred_struct p) (dom :: args) in
  let paired = List.combine def.Symbols.parameters (dom :: args) in
  let in_args = 
    let i =
      List.filter
        (fun ((i,_), _) -> List.for_all (fun (i2, _) -> i <> i2) def.Symbols.outputs)
        paired
    in
      List.map snd i
  in
  let mk_output id =
    let ((_, srt), t) = List.find (fun ((i,_), _) -> i = id) paired in
      mk_eq t (mk_free_fun srt (Symbols.pred_naming p id) in_args)
  in
  let dom_out = List.hd def.Symbols.outputs in
  let other_out = List.tl def.Symbols.outputs in
    mk_and (structure :: (List.map (fun (id, _) -> mk_output id) other_out)), [mk_output (fst dom_out)]


