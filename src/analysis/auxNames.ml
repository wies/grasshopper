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
  let mk_output id =
    let args =
      List.map snd (
        List.filter
          (fun ((i,_), _) -> List.for_all (fun (i2, _) -> i <> i2) def.Symbols.outputs)
          paired)
    in
    let ((_, srt), t) = List.find (fun ((i,_), _) -> i = id) paired in
      mk_eq t (mk_free_fun ~srt:srt (Symbols.pred_naming p id) args)
  in
  let outputs = List.map (fun (id, _) -> mk_output id) def.Symbols.outputs in
    structure, outputs


