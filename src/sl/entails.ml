open Form
open FormUtil
open Axioms


let alloc_id = (mk_ident "Alloc")

let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

(* static declaration of the heaps *)
let pre_heap_id = "A"
let post_heap_id = "B"
let pre_heap () = fresh_ident pre_heap_id
let post_heap () = fresh_ident post_heap_id

let same_heap_axioms subst preh posth =
  (* heap matches: A(x) <=> B(x) *)
  let first_alloc = alloc_id in
  let last_alloc =
    if IdMap.mem alloc_id subst
    then IdMap.find alloc_id subst
    else alloc_id
  in
    (* "same_heap_content_pre"  *)
    [ mk_eq (SlUtil.mk_loc_set preh) (SlUtil.mk_loc_set first_alloc);
    (* "same_heap_content_post" *)
      mk_eq (SlUtil.mk_loc_set posth) (SlUtil.mk_loc_set last_alloc) ]

let mk_entailment_query1 pre_sl pathf post_sl subst =
  let preh = pre_heap () in
  let posth = post_heap () in
  let pre = ToGrass.to_grass Symbols.pred_to_form preh pre_sl in
  let post = subst_id subst (ToGrass.to_grass_negated Symbols.pred_to_form posth post_sl) in
  (* query *)
  let query = smk_and ( (*SlUtil.make_axioms*) (mk_and [pre; post; pathf]) ::
                        (same_heap_axioms subst preh posth) )
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "query: ";
      print_form stdout query
    end
  in
    query

let mk_entailment_query pre_sl post_sl =
  mk_entailment_query1 pre_sl mk_true post_sl IdMap.empty
  

let check_entailment pre_sl post_sl =
  let mk_query () = mk_entailment_query pre_sl post_sl in
  let query = Util.measure_call "translation" mk_query () in
    Prover.check_sat query
