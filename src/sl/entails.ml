open Form
open FormUtil
open Axioms
open Stmnt

(* static declaration of the heaps *)
let pre_heap_id = "A"
let post_heap_id = "B"
let pre_heap = fresh_ident pre_heap_id
let post_heap = fresh_ident post_heap_id

let same_heap_axioms subst =
  (* heap matches: A(x) <=> B(x) *)
  let first_alloc = alloc_id in
  let last_alloc =
    if IdMap.mem alloc_id subst
    then IdMap.find alloc_id subst
    else alloc_id
  in
  (*
    [ Comment ("same_heap_content_pre" , mk_eq (mk_free_const pre_heap) (mk_free_const first_alloc));
      Comment ("same_heap_content_post", mk_eq (mk_free_const post_heap) (mk_free_const last_alloc)) ]
  *)
    [ mk_eq (mk_free_const pre_heap) (mk_free_const first_alloc);
      mk_eq (mk_free_const post_heap) (mk_free_const last_alloc) ]

let mk_entailment_query1 pre_sl pathf post_sl subst =
  let pre = Sl.to_grass pre_heap pre_sl in
  let post = subst_id subst (Sl.to_grass_negated post_heap post_sl) in
  (* query *)
  let query = smk_and ( (*Sl.make_axioms*) (mk_and [pre; post; pathf]) ::
                        (same_heap_axioms subst) )
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
