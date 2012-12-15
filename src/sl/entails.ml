open Form
open Axioms
open Stmnt

(* static declaration of the heaps *)
let pre_heap_id = "A"
let post_heap_id = "B"
let pre_heap = mk_ident pre_heap_id
let post_heap = mk_ident post_heap_id

let same_heap_axioms subst =
  (* heap matches: A(x) <=> B(x) *)
  let first_alloc = alloc_id in
  let last_alloc =
    if IdMap.mem alloc_id subst
    then IdMap.find alloc_id subst
    else alloc_id
  in
  let a_x = mk_pred pre_heap [var1] in
  let b_x = mk_pred post_heap [var1] in
    [ Comment ("same_heap_content_pre" , mk_equiv a_x (mk_pred first_alloc [var1]));
      Comment ("same_heap_content_post", mk_equiv b_x (mk_pred last_alloc [var1])) ]

let mk_entailment_query pre_sl path post_sl =
  let pre = Sl.to_lolli pre_heap_id pre_sl in

  let pathf, subst = ssa_partial IdMap.empty path in
  assert (List.length pathf = 1);
  let pathf = List.hd pathf in

  let post = Form.subst_id subst (Sl.to_lolli post_heap_id (Sl.mk_not post_sl)) in
  
  (* axioms from the logic *)
  let logic_axioms = List.flatten (make_axioms [ [pre]; pathf; [post]]) in
  
  (* query *)
  let query = smk_and ( pre :: post :: pathf @
                        (same_heap_axioms subst) @ logic_axioms )
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "query: ";
      print_form stdout query
    end
  in
    query

(*TODO test that ...*)
let check_entailment pre_sl path post_sl =
  let mk_query () = mk_entailment_query pre_sl path post_sl in
  let query = Util.measure_call "translation" mk_query () in
    Prover.satisfiable query
