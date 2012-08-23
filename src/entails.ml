open Form
open Axioms
open Stmnt

let translate pre_sl path post_sl =
  let pre_heap = mk_ident "A" in
  let post_heap = mk_ident "B" in

  let print_clauses cl =
    IdMap.iter
      (fun t f -> print_form stdout (mk_implies (mk_pred t []) f))
      cl
  in

  (* convert wo axioms and add axioms later *)
  let translate heap sl =
    let sl_n = Sl.normalize sl in
    let f, clauses = Sl.to_form_with_clauses heap sl_n in
    let disj = Sl.disjointness_constraints heap sl_n in
    let tight = Sl.tightness_constraints heap sl_n in
      (f, clauses, disj, tight)
  in
  let (pre, clauses_pre, disj_pre, tight_pre) = translate pre_heap pre_sl in
  let (post, clauses_post, disj_post, tight_post) = translate post_heap post_sl in

  (* ssa *)
  let pre_1 = List.map (fun f -> Comment ("clause_pre", f)) (Sl.clauses_to_forms clauses_pre) in
  let pre_2 = List.map (fun f -> Comment ("tight_pre", f)) (Sl.clauses_to_forms tight_pre) in
  let pre_3 = List.map (fun f -> Comment ("disj_pre", f)) (Sl.clauses_to_forms disj_pre) in
  let pre_combined = pre :: pre_1 @ pre_2 @ pre_3 in

  let pathf, subst = ssa_partial IdMap.empty path in
  assert (List.length pathf = 1);
  let pathf = List.hd pathf in

  let subst_clauses clauses = IdMap.map (subst_id subst) clauses in
  let post_subst = subst_id subst post in
  let clauses_post_subst = subst_clauses clauses_post in
  let disj_post_subst = subst_clauses disj_post in
  let tight_post_subst = subst_clauses tight_post in

  (* show what we have *)
  let _ = if !Debug.verbose then
    begin
      print_endline ("pre: " ^ (Sl.to_string pre_sl));
      print_endline "pre converted (with axioms):";
      List.iter (print_form stdout) pre_combined;

      print_endline "path: ";
      List.iter (print_form stdout) pathf;

      print_endline ("post: " ^ (Sl.to_string post_sl));
      print_endline "post converted:";
      print_form stdout post_subst;
      print_endline "post clauses:";
      print_clauses clauses_post_subst;
      print_endline "post disj:";
      print_clauses disj_post_subst;
      print_endline "post tight:";
      print_clauses tight_post_subst
    end
  in
  
  (* heap matches: A(x) <=> B(x) *)
  let first_alloc = alloc_id in
  let last_alloc =
    if IdMap.mem alloc_id subst
    then IdMap.find alloc_id subst
    else alloc_id
  in
  let a_x = mk_pred pre_heap [var1] in
  let b_x = mk_pred post_heap [var1] in
  let same_heap_content =
    [ Comment ("same_heap_content_pre" , mk_equiv a_x (mk_pred first_alloc [var1]));
      Comment ("same_heap_content_post", mk_equiv b_x (mk_pred last_alloc [var1])) ]
  in


  (* negating the post condition (need to skolemize axioms) *)
  let fresh () = mk_const (fresh_ident "sk_var") in
  let negate_clauses clauses =
    IdMap.map
      (fun cl -> nnf (mk_not (skolemize fresh cl)))
      clauses
  in
  let post_neg = nnf (mk_not post_subst) in
  let clauses_post_neg = negate_clauses clauses_post_subst in
  let disj_post_neg = negate_clauses disj_post_subst in
  let tight_post_neg = negate_clauses tight_post_subst in

  let combine_clauses clauses_lst =
    (* assumes the set of trigger is the same for everybody *)
    assert (clauses_lst <> []);
    let keys = IdMap.fold (fun t _ acc -> t::acc) (List.hd clauses_lst) [] in
    let keysWithForm =
      List.map
        (fun trig ->
          let depends_on_trig = List.map (fun cl -> IdMap.find trig cl) clauses_lst in
          (*the negation of the trigger is important!*)
          mk_implies (mk_not (mk_pred trig [])) (smk_or depends_on_trig)
        )
        keys
    in
      keysWithForm
  in
  
  let cl_combined = combine_clauses [clauses_post_neg; disj_post_neg; tight_post_neg] in
  let post_neg_combined = List.map (fun f -> Comment ("post", f)) (post_neg :: cl_combined) in

  (* axioms from the logic *)
  let logic_axioms = List.flatten (make_axioms [ pre_combined; pathf; post_neg_combined]) in

  (* query *)
  let query = smk_and ( same_heap_content @ pre_combined @
                        pathf @ post_neg_combined @ logic_axioms )
  in
  let _ = if !Debug.verbose then
    begin
      print_endline "post negated: ";
      List.iter (print_form stdout) post_neg_combined;
      print_endline "query: ";
      print_form stdout query
    end
  in
    query

let check_entailment pre_sl path post_sl =
  let mk_query () = translate pre_sl path post_sl in
  let query = Util.measure_call "translation" mk_query () in
    Prover.satisfiable query
