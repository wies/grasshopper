open Form
open Axioms
open Stmnt

(* static declaration of the heaps *)
let pre_heap = mk_ident "A"
let post_heap = mk_ident "B"

type clausified = {
    bool_struct: Form.form;
    clauses: Form.form IdMap.t;
    disj: Form.form IdMap.t;
    tight: Form.form IdMap.t
  }

let combine prefix cls =
  let part_1 = List.map (fun f -> Comment (prefix ^ "clause", f)) (Sl.clauses_to_forms cls.clauses) in
  let part_2 = List.map (fun f -> Comment (prefix ^ "tight", f)) (Sl.clauses_to_forms cls.tight) in
  let part_3 = List.map (fun f -> Comment (prefix ^ "disj", f)) (Sl.clauses_to_forms cls.disj) in
    cls.bool_struct :: part_1 @ part_2 @ part_3

let alpha subst cls = 
  let subst_clauses clauses = IdMap.map (subst_id subst) clauses in
    { bool_struct = subst_id subst cls.bool_struct;
      clauses =  subst_clauses cls.clauses;
      disj = subst_clauses cls.disj;
      tight = subst_clauses cls.tight
    }

let negate cls =
  let fresh () = mk_const (fresh_ident "sk_var") in
  let negate_clauses clauses =
    IdMap.map
      (fun cl -> nnf (mk_not (skolemize fresh cl)))
      clauses
  in
    { bool_struct = nnf (mk_not cls.bool_struct);
      clauses = negate_clauses cls.clauses;
      disj = negate_clauses cls.disj;
      tight = negate_clauses cls.tight
    }

let combine_negated cls =
  (* assumes the set of trigger is the same for everybody *)
  let clauses_lst = [cls.clauses; cls.disj; cls.tight] in
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
    cls.bool_struct :: keysWithForm

let print_clauses prefix sl cls =
  let print_cls cl =
    IdMap.iter
      (fun t f -> print_form stdout (mk_implies (mk_pred t []) f))
      cl
  in
    print_endline (prefix ^ ": " ^ (Sl.to_string sl));
    print_endline (prefix ^ " converted:");
    print_form stdout cls.bool_struct;
    print_endline (prefix ^ " clauses:");
    print_cls cls.clauses;
    print_endline (prefix ^ " disj:");
    print_cls cls.disj;
    print_endline (prefix ^ " tight:");
    print_cls cls.tight


let translate pre_sl path post_sl =

  (* convert wo axioms and add axioms later *)
  let translate heap sl =
    let sl_n = Sl.normalize sl in
    let f, clauses = Sl.to_form_with_clauses heap sl_n in
    let disj = Sl.disjointness_constraints heap sl_n in
    let tight = Sl.tightness_constraints heap sl_n in
      { bool_struct = f;
        clauses = clauses;
        disj = disj;
        tight = tight
      }
  in
  let pre = translate pre_heap pre_sl in
  let post = translate post_heap post_sl in

  (* ssa *)

  let pathf, subst = ssa_partial IdMap.empty path in
  assert (List.length pathf = 1);
  let pathf = List.hd pathf in

  let post_subst = alpha subst post in

  (* show what we have *)
  let _ = if !Debug.verbose then
    begin
      print_clauses "pre" pre_sl pre;
      print_endline "path: ";
      List.iter (print_form stdout) pathf;
      print_clauses "post" post_sl post
    end
  in
    (pre, pathf, post_subst, subst)



(* negate post + add alloc + axioms *)
let mk_entailment_query pre pathf post_subst subst =
  let pre_combined = combine "pre_" pre in
  
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
  let post_neg = negate post_subst in
  let post_neg_combined = List.map (fun f -> Comment ("post", f)) (combine_negated post_neg) in

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
  let mk_query () =
    let (pre, pathf, post_subst, subst) = translate pre_sl path post_sl in
      mk_entailment_query pre pathf post_subst subst
  in
  let query = Util.measure_call "translation" mk_query () in
    Prover.satisfiable query
