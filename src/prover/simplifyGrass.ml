open Grass
open GrassUtil


(** Pull up equalities of the form "x = t" below disjunctions when x occurs only in a single disjunct
 ** Assumes that [f] is typed and in NNF, returns a formula in NNF *)
(* TODO inefficient implementation, lots of redundent computation *)
let pull_up_equalities fs =
  (* phrase this as a rewrite rule ?? *)
  (* identifies the constants/ground terms that are only in one disjunct
   * be careful about pulling eq with literals and/or pulling more than one eq *)
  let rec find id elts = match elts with
    (* pull out at most one eq per candidate *)
    | (Atom (App (Eq, [App (FreeSym id1, [], _); e], _), _) as x) :: xs 
    | (Atom (App (Eq, [e; App (FreeSym id1, [], _)], _), _) as x) :: xs when id1 = id -> [x], xs
    | x :: xs ->
      let y, ys = find id xs in
        y, x :: xs
    | [] -> [], []
  in
  let find_eq candidates f = match f with
    | BoolOp (And, conjuncts) ->
      let pulled, conjs =
        IdSet.fold
          (fun id (pulled, eqs) ->
            let p, eqs = find id eqs in
              (p @ pulled, eqs) )
          candidates
          ([], conjuncts)
      in
        pulled, smk_and conjs
    | f -> [] , f
  in
  let process_disj disj gts =
    let rec p pulled pre post = match post with
      | x :: xs ->
        let other_free_cst = IdSet.union (free_consts (mk_and pre)) (free_consts (mk_and xs)) in
        let candidates = IdSet.diff (free_consts x) other_free_cst in
        let eqs, fs = find_eq candidates x in
          p (eqs @ pulled) (fs :: pre) xs
      | [] -> pulled, pre
    in
    let pulled, disj = p [] [] disj in
      (smk_or disj) :: pulled
  in
  let rec process pre post = match post with
    | x :: xs ->
      begin
        match x with
        | BoolOp (Or, disjuncts) ->
          (*let disjuncts = List.map (fun d -> ...) disjuncts in (*TODO recurse *)*)
          let pre_free_cst = free_consts (mk_and pre) in
          let post_free_cst = free_consts (mk_and xs) in
          let new_fs = process_disj disjuncts (IdSet.union pre_free_cst post_free_cst) in
            process (new_fs @ pre) xs
        | _ -> process (x::pre) xs
      end
    | [] -> pre
  in
    process [] fs

(** Eliminate certain field reads using reachability predicates *)   
let massage_field_reads fs = 
  let reach_flds = 
    fold_terms (fun flds -> function
      | App (Btwn, Var _ :: _, _) -> flds
      | App (Btwn, fld :: _, _) -> TermSet.add fld flds
      | _ -> flds)
      TermSet.empty (mk_and fs)
  in
  let rec massage = function 
  | BoolOp (And as op, fs)
  | BoolOp (Or as op, fs) -> BoolOp (op, List.map massage fs)
  | Binder (b, vs, f, a) -> Binder (b, vs, massage f, a)
  | Atom (App (Eq, [App (Read, [fld; Var _ as arg], Loc _); App (FreeSym _, [], _) as t], _), a)
  | Atom (App (Eq, [App (FreeSym _, [], _) as t; App (Read, [fld; Var _ as arg], Loc _)], _), a) 
    when TermSet.mem fld reach_flds ->
      let sid = match sort_of fld with
        | Map ([Loc s], _) -> s
        | _ -> failwith "massage_field_reads: field has not Map<Loc _, _> type"
      in
      let l1 = Axioms.l1 sid in
      let loc1 = Axioms.loc1 sid in
      let f1 = 
        annotate
          (mk_and [mk_btwn fld arg t t;
                   mk_or [mk_neq arg t; 
                          mk_forall [l1]
                            (mk_or [mk_not (mk_reach fld t loc1); mk_eq t loc1])];
                   mk_forall [l1]
                     (mk_or [mk_eq loc1 arg; mk_eq loc1 t; 
                             mk_not (mk_btwn fld arg loc1 t)])]) a
      in
      f1
  | f -> f
  in List.map massage fs


(** Simplify set expressions by propagating empty sets, etc. *)
let rec simplify_sets fs =
  let rec simp (t : term) = 
    match t with
    | App (Union, ts, srt) ->
        let ts1 =
          List.filter
            (function App (Empty, [], _) -> false | _ -> true)
            (List.map simp ts)
        in
        (match ts1 with
        | [] -> mk_empty srt
        | _ -> mk_union ts1)
    | App (Inter, ts, srt) ->
        let ts1 = List.map simp ts in
        if List.exists (function App (Empty, [], _) -> true | _ -> false) ts1
        then mk_empty srt
        else App (Inter, ts1, srt)
    | App (Diff, [s1; s2], srt) ->
      let s1' = simp s1 in
      let s2' = simp s2 in
        if s1' = s2' then mk_empty srt
        else
          begin
            match (s1', s2') with
            | (App (Empty, _, _), s) | (s, App (Empty, _, _)) -> s
            | (App (SetEnum, ts1, _), App (SetEnum, ts2, _)) ->
              let ts = List.filter (fun t -> not (List.mem t ts2)) ts1 in
                mk_setenum ts
            | _ -> mk_diff s1' s2'
          end
    | App (Disjoint, [s1; s2], _) ->
      let s1' = simp s1 in
      let s2' = simp s2 in
      (match s1', s2' with
      | App (Empty, _, _), _ | _, App (Empty, _, _) -> mk_true_term
      | _ -> mk_disjoint_term s1' s2')
    (*| App (SetEnum, ts, srt) -> ...*)
    | App (sym, ts, srt) -> 
        App (sym, List.map simp ts, srt)
    | Var _ -> t
  in
  let fs1 = List.map (fun f -> map_terms simp f) fs in
  let submap, fs2 = 
    List.fold_right (fun f (submap, fs1) -> 
      match f with
      | Atom (App ((Eq | SubsetEq), [App (FreeSym id, [], _); App (Empty, [], srt)], _), _) 
      | Atom (App (Eq, [App (Empty, [], srt); App (FreeSym id, [], _)], _), _) ->
          IdMap.add id (App (Empty, [], srt)) submap, fs1
      | _ -> submap, f :: fs1) fs1 (IdMap.empty, [])
  in
  if IdMap.is_empty submap then fs2 else 
  simplify_sets (List.map (subst_consts submap) fs2)

let simplify_one_sets f =
  split_ands [f] |>
  simplify_sets |>
  mk_and
  
    
let simplify fs = simplify_sets fs
