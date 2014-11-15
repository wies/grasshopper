open Grass
open GrassUtil


(* pull out '=' below disj when on of the variable is occuring in a single branch of the disj
 * Assumes that [f] is typed and in NNF, return a formula in NNF *)
(* TODO inefficient implementation, lots of redundent computation *)
let pull_eq_up fs =
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
        | [t] -> t
        | _ -> App (Union, ts1, srt))
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
            | (App (Empty, _, _), _) | (_, App (Empty, _, _)) -> s1'
            | (App (SetEnum, ts1, _), App (SetEnum, ts2, _)) ->
              let ts = List.filter (fun t -> not (List.mem t ts2)) ts1 in
                mk_setenum ts
            | _ -> mk_diff s1' s2'
          end
    (*| App (SetEnum, ts, srt) -> ...*)
    | App (sym, ts, srt) -> 
        App (sym, List.map simp ts, srt)
    | t -> t
  in
  let submap, fs1 = 
    List.fold_right (fun f (submap, fs1) -> 
      match f with
      | Atom (App (Eq, [App (FreeSym id, [], _); App (Empty, [], srt)], _), _) 
      | Atom (App (Eq, [App (Empty, [], srt); App (FreeSym id, [], _)], _), _) ->
          IdMap.add id (App (Empty, [], srt)) submap, fs1
      | _ -> submap, f :: fs1) fs (IdMap.empty, [])
  in
  if IdMap.is_empty submap then fs else 
  let fs2 = List.map (fun f -> map_terms simp (subst_consts submap f)) fs1 in
  simplify_sets fs2
  
let simplify fs = simplify_sets fs
