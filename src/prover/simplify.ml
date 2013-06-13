open Form
open FormUtil
   
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
    | App (sym, ts, srt) -> 
        App (sym, List.map simp ts, srt)
    | t -> t
  in
  let submap, fs1 = 
    List.fold_right (fun f (submap, fs1) -> 
      match f with
      | Atom (App (Eq, [App (FreeSym id, [], _); App (Empty, [], srt)], _)) 
      | Atom (App (Eq, [App (Empty, [], srt); App (FreeSym id, [], _)], _)) ->
          IdMap.add id (App (Empty, [], srt)) submap, fs1
      | _ -> submap, f :: fs1) fs (IdMap.empty, [])
  in
  if IdMap.is_empty submap then fs else 
  let fs2 = List.map (fun f -> map_terms simp (subst_consts submap f)) fs1 in
  simplify_sets fs2
  
let simplify fs = simplify_sets fs
