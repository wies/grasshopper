open Util
open Grass
open GrassUtil

let transitive_closure type_graph =
  let rec close_graph v acc =
    if SortMap.mem v acc then acc
    else
      try
        let s = SortMap.find v type_graph in
        let acc = SortSet.fold close_graph s acc in
        let succ = SortSet.fold (fun s set -> SortSet.union set (SortMap.find s acc) ) s s in
          SortMap.add v succ acc
      with Not_found -> SortMap.add v SortSet.empty acc
  in
    SortMap.fold (fun k _ acc -> close_graph k acc) type_graph SortMap.empty

(* returns a DAG of type dependencies. *)
let stratify_types axioms =
  (* 1: build a weighted graph of dependencies.
   *   (a, b) means terms of type a generate terms of type b *)
  let fs = mk_and axioms in
  let terms = fun_terms_with_vars fs in
  let edges =
    TermSet.fold
      (fun t acc -> match t with
        | App (sym, ts, tpe) ->
          assert (ts <> []);
          List.fold_left
            (fun acc t2 -> 
              if not (IdSet.is_empty (fv_term t2))
              then (sort_of t2, tpe) :: acc
              else acc)
            acc
            ts
        | _ -> failwith ("stratify_types expect a type formula")
      ) terms []
  in
  let edges = List.filter (fun (a,b) -> a <> b) edges in (* remove the self loops *)
  let add_edge graph (a, b) =
    let old_a = try SortMap.find a graph with Not_found -> SortMap.empty in
    let old_b = try SortMap.find b old_a with Not_found -> 0 in
      SortMap.add a (SortMap.add b (old_b + 1) old_a) graph
  in
  let graph =
    List.fold_left
      add_edge
      SortMap.empty
      edges
  in
  (* 2: SCC decomposion of the type deps *)
  let succ v =
    try SortMap.find v graph
    with Not_found -> SortMap.empty
  in
  let all_succ v =
    SortMap.fold
      (fun v2 _ acc -> SortSet.add v2 acc)
      (succ v)
      SortSet.empty
  in
  let vs =
    SortMap.fold
      (fun k v acc ->
        SortMap.fold
          (fun k _ acc -> SortSet.add k acc)
          v
          (SortSet.add k acc)
      )
      graph
      SortSet.empty
  in
  let scc =
    (* Tarjan algorithm *)
    let i = ref 0 in
    let idx = ref SortMap.empty in
    let lowlink = ref SortMap.empty in
    let stack = ref [] in
    let ccs = ref [] in
    let rec connect v =
      idx := SortMap.add v !i !idx;
      lowlink := SortMap.add v !i !lowlink;
      i := !i + 1;
      stack := v :: !stack;
      SortSet.iter
        (fun w ->
          if not (SortMap.mem w !idx) then
            begin
              connect w;
              lowlink := SortMap.add v (min (SortMap.find v !lowlink) (SortMap.find w !lowlink)) !lowlink
            end
          else if List.mem w !stack then
            lowlink := SortMap.add v (min (SortMap.find v !lowlink) (SortMap.find w !idx)) !lowlink
        )
        (all_succ v);
      if (SortMap.find v !lowlink) = (SortMap.find v !idx) then
        begin
          let rec pop acc = match !stack with
            | x :: xs ->
              stack := xs;
              if (x <> v) then pop (x :: acc)
              else acc
            | [] -> failwith "Tarjan: empty stack!"
          in
            ccs := (pop [v]) :: !ccs
        end
    in
      SortSet.iter
        (fun v ->
          if not (SortMap.mem v !idx) then
            connect v)
        vs;
      !ccs
  in
  (* 3: find the set of edges with smallest weight such that remove them makes a DAG 
        break symmetry using a default order *)
  let default_priorities =
    [ Map (Loc, Loc), 6 ;
      Map (Loc, Int), 5 ;
      Loc, 4 ;
      Int, 3 ;
      Set Loc, 2 ;
      Set Int, 1 ]
  in
  let get_priority t =
    try List.assoc t default_priorities
    with Not_found -> 7
  in
  let sequencify lst =
    if List.length lst > 1 then
      Debug.debug (fun () -> "TODO ordering of types for stratification!\n");
    snd (
      List.split (
        List.stable_sort compare (
          List.map
            (fun t -> (get_priority t, t))
            lst)))
  in
  let order = List.map sequencify scc in
  let intra_cc_edges =
    let rec window acc curr lst = match lst with
      | x::xs -> window ((curr, x) :: acc) x xs
      | [] -> acc
    in
      Util.flat_map
        (fun l -> window [] (List.hd l) (List.tl l))
        order
  in
  let unweighted =
    SortMap.mapi
      (fun k v ->
        let v = SortMap.fold (fun k _ acc -> SortSet.add k acc) v SortSet.empty in
        let cc = List.find (List.mem k) scc in
          SortSet.filter (fun x -> not (List.mem x cc)) v
      )
      graph
  in
  let graph =
    List.fold_left
      (fun acc (a,b) ->
        let old = try SortMap.find a acc with Not_found -> SortSet.empty in
          SortMap.add a (SortSet.add b old) acc
      )
      unweighted
      intra_cc_edges
  in
    if Debug.is_debug 1 then
      begin
        print_endline "type stratification constraints:";
        SortMap.iter
          (fun k v ->
            let vs = List.map string_of_sort (SortSet.elements v) in
            let v_str = String.concat ", " vs in
              print_endline ( "  " ^ (string_of_sort k) ^ " -> " ^ v_str))
          graph
      end;
    graph

let default_type_stratification =
  let edges = [
    (Map (Loc, Bool), Bool);
    (Map (Loc, Loc), Loc);
    (Map (Loc, Int), Int);
    (Bool, Loc);
    (Loc, Int);
    (Loc, Set Loc);
    (Int, Set Int)
    ]
  in
    List.fold_left
      (fun acc (a, b) ->
        let old = try SortMap.find a acc with Not_found -> SortSet.empty in
          SortMap.add a (SortSet.add b old) acc
      )
      SortMap.empty
      edges

let type_graph: (SortSet.t SortMap.t) option ref = ref None

let get () = match !type_graph with
  | None ->
    Debug.warn (fun () -> "Type stratification was not initialized, using the default one!\n");
    default_type_stratification
  | Some ts -> ts

let init fs =
  if !type_graph <> None then
    Debug.warn (fun () -> "Type stratification is already existing!\n");
  type_graph := Some (stratify_types fs)

let default () =
  if !type_graph <> None then
    Debug.warn (fun () -> "Type stratification is already existing!\n");
  type_graph := Some default_type_stratification

let reset () = 
  type_graph := None
