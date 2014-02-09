open Util
open Form
open FormUtil

let transitive_closure type_graph =
  let rec close_graph v acc =
    if SrtMap.mem v acc then acc
    else
      try
        let s = SrtMap.find v type_graph in
        let acc = SrtSet.fold close_graph s acc in
        let succ = SrtSet.fold (fun s set -> SrtSet.union set (SrtMap.find s acc) ) s s in
          SrtMap.add v succ acc
      with Not_found -> SrtMap.add v SrtSet.empty acc
  in
    SrtMap.fold (fun k _ acc -> close_graph k acc) type_graph SrtMap.empty

(* returns a DAG of type dependencies. *)
let stratify_types axioms =
  (* 1: build a weighted graph of dependencies.
   *   (a, b) means terms of type a generate terms of type b *)
  let fs = mk_and axioms in
  let terms = fun_terms_with_vars fs in
  let edges =
    TermSet.fold
      (fun t acc -> match t with
        | App (sym, ts, Some tpe) ->
          assert (ts <> []);
          List.fold_left
            (fun acc t2 -> 
              if not (IdSet.is_empty (fvt IdSet.empty t2))
              then (Util.unopt (sort_of t2), tpe) :: acc
              else acc)
            acc
            ts
        | _ -> failwith ("stratify_types expect a type formula")
      ) terms []
  in
  let edges = List.filter (fun (a,b) -> a <> b) edges in (* remove the self loops *)
  let add_edge graph (a, b) =
    let old_a = try SrtMap.find a graph with Not_found -> SrtMap.empty in
    let old_b = try SrtMap.find b old_a with Not_found -> 0 in
      SrtMap.add a (SrtMap.add b (old_b + 1) old_a) graph
  in
  let graph =
    List.fold_left
      add_edge
      SrtMap.empty
      edges
  in
  (* 2: SCC decomposion of the type deps *)
  let succ v =
    try SrtMap.find v graph
    with Not_found -> SrtMap.empty
  in
  let all_succ v =
    SrtMap.fold
      (fun v2 _ acc -> SrtSet.add v2 acc)
      (succ v)
      SrtSet.empty
  in
  let vs =
    SrtMap.fold
      (fun k v acc ->
        SrtMap.fold
          (fun k _ acc -> SrtSet.add k acc)
          v
          (SrtSet.add k acc)
      )
      graph
      SrtSet.empty
  in
  let scc =
    (* Tarjan algorithm *)
    let i = ref 0 in
    let idx = ref SrtMap.empty in
    let lowlink = ref SrtMap.empty in
    let stack = ref [] in
    let ccs = ref [] in
    let rec connect v =
      idx := SrtMap.add v !i !idx;
      lowlink := SrtMap.add v !i !lowlink;
      i := !i + 1;
      stack := v :: !stack;
      SrtSet.iter
        (fun w ->
          if not (SrtMap.mem w !idx) then
            begin
              connect w;
              lowlink := SrtMap.add v (min (SrtMap.find v !lowlink) (SrtMap.find w !lowlink)) !lowlink
            end
          else if List.mem w !stack then
            lowlink := SrtMap.add v (min (SrtMap.find v !lowlink) (SrtMap.find w !idx)) !lowlink
        )
        (all_succ v);
      if (SrtMap.find v !lowlink) = (SrtMap.find v !idx) then
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
      SrtSet.iter
        (fun v ->
          if not (SrtMap.mem v !idx) then
            connect v)
        vs;
      !ccs
  in
  (* 3: find the set of edges with smallest weight such that remove them makes a DAG 
        break symmetry using a default order *)
  let default_priorities =
    [ Fld Loc, 6 ;
      Fld Int, 5 ;
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
    SrtMap.mapi
      (fun k v ->
        let v = SrtMap.fold (fun k _ acc -> SrtSet.add k acc) v SrtSet.empty in
        let cc = List.find (List.mem k) scc in
          SrtSet.filter (fun x -> not (List.mem x cc)) v
      )
      graph
  in
  let graph =
    List.fold_left
      (fun acc (a,b) ->
        let old = try SrtMap.find a acc with Not_found -> SrtSet.empty in
          SrtMap.add a (SrtSet.add b old) acc
      )
      unweighted
      intra_cc_edges
  in
    if Debug.is_debug () then
      begin
        print_endline "type stratification constraints:";
        SrtMap.iter
          (fun k v ->
            let vs = List.map string_of_sort (SrtSet.elements v) in
            let v_str = String.concat ", " vs in
              print_endline ( "  " ^ (string_of_sort k) ^ " -> " ^ v_str))
          graph
      end;
    graph

let default_type_stratification =
  let edges = [
    (Fld Bool, Bool);
    (Fld Loc, Loc);
    (Fld Int, Int);
    (Bool, Loc);
    (Loc, Int);
    (Loc, Set Loc);
    (Int, Set Int)
    ]
  in
    List.fold_left
      (fun acc (a, b) ->
        let old = try SrtMap.find a acc with Not_found -> SrtSet.empty in
          SrtMap.add a (SrtSet.add b old) acc
      )
      SrtMap.empty
      edges

let type_graph: (SrtSet.t SrtMap.t) option ref = ref None

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
