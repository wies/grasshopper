open Util
open Form
open FormUtil
open Axioms

  
let choose_rep_terms classes =
  let find_rep cl = 
    try List.find (function App (_, [], _) -> true | _ -> false) cl
    with Not_found -> List.hd cl
  in
  List.fold_left (fun (reps, rep_map) cl ->
    let cl_rep : term = find_rep cl in
    (cl_rep :: reps, 
     List.fold_left (fun rep_map t -> TermMap.add t cl_rep rep_map) rep_map cl))
    ([], TermMap.empty) classes

let generate_terms generators ground_terms =
  let terms_by_sort srt sort_to_terms =
    try SrtMap.find srt sort_to_terms
    with Not_found -> TermSet.empty
  in
  let rec add_to_term_maps (sort_to_terms, new_terms) t =
    match t with
    | App (sym, ts, Some srt) ->
        let sort_terms = terms_by_sort srt sort_to_terms in     
        if TermSet.mem t sort_terms 
        then sort_to_terms, new_terms
        else 
          List.fold_left add_to_term_maps 
            (SrtMap.add srt (TermSet.add t sort_terms) sort_to_terms,
            TermSet.add t new_terms)
            ts
    | App _ -> failwith ("InstGen.generate_terms: sorted term expected, found " ^ (string_of_term t))
    | Var _ -> failwith ("InstGen.generate_terms: ground term expected, found "  ^ (string_of_term t))
  in
  let sort_to_terms, new_terms =
    TermSet.fold (fun t acc -> add_to_term_maps acc t)
      ground_terms (SrtMap.empty, TermSet.empty)
  in
  let find_matches sort_to_terms t1 sm =
    let srt = unsafe_sort_of t1 in
    let candidates = terms_by_sort srt sort_to_terms in
    let rec mt sm t1 t2 =
      match t1, t2 with 
      | App (sym1, ts1, srt1), App (sym2, ts2, srt2) 
        when sym1 = sym2 && srt1 = srt2 ->
          List.fold_left2 (fun sm_opt t1 t2 -> 
            match sm_opt with 
            | None -> None
            | Some sm -> mt sm t1 t2)
            (Some sm) ts1 ts2
      | Var (x, srt1), t2 when srt1 = sort_of t2 ->
          if IdMap.mem x sm then
            if IdMap.find x sm = t2 then Some sm
            else None
          else Some (IdMap.add x t2 sm)
      | _, _ -> None
    in
    TermSet.fold (fun t2 subst_maps ->
      match mt sm t1 t2 with
      | None -> subst_maps
      | Some sm -> (t2, sm) :: subst_maps)
      candidates []
  in
  let filter_term filter t = 
    match filter with
    | FilterTrue -> true
    | FilterNotOccurs sym -> 
        let rec hasSym = function
          | App (sym1, _, _) when sym1 = sym -> false
          | App (_, ts, _) -> List.for_all hasSym ts
          | _ -> true
        in hasSym t
  in
  let rec generate sort_to_terms new_terms old_terms = function
    | (bvs, fvs, guards, gen_term) :: generators1 ->
        let subst_maps =
          List.fold_left (fun subst_maps -> function Match (t, filter) -> 
            let new_subst_maps =
              List.fold_left 
                (fun new_subst_maps sm ->
                  let matches = find_matches sort_to_terms (subst_term sm t) sm in
                  Util.filter_map 
                    (fun (t_matched, _) -> 
                      filter_term filter t_matched)
                    (fun (t_matched, sm) -> 
                      (*print_string "Matched term: "; 
                      print_term stdout t_matched; 
                      print_newline ();*)
                      sm) matches @ new_subst_maps
                ) [] subst_maps 
            in
            new_subst_maps)
            [IdMap.empty] guards
        in
        let sort_to_terms1, new_terms1 =
          List.fold_left (fun acc sm ->
            let t = subst_term sm gen_term in
            (*print_string "Generated term: "; 
            print_term stdout t; 
            print_newline ();*)
            add_to_term_maps acc t)
            (sort_to_terms, new_terms) subst_maps
        in
        generate sort_to_terms1 new_terms1 old_terms generators1
    | [] -> 
        if new_terms <> old_terms 
        then 
          generate sort_to_terms new_terms new_terms generators
        else new_terms
  in
  generate sort_to_terms new_terms ground_terms generators

(*
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
      Debug.debug "TODO ordering of types for stratification!";
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
    List.fold_left
      (fun acc (a,b) ->
        let old = try SrtMap.find a acc with Not_found -> SrtSet.empty in
          SrtMap.add a (SrtSet.add b old) acc
      )
      unweighted
      intra_cc_edges
*)
let stratify_types axioms =
  let edges = [
    (Fld Loc, Loc);
    (Fld Int, Int);
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

let generate_instances useLocalInst axioms terms rep_map type_graph = 
  let ground_terms = 
    TermMap.fold (fun t _ acc -> TermSet.add t acc) rep_map TermSet.empty 
  in
  (* stratification: can a var of type t1 be used to generate a term of type t2 *)
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
  let closed_type_graph =
    SrtMap.fold (fun k _ acc -> close_graph k acc) type_graph SrtMap.empty
  in
  (*
  print_endline "YYY";
  SrtMap.iter (fun k v -> print_endline ((string_of_sort k) ^" -> "^ (String.concat " " (List.map string_of_sort (SrtSet.elements v))))) closed_type_graph;
  *)
  let can_reach a b =
    try SrtSet.mem b (SrtMap.find a closed_type_graph)
    with Not_found -> false
  in
  let is_stratified t1 t2 =
    let res = t1 <> t2 && not (can_reach t2 t1) in
      Debug.debug ("is_stratified("^(string_of_sort t1)^","^(string_of_sort t2)^") = "^(string_of_bool res)^"\n");
      res
  in
  (* *)
  let epr_axioms, axioms = 
    List.partition 
      (fun f -> useLocalInst && IdSrtSet.is_empty (vars_in_fun_terms f)) 
      axioms
  in
  (*print_endline "EPR:";
    List.iter print_endline (List.map string_of_form epr_axioms);*)
  (*let _ = print_endline "Candidate axioms for instantiation:" in
    let _ = print_forms stdout axioms in*)
  let instantiate acc f =
    let fvars0 = sorted_free_vars f in
    let fvars =
      if useLocalInst 
      then IdSrtSet.inter fvars0 (vars_in_fun_terms f)
      else fvars0
    in
    (* filter out what is stratified *)
    (*let fvars =
      let merge_map k a b = match (a,b) with
        | (Some a, Some b) -> Some (a @ b)
        | (Some a, None) -> Some a
        | (None, Some b) -> Some b
        | (None, None) -> None 
      in
      let rec gen_tpe acc t = match t with
        | App (_, ts, Some srt) ->
          List.fold_left
            (IdMap.merge merge_map)
            IdMap.empty
            (List.map (gen_tpe (srt::acc)) ts)
        | App (_, _, None) -> failwith "expecting typed form"
        | Var (id, _) -> IdMap.add id acc IdMap.empty
      in
      let gen_map =
        TermSet.fold
          (fun t acc -> IdMap.merge merge_map (gen_tpe [] t) acc)
          (fun_terms_with_vars f)
          IdMap.empty
      in
        (*
        print_endline "XXX";
        IdMap.iter (fun k v -> print_endline ((str_of_ident k) ^ " -> " ^ (String.concat "," (List.map string_of_sort v)))) gen_map;
        print_endline "ZZZ";
        IdSrtSet.iter (fun (id, srt) -> print_endline ((str_of_ident id)^", "^(string_of_sort srt))) fvars;
        *)
        if !Config.stratify && useLocalInst then
          IdSrtSet.filter
            (fun (id, srt) ->
              try
                let generating = IdMap.find id gen_map in
                  not (List.for_all (is_stratified srt) generating)
              with Not_found ->
                begin
                  print_endline ("BUG " ^ (str_of_ident id));
                  true
                end
            )
            fvars
        else fvars
    in*)
    let _ = if Debug.is_debug () then
      begin
        print_endline "--------------------";
        print_endline (string_of_form f);
        print_string "all  vars: ";
        print_endline (String.concat ", " (List.map str_of_ident (List.map fst (IdSrtSet.elements fvars0))));
        print_string "inst vars: ";
        print_endline (String.concat ", " (List.map str_of_ident (List.map fst (IdSrtSet.elements fvars))));
        print_endline "--------------------"
      end
    in
    (* collect all terms in which free variables appear below function symbols *)
    let fun_terms, fun_vs = 
      if not useLocalInst then [], IdSet.empty else
      let rec tt bv (fun_terms, fun_vs) t =
        match t with  
        | App (_, _, Some srt) when srt <> Bool -> 
            let vs = IdSet.diff (fvt IdSet.empty t) bv in
            if IdSet.is_empty vs
            then fun_terms, fun_vs
            else t :: fun_terms, IdSet.union vs fun_vs
        | App (fn, ts, _) -> List.fold_left (tt bv) (fun_terms, fun_vs) ts
        | _ -> fun_terms, fun_vs
      in fold_terms_with_bound tt ([], IdSet.empty) f
    in
    (* generate substitution maps for variables that appear below function symbols *)
    let proto_subst_maps =
      let find_rep t = TermMap.find t rep_map in
      let add_subst_map sm subst_maps =
        if List.mem sm subst_maps then subst_maps else sm :: subst_maps
      in
      let find_matches t1 sm subst_maps =
        let candidates = ground_terms in
        let rec mt sm t1 t2 =
          match t1, t2 with 
          | App (sym1, ts1, srt1), App (sym2, ts2, srt2) 
            when sym1 = sym2 && srt1 = srt2 ->
              begin
                try List.fold_left2 (fun sm_opt t1 t2 -> 
                  match sm_opt with 
                  | None -> None
                  | Some sm -> mt sm t1 t2)
                    (Some sm) ts1 ts2
                with Invalid_argument _ -> None
              end
          | Var (x, srt1), t2 when srt1 = sort_of t2 ->
              if IdMap.mem x sm then
                if IdMap.find x sm = find_rep t2 then Some sm
                else None
              else Some (IdMap.add x (find_rep t2) sm)
          | _, _ -> None
        in
        TermSet.fold (fun t2 subst_maps ->
          match mt sm t1 t2 with
          | None -> subst_maps
          | Some sm1 -> add_subst_map sm1 subst_maps)
          candidates subst_maps
      in
      List.fold_left 
        (fun subst_maps t ->
          List.fold_left 
            (fun subst_maps1 sm -> find_matches t sm subst_maps1)
            [] subst_maps)
        [IdMap.empty] fun_terms        
    in
    (* complete substitution maps for remaining variables *)
    let subst_maps = 
      IdSrtSet.fold 
        (fun (v, srt) subst_maps ->
          if IdSet.mem v fun_vs then subst_maps else
          List.fold_left 
            (fun acc t -> match t with
            | App (_, _, Some srt2) 
            | Var (_, Some srt2) when srt2 = srt ->
                let new_subst_maps = 
                  List.fold_left 
                    (fun acc sub ->
                      let new_sub = IdMap.add v t sub in
                      new_sub :: acc
                    ) acc subst_maps
                in
                new_subst_maps
            | _ -> acc)
            [] terms
        ) fvars proto_subst_maps
    in
    (*let _ = match f with
    | Binder (_, _, _, [Comment "entry-point1"]) ->
        begin
          print_endline "Axiom:";
          print_forms stdout [f];
          print_endline "fun_terms:";
          List.iter (fun t -> print_term stdout t; print_string ", ") fun_terms;
          print_endline "\nfvars: ";
          IdSrtSet.iter (fun (id, _) -> Printf.printf "%s, " (str_of_ident id)) fvars;
          print_endline "\nground_terms:";
          TermSet.iter (fun t -> print_term stdout t; print_newline ()) ground_terms;
          print_endline "\nproto_subst_maps:";
          List.iter print_subst_map proto_subst_maps;
          print_endline "\nsubst_maps:";
          List.iter print_subst_map subst_maps
        end
    | _ -> ()
    in*)
    (* generate instances of axiom *)
    List.fold_left (fun acc subst_map -> (*Axioms.mk_axiom2*) (subst subst_map f) :: acc) acc subst_maps
  in
  List.fold_left instantiate epr_axioms axioms
  

let instantiate_with_terms local axioms classes =
    if !Config.instantiate then
      let _ = 
        if Debug.is_debug () then
          ignore
            (List.fold_left (fun num cl ->
              print_string ("Class " ^ string_of_int num ^ ": ");
              List.iter (fun t -> print_string (string_of_term t ^ ", ")) cl; 
              print_newline ();
              num + 1) 1 classes)
      in
      let type_graph = stratify_types axioms in
      let _ = if Debug.is_debug () then
          begin
            print_endline "type stratification constraints:";
            SrtMap.iter
              (fun k v ->
                let vs = List.map string_of_sort (SrtSet.elements v) in
                let v_str = String.concat ", " vs in
                  print_endline ( "  " ^ (string_of_sort k) ^ " -> " ^ v_str))
              type_graph
          end;
      in
      let reps_f, rep_map_f = choose_rep_terms classes in
      let instances_f = generate_instances local axioms reps_f rep_map_f type_graph in
      instances_f
    else
      axioms

