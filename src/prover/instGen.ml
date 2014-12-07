open Util
open Grass
open GrassUtil
open Axioms

module TermListSet = Set.Make(struct
    type t = term list
    let compare = compare
  end)

module EGraph = Map.Make(struct
    type t = term * symbol
    let compare = compare
  end)
  
let choose_rep_terms classes =
  let find_rep cl = 
    try List.find (function App (_, [], _) -> true | _ -> false) cl
    with Not_found -> List.hd cl
  in
  let reps, rep_map =
    List.fold_left (fun (reps, rep_map) cl ->
      let cl_rep : term = find_rep cl in
      (TermSet.add cl_rep reps, 
       List.fold_left (fun rep_map t -> TermMap.add t cl_rep rep_map) rep_map cl))
      (TermSet.empty, TermMap.empty) classes
  in
  let egraph = 
    List.fold_left (fun egraph -> 
      function
        | App (sym, ts, _) as t -> 
            begin
              try
                let t_rep = TermMap.find t rep_map in
                let ts_reps = List.map (fun t -> TermMap.find t rep_map) ts in
                let other_ts_reps =
                  try EGraph.find (t_rep, sym) egraph
                  with Not_found -> TermListSet.empty
                in
                EGraph.add (t_rep, sym) (TermListSet.add ts_reps other_ts_reps) egraph
              with Not_found -> egraph
            end
        | _ -> egraph)
      EGraph.empty (List.concat classes)
  in reps, egraph

let ematch t rep_terms egraph subst_maps =
  let rec ematches ts1 ts2s subst_maps =
    TermListSet.fold 
      (fun ts2 out_subst_maps ->
        try 
          let out_subst_maps1 =
            List.fold_left2 
              (fun subst_maps1 t1 t2 -> 
                match subst_maps with 
                | [] -> []
                | _ -> ematch t1 t2 subst_maps1)
              subst_maps ts1 ts2
          in 
          List.rev_append out_subst_maps1 out_subst_maps
        with Invalid_argument _ -> out_subst_maps)
      ts2s []
  and ematch t1 t2 subst_maps =
    match t1 with 
    | App (sym1, ts1, srt1) when srt1 = sort_of t2 ->
        begin
          try
            let ts2s = EGraph.find (t2, sym1) egraph in
            ematches ts1 ts2s subst_maps
          with Not_found -> []
        end
    | Var (x, srt1) when srt1 = sort_of t2 ->
        List.fold_left 
          (fun out_subst_maps sm ->
            if IdMap.mem x sm then
              if IdMap.find x sm = t2 
              then sm :: out_subst_maps
              else out_subst_maps
            else IdMap.add x t2 sm :: out_subst_maps)
          [] subst_maps
    | _ -> []
  in
  let terms = 
    TermSet.fold 
      (fun t terms -> TermListSet.add [t] terms) 
      rep_terms TermListSet.empty 
  in
  ematches [t] terms subst_maps

let generate_terms generators ground_terms =
  let rec add_terms new_terms t =
    if TermSet.mem t new_terms then new_terms else
    match t with
    | App (sym, ts, _) ->
        List.fold_left add_terms (TermSet.add t new_terms) ts
    | Var _ -> failwith ("InstGen.generate_terms: ground term expected, found "  ^ (string_of_term t))
  in
  let new_terms =
    TermSet.fold (fun t acc -> add_terms acc t)
      ground_terms TermSet.empty
  in
  let find_matches candidates t1 sm =
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
  let filter_term filter t sm = 
    match filter with
    | FilterTrue -> true
    | FilterSymbolNotOccurs sym ->
        let rec not_occurs = function
          | App (sym1, _, _) when sym1 = sym -> false
          | App (_, ts, _) -> List.for_all not_occurs ts
          | _ -> true
        in not_occurs t
    | FilterNameNotOccurs (name, (arg_srts, res_srt)) ->
        let rec not_occurs = function
          | App (FreeSym (name1, _), ts, res_srt1) ->
              let ok =
                try
                  name1 <> name ||
                  res_srt1 <> res_srt ||
                  List.fold_left2 (fun acc t1 srt -> acc || sort_of t1 <> srt) false ts arg_srts 
                with Invalid_argument _ -> true
              in ok && List.for_all not_occurs ts
          | App (_, ts, _) -> List.for_all not_occurs ts
          | _ -> true
        in not_occurs t
    | FilterGeneric fn -> fn sm t
  in
  let rec generate new_terms old_terms = function
    | (bvs, fvs, guards, gen_term) :: generators1 ->
        let subst_maps =
          List.fold_left (fun subst_maps -> function Match (t, filter) -> 
            let new_subst_maps =
              List.fold_left 
                (fun new_subst_maps sm ->
                  let matches = find_matches new_terms (subst_term sm t) sm in
                  Util.filter_rev_map 
                    (fun (t_matched, sm) ->
                      (*let _ = print_endline ("Matched " ^ string_of_term t_matched) in*)
                      filter_term filter t_matched sm)
                    (fun (t_matched, sm) -> 
                      sm) matches @ new_subst_maps
                ) [] subst_maps 
            in
            new_subst_maps)
            [IdMap.empty] guards
        in
        let new_terms1 =
          List.fold_left (fun acc sm ->
            let t = subst_term sm gen_term in
            add_terms acc t)
            new_terms subst_maps
        in
        generate new_terms1 old_terms generators1
    | [] -> 
        if new_terms <> old_terms 
        then 
          generate new_terms new_terms generators
        else new_terms
  in
  generate new_terms ground_terms generators


let generate_instances useLocalInst axioms rep_terms egraph type_graph = 
  (* stratification: can a var of type t1 be used to generate a term of type t2 *)
  let closed_type_graph = TypeStrat.transitive_closure type_graph in
  let can_reach a b =
    try SortSet.mem b (SortMap.find a closed_type_graph)
    with Not_found -> false
  in
  let is_stratified t1 t2 =
    let res = t1 <> Int && t1 <> t2 && not (can_reach t2 t1) in
      Debug.debugl 1 (fun () -> "is_stratified("^(string_of_sort t1)^","^(string_of_sort t2)^") = "^(string_of_bool res)^"\n");
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
    let fvars, strat_vars =
      let merge_map k a b = match (a,b) with
        | (Some a, Some b) -> Some (a @ b)
        | (Some c, None) | (None, Some c) -> Some c
        | (None, None) -> None 
      in
      let rec gen_tpe acc t = match t with
      | App (_, ts, srt) ->
          List.fold_left
            (IdMap.merge merge_map)
            IdMap.empty
            (List.map (gen_tpe (srt :: acc)) ts)
      | Var (id, _) -> IdMap.add id acc IdMap.empty
      in
      let gen_map =
        TermSet.fold
          (fun t acc -> IdMap.merge merge_map (gen_tpe [] t) acc)
          (fun_terms_with_vars f)
          IdMap.empty
      in
        if !Config.stratify && useLocalInst then
          IdSrtSet.partition
            (fun (id, srt) ->
              try
                let generating = IdMap.find id gen_map in
                  not (List.for_all (is_stratified srt) generating)
              with Not_found ->
                begin
                  Debug.warn (fun () -> "BUG in stratification: " ^ (string_of_ident id) ^ "\n");
                  true
                end
            )
            fvars
        else fvars, IdSrtSet.empty
    in
    let _ = if Debug.is_debug 1 then
      begin
        print_endline "--------------------";
        print_endline (string_of_form f);
        print_string "all  vars: ";
        print_endline (String.concat ", " (List.map string_of_ident (List.map fst (IdSrtSet.elements fvars0))));
        print_string "inst vars: ";
        print_endline (String.concat ", " (List.map string_of_ident (List.map fst (IdSrtSet.elements fvars))));
        print_endline "--------------------"
      end
    in
    (* close the strat_vars so they are not instantiated *)
    let f =
      if not (IdSrtSet.is_empty strat_vars)
      then mk_forall (IdSrtSet.elements strat_vars) f
      else f
    in
    (* collect all terms in which free variables appear below function symbols *)
    let fun_terms, fun_vs = 
      if not useLocalInst then TermSet.empty, IdSet.empty else
      let rec tt bv (fun_terms, fun_vs) t =
        match t with  
        | App (_, _, srt) when srt <> Bool -> 
            let vs = IdSet.diff (fv_term t) bv in
            if IdSet.is_empty vs
            then fun_terms, fun_vs
            else TermSet.add t fun_terms, IdSet.union vs fun_vs
        | App (fn, ts, _) -> List.fold_left (tt bv) (fun_terms, fun_vs) ts
        | _ -> fun_terms, fun_vs
      in fold_terms_with_bound tt (TermSet.empty, IdSet.empty) f
    in
    (* generate substitution maps *)
    let subst_maps () =
      (* generate substitution maps for variables that appear below function symbols *)
      let proto_subst_maps =
        TermSet.fold
          (fun t subst_maps -> ematch t rep_terms egraph subst_maps)
          fun_terms [IdMap.empty]
      in
      (* complete substitution maps for remaining variables *)
      IdSrtSet.fold 
        (fun (v, srt) subst_maps -> 
          if IdSet.mem v fun_vs 
          then subst_maps
          else ematch (Var (v, srt)) rep_terms egraph subst_maps)
        fvars proto_subst_maps         
    in
    let subst_maps = (*measure*) subst_maps () in
    (*let _ = match f with
    | Binder (_, _, _, [Comment _ (*"entry-point1"*)]) ->
        begin
          print_endline "Axiom:";
          print_forms stdout [f];
          print_endline "fun_terms:";
          TermSet.iter (fun t -> print_term stdout t; print_string ", ") fun_terms;
          print_endline "\nfvars: ";
          IdSrtSet.iter (fun (id, _) -> Printf.printf "%s, " (string_of_ident id)) fvars;
          print_endline "\nrep_terms:";
          TermSet.iter (fun t -> print_term stdout t; print_newline ()) terms;
          print_endline "\nground_terms:";
          TermSet.iter (fun t -> print_term stdout t; print_newline ()) ground_terms;
          print_endline "\nsubst_maps:";
          List.iter print_subst_map subst_maps
        end
    | _ -> ()
    in*)
    (* generate instances of axiom *)
    List.fold_left (fun acc subst_map -> (*Axioms.mk_axiom2*) (subst subst_map f) :: acc) acc subst_maps
  in
  List.fold_left instantiate epr_axioms axioms
  
let instantiate_with_terms ?(force=false) local axioms classes =
    if !Config.instantiate || force then
      (* remove atoms from congruence classes *)
      let classes = List.filter (function t :: _ -> sort_of t <> Bool | _ -> false) classes in
      let _ = 
        if Debug.is_debug 1 then
          ignore
            (List.fold_left (fun num cl ->
              print_string ("Class " ^ string_of_int num ^ ": ");
              List.iter (fun t -> print_string (string_of_term t ^ ", ")) cl; 
              print_newline ();
              num + 1) 1 classes)
      in
      let type_graph = TypeStrat.get () in
      (* choose representatives for instantiation *)
      let reps_f, egraph = choose_rep_terms classes in
      let instances_f = generate_instances local axioms reps_f egraph type_graph in
      instances_f
    else
      axioms

