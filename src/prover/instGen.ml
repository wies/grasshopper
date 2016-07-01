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
                let ts_reps =
                  List.map (fun t -> TermMap.find t rep_map) ts
                in
                let other_ts_reps =
                  try EGraph.find (t_rep, sym) egraph
                  with Not_found -> TermListSet.empty
                in
                EGraph.add (t_rep, sym) (TermListSet.add ts_reps other_ts_reps) egraph
              with Not_found ->
                egraph
            end
        | _ -> egraph)
      EGraph.empty (List.concat classes)
  in reps, egraph

let filter_term filters t sm = 
  List.for_all
    (fun f -> match f with
    | FilterNotNull ->
        (match t with
        | App (Null, [], _) -> false
        | _ -> true)
    | FilterSymbolNotOccurs sym ->
        let rec not_occurs = function
          | App (EntPnt, _, _) -> sym <> EntPnt
          | App (sym1, _, _) when sym1 = sym -> false
          | App (_, ts, _) -> List.for_all not_occurs ts
          | _ -> true
        in not_occurs t
    | FilterReadNotOccurs (name, (arg_srts, res_srt)) ->
        let rec not_occurs = function
          | App (EntPnt, _, _) -> true
          | App ((Read | ArrayCells), (App (FreeSym (name1, _), arg_ts, res_srt1) :: _ as ts), _) ->
              let ok =
                try
                  name1 <> name ||
                  res_srt1 <> res_srt ||
                  List.fold_left2 (fun acc t1 srt -> acc || sort_of t1 <> srt) false arg_ts arg_srts
                with Invalid_argument _ -> true
              in ok && List.for_all not_occurs ts
          | App (_, ts, _) -> List.for_all not_occurs ts
          | _ -> true
        in not_occurs t
    | FilterGeneric fn -> fn sm t
    )
    filters

    
let ematch filters t rep_terms egraph subst_maps =
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
    (*print_endline ("matching " ^ string_of_term t1 ^ " with " ^ string_of_term t2);*)
    match t1 with 
    | App (sym1, ts1, srt1) when srt1 = sort_of t2 ->
        begin
          try
            let ts2s = EGraph.find (t2, sym1) egraph in
            ematches ts1 ts2s subst_maps
          with Not_found -> 
            (*print_endline "fail 1";*)
            []
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
    | _ ->
        (*print_string (string_of_sort (sort_of t1) ^ " " ^ string_of_sort (sort_of t2) ^ " fail 2");*)
        []
  in
  let terms = 
    TermSet.fold 
      (fun t terms -> TermListSet.add [t] terms) 
      rep_terms TermListSet.empty 
  in
  let subst_maps1 = ematches [t] terms subst_maps in
  List.filter (fun sm -> filter_term filters (subst_term sm t) sm) subst_maps1 

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
    if is_ground_term t1 then
      if TermSet.mem t1 candidates then [t1, sm] else [] 
    else 
      let rec mt sm t1 t2 =
      match t1, t2 with 
      | App (sym1, ts1, srt1), App (sym2, ts2, srt2) 
        when sym1 = sym2 && srt1 = srt2 && List.length ts1 = List.length ts2 ->
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
      | _, _ ->
          (*Printf.printf "%s != %s\n" (string_of_term t1) (string_of_term t2);
          Printf.printf "%s != %s\n" (string_of_sort (sort_of t1)) (string_of_sort (sort_of t2));*)
          None
    in
    TermSet.fold (fun t2 subst_maps ->
      match mt sm t1 t2 with
      | None ->
          (*Printf.printf "Failed to match %s and %s\n" (string_of_term t1) (string_of_term t2);*)
          subst_maps
      | Some sm ->
          (*Printf.printf "Succeeded to match %s and %s\n" (string_of_term t1) (string_of_term t2);*)
          (t2, sm) :: subst_maps)
      candidates []
  in
  let rec generate round new_terms old_terms = function
    | (guards, gen_terms) :: generators1 ->
        (*
        print_endline "======";
        List.iter (fun t -> print_endline ("  generator: " ^ string_of_term t)) gen_terms;
        *)
        let subst_maps =
          List.fold_left (fun subst_maps -> function Match (t, filters) -> 
            (*
            print_endline ("  matching " ^ (string_of_term t));
            List.iter (fun f -> print_endline ("    subject to " ^ (string_of_filter f))) filters;
            *)
            let new_subst_maps =
              List.fold_left 
                (fun new_subst_maps sm ->
                  let matches = find_matches new_terms (subst_term sm t) sm in
                  Util.filter_rev_map 
                    (fun (t_matched, sm) -> filter_term filters t_matched sm)
                    (fun (t_matched, sm) -> sm)
                    matches |>
                  fun new_matches -> List.rev_append new_matches new_subst_maps
                ) [] subst_maps 
            in
            new_subst_maps)
            [IdMap.empty] guards
        in
        let new_terms1 =
          List.fold_left
            (fun acc sm ->
              List.fold_left
                (fun acc gen_term ->
                  let t = subst_term sm gen_term in
                  (*let _ = print_endline ("  Adding generated term " ^ string_of_term t) in *)
                  add_terms acc t)
                acc gen_terms
            )
            new_terms subst_maps
        in
        generate round new_terms1 old_terms generators1
    | [] -> 
        if round < !Config.term_gen_max_rounds && new_terms <> old_terms 
        then generate (round + 1) new_terms new_terms generators
        else new_terms
  in
  generate 0 new_terms ground_terms generators


let generate_instances stratify useLocalInst axioms rep_terms egraph = 
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
    (* filter out stratified variables *)
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
        if stratify && useLocalInst then
          IdSrtSet.partition
            (fun (id, srt) ->
              try
                let generating = IdMap.find id gen_map in
                  not (List.for_all (TypeStrat.is_stratified srt) generating)
              with Not_found ->
                begin
                  Debug.warn (fun () -> "BUG in stratification: " ^ (string_of_ident id) ^ "\n");
                  true
                end
            )
            fvars
        else fvars, IdSrtSet.empty
    in
    let strat_var_ids = IdSrtSet.fold (fun (id, _) acc -> IdSet.add id acc) strat_vars IdSet.empty in 
    (* collect all terms in which free variables appear below function symbols *)
    let fun_terms, fun_vars, strat_terms = 
      if not useLocalInst then TermSet.empty, IdSet.empty, TermSet.empty else
      let rec tt (fun_terms, fun_vars, strat_terms) t =
        match t with
        | App (sym, _ :: _, srt) when srt <> Bool ->
            let tvs = fv_term t in
            if IdSet.is_empty tvs then
              fun_terms, fun_vars, strat_terms
            else if IdSet.is_empty (IdSet.inter strat_var_ids tvs)
            then TermSet.add t fun_terms, IdSet.union tvs fun_vars, strat_terms
            else fun_terms, fun_vars, TermSet.add t strat_terms
        | App (_, ts, _) ->
            List.fold_left tt (fun_terms, fun_vars, strat_terms) ts
        | _ -> fun_terms, fun_vars, strat_terms
      in fold_terms tt (TermSet.empty, IdSet.empty, TermSet.empty) f
    in
    let unmatched_vars =
      IdSrtSet.fold (fun (id, _) acc ->
        if IdSet.mem id fun_vars then acc
        else IdSet.add id acc) fvars IdSet.empty
    in
    let fun_terms, fun_vars =
      TermSet.fold (fun t (fun_terms, fun_vars) ->
        let vs = fv_term t in
        if IdSet.is_empty (IdSet.inter unmatched_vars vs)
        then fun_terms, fun_vars
        else TermSet.add t fun_terms, IdSet.union vs fun_vars)
        strat_terms (fun_terms, fun_vars)
    in
    let strat_vars1 =
      IdSrtSet.filter (fun (id, _) -> not (IdSet.mem id fun_vars)) strat_vars
    in
    (* extract patterns separately to obtain auxilary filters *)
    let patterns = extract_patterns f in
    let fun_terms_with_filters =
      TermSet.fold (fun t acc ->
        try (t, List.assoc t patterns) :: acc
        with Not_found -> (t, []) :: acc)
        fun_terms []
    in
    let fun_terms_with_filters =
      List.sort (fun (t1, _) (t2, _) ->
        - (compare
             (IdSet.cardinal (fv_term t1))
             (IdSet.cardinal (fv_term t2))))
        fun_terms_with_filters
    in
    (* close the strat_vars so they are not instantiated *)
    let f = mk_forall (IdSrtSet.elements strat_vars1) f in
    (* generate substitution maps *)
    let subst_maps () =
      (* generate substitution maps for variables that appear below function symbols *)
      let proto_subst_maps =
        List.fold_left
          (fun subst_maps (t, fs) ->
            (*print_endline ("Matching term " ^ string_of_term t);*)
            let subst_maps1 = ematch fs t rep_terms egraph subst_maps in
            (*List.iter print_subst_map subst_maps1;*)
            subst_maps1
          )
          [IdMap.empty] fun_terms_with_filters 
      in
      (* complete substitution maps for remaining variables *)
      IdSrtSet.fold 
        (fun (v, srt) subst_maps -> 
          if IdSet.mem v fun_vars
          then subst_maps
          else ematch [] (Var (v, srt)) rep_terms egraph subst_maps)
        fvars proto_subst_maps         
    in
    let subst_maps = (*measure*) subst_maps () in
    let _ = if Debug.is_debug 1 then
      begin
        print_endline "--------------------";
        print_endline (string_of_form f);
        print_string "all vars: ";
        print_endline (String.concat ", " (List.map string_of_ident (List.map fst (IdSrtSet.elements fvars0))));
        print_string "strat vars: ";
        print_endline (String.concat ", " (List.map string_of_ident (List.map fst (IdSrtSet.elements strat_vars1))));
        print_string "unmatched vars: ";
        print_endline (String.concat ", " (List.map string_of_ident (IdSet.elements unmatched_vars)));
        print_string "inst vars: ";
        print_endline (String.concat ", " (List.map string_of_ident (IdSet.elements fun_vars)));
        print_string "fun terms: ";
        print_endline (String.concat ", " (List.map string_of_term (List.map fst fun_terms_with_filters)));
        Printf.printf "# of insts: %d\n" (List.length subst_maps);
        print_endline "subst_maps:";
        List.iter print_subst_map subst_maps;
        print_endline "--------------------"
      end
    in
    (* generate instances of axiom *)
    List.fold_left
      (fun acc subst_map -> (subst subst_map f) :: acc) acc subst_maps
  in
  List.fold_left instantiate epr_axioms axioms
  
let instantiate_with_terms ?(force=false) ?(stratify=(!Config.stratify)) local axioms classes =
    if !Config.instantiate || force then
      (* remove theory atoms from congruence classes *)
      let filter_term t =
        sort_of t <> Bool ||
        Opt.get_or_else false
          (Opt.map
             (((=) Frame) |||
             is_free_symbol |||
             ((=) (BoolConst true)) |||
             ((=) (BoolConst false)))
             (symbol_of t))
      in
      let classes =
        let classes2 = List.map (List.filter filter_term) classes in
        List.filter (fun x -> x <> []) classes2
      in
      let _ = 
        if Debug.is_debug 1 then
          ignore
            (List.fold_left (fun num cl ->
              print_endline ("Class " ^ string_of_int num ^ ": " ^ (string_of_sort (sort_of (List.hd cl))));
              List.iter (fun t -> print_endline ("    " ^ (string_of_term t))) cl; 
              print_newline ();
              num + 1) 1 (List.sort compare classes))
      in
      (* choose representatives for instantiation *)
      let reps_f, egraph = choose_rep_terms classes in
      generate_instances stratify local axioms reps_f egraph
        else
          axioms
            
