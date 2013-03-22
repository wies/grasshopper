open Util
open Form
open FormUtil
open Axioms

  
let choose_rep_terms classes =
  let find_rep cl = 
    try List.find (function App (_, [], _) -> true | _ -> false) cl
    with Not_found -> 
      match cl with
      |	t :: _ -> t
      |	[] -> raise Not_found
  in
  let list_to_set cl =
    List.fold_left (fun acc t -> TermSet.add t acc) TermSet.empty cl
  in
  List.fold_left (fun (reps, new_classes) cl ->
    let cl_rep : term = find_rep cl in
    (cl_rep :: reps, TermMap.add cl_rep (list_to_set cl) new_classes))
    ([], TermMap.empty) classes

let generate_instances useLocalInst axioms terms rep_map = 
  let ground_terms = 
    TermMap.fold (fun _ -> TermSet.union) rep_map TermSet.empty 
  in
  let epr_axioms, axioms = 
    List.partition 
      (fun f -> useLocalInst && IdSrtSet.is_empty (vars_in_fun_terms f)) 
      axioms
  in
  (*let _ = print_endline "Candidate axioms for instantiation:" in
    let _ = print_forms stdout axioms in*)
  let instantiate acc f =
    let fvars =
      let fvars0 = sorted_free_vars f in
      if useLocalInst 
      then IdSrtSet.inter fvars0 (vars_in_fun_terms f)
      else fvars0
    in
    let fun_terms = 
      let rec tt bv terms t =
        match t with  
        | App (_, _, Some srt) when srt <> Bool -> 
            let vs = IdSet.diff (fvt IdSet.empty t) bv in
            if IdSet.is_empty vs
            then terms 
            else (vs, t) :: terms
        | App (fn, ts, _) -> List.fold_left (tt bv) terms ts
        | _ -> terms
      in fold_terms_with_bound tt [] f
    in
    let is_local subst_map = 
      List.for_all 
        (fun (_, t) ->
          match t with
          | App (fn1, ts1, _) ->
              TermSet.exists
                (function
                  | App (fn2, ts2, _) when fn1 = fn2 ->
                      List.for_all2
                        (fun t1 t2 ->
                          let t1_rep =
                            match t1 with
                            | Var (v, _) ->
                                (try TermMap.find (IdMap.find v subst_map) rep_map
                                with Not_found -> TermSet.singleton t2)
                            | _ -> 
                                try TermMap.find t1 rep_map
                                with Not_found -> TermSet.singleton t1
                          in TermSet.mem t2 t1_rep
                        ) ts1 ts2
                  | t -> false)
                ground_terms
          | _ -> true) 
        fun_terms
    in
    (*let _ = print_endline "Axiom:" in
    let _ = print_forms stdout [f] in
    let _ = print_endline "fun_terms:" in
    let _ = List.iter (fun (_, t) -> print_term stdout t; print_string ", ") fun_terms in*)
    let subst_maps = 
      IdSrtSet.fold 
        (fun (v, srt) subst_maps ->
          List.fold_left 
            (fun acc t -> match t with
            | App (_, _, Some srt2) 
            | Var (_, Some srt2) when srt2 = srt ->
                let new_subst_maps = 
                  List.fold_left 
                    (fun acc sub ->
                      let new_sub = IdMap.add v t sub in
                      if not useLocalInst || is_local new_sub 
                      then new_sub :: acc
                      else acc
                    ) acc subst_maps
                in
                new_subst_maps
            | _ -> acc)
            [] terms
        ) fvars [IdMap.empty]
    in
    List.fold_left (fun acc subst_map -> subst subst_map f :: acc) acc subst_maps
  in
  List.fold_left instantiate epr_axioms axioms
  

let instantiate_with_terms local axioms classes =
    if !Config.instantiate then
      let _ = 
        if !Debug.verbose then
          ignore
            (List.fold_left (fun num cl ->
              print_string ("Class " ^ string_of_int num ^ ": ");
              List.iter (fun t -> print_string (string_of_term t ^ ", ")) cl; 
              print_newline ();
              num + 1) 1 classes)
      in
      let reps_f, rep_map_f = choose_rep_terms classes in
      let instances_f = generate_instances local axioms reps_f rep_map_f in
      instances_f
    else
      axioms

