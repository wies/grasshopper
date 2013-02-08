open Util
open Form
open FormUtil
open Axioms

  
let congr_classes fs gterms inst_terms =
  let cc_graph = new CongruenceClosure.dag (TermSet.elements gterms) in
  List.iter
    (fun f -> match f with
    | Atom (App (Eq, _, _)) -> cc_graph#add_constr f
    | _ -> () )
    fs;
  List.filter (fun cc -> List.exists (fun t -> TermSet.mem t inst_terms) cc) cc_graph#get_cc

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
  List.fold_left (fun (reps, defs, new_classes) cl ->
    let cl_rep : term = find_rep cl in
    (cl_rep :: reps, defs, TermMap.add cl_rep (list_to_set cl) new_classes))
    ([], [], TermMap.empty) classes

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
  let instantiate subst_map acc axiom =
    let fun_terms = 
      let rec tt bv terms t =
        match t with  
        | App (fn, ts, Some srt) when srt <> Bool -> 
	    let has_var, vs = 
              List.fold_right 
                (fun t (has_var, vs) ->
                  match t with 
                  | Var (v, _) when not (IdSet.mem v bv) -> 
                      let rep_class = TermMap.find (IdMap.find v subst_map) rep_map in
                      true, Some rep_class :: vs
                  | _ -> has_var, None :: vs
                ) ts (false, [])
            in
            let new_terms = 
              if has_var 
              then ((vs, fn) :: terms)
              else terms
            in List.fold_left (tt bv) new_terms ts
        | App (fn, ts, _) -> List.fold_left (tt bv) terms ts
        | _ -> terms
      in fold_terms_with_bound tt [] axiom
    in
    let is_local () = 
      List.for_all 
        (fun (rep_classes, fn) ->
          (* let _ = print_endline ("Symbol: " ^ str_of_symbol fn) in *)
	  TermSet.exists 
	    (function 
	      | App (fn2, ts, _) when fn = fn2 -> 
		  List.for_all2 
		    (fun rep_class_opt t ->
                      match rep_class_opt with
                      | None -> true
                      | Some rep_class -> TermSet.mem t rep_class
                    ) rep_classes ts
              |	t -> false)
            ground_terms)
        fun_terms
    in
    if not useLocalInst || is_local ()
    then ((*print_endline "\nSubstituting in:"; 
	  print_form stdout axiom;
	  print_endline "\nwith substitution:";
	  IdMap.iter (fun id t -> print_endline (str_of_ident id ^ " -> " ^ string_of_term t)) subst_map;
	  print_endline "\nResult:";
	  print_form stdout (subst subst_map axiom);*)
	  subst subst_map axiom :: acc)
    else acc
  in
  let partitioned_axioms = 
    let add_class acc vars cl = 
      match cl with
      | [] -> acc
      | _ -> (vars, cl) :: acc
    in
    let fv_axioms = 
      List.map 
        (fun f -> 
          let fvars = sorted_free_vars f in
          if useLocalInst 
          then IdSrtSet.inter fvars (vars_in_fun_terms f), f
          else fvars, f) axioms 
    in
    let sorted = 
      List.sort 
        (fun (vars1, _) (vars2, _) -> IdSrtSet.compare vars1 vars2) 
        fv_axioms 
    in
    let classes, vars, cl = 
      List.fold_left 
        (fun (acc, lvars, cl) (vars, f) ->
          if lvars = vars then (acc, lvars, f :: cl)
          else (add_class acc lvars cl, vars, [f]))
        ([], IdSrtSet.empty, []) sorted
    in add_class classes vars cl	  
  in
  let gen (vars, axioms) =
    (* let vars = IdSet.elements (fv (mk_and axioms)) in *)
    let subst_maps = 
      IdSrtSet.fold (fun (v, srt) subst_maps ->
        let new_subst_maps = 
          List.fold_left 
            (fun acc t -> match t with
            | App (_, _, Some srt2) 
            | Var (_, Some srt2) when srt2 = srt ->
                List.fold_left (fun acc sub -> (IdMap.add v t sub) :: acc) acc subst_maps
            | _ -> acc)
            [] terms
        in new_subst_maps)
        vars [IdMap.empty]
    in List.fold_left 
      (fun instances subst_map -> List.fold_left (instantiate subst_map) instances axioms)
      [] subst_maps
  in
  epr_axioms @ rev_concat (List.rev_map gen partitioned_axioms)
  

let instantiate_with_terms local fs axioms inst_terms =
  let classes = congr_classes fs (ground_terms (smk_and fs)) inst_terms in
  let _ = 
    if !Debug.verbose then
      ignore
        (List.fold_left (fun num cl ->
          print_string ("Class " ^ string_of_int num ^ ": ");
          List.iter (fun t -> print_string (string_of_term t ^ ", ")) cl; 
          print_newline ();
          num + 1) 1 classes)
  in
  let reps_f, defs_f, rep_map_f = choose_rep_terms classes in
  let instances_f = generate_instances local axioms reps_f rep_map_f in
  defs_f, instances_f

(*
let get_ground_terms f =
  let g1 = ground_terms f in
  let unary_arg t = match t with
    | FunApp (id, [arg]) when is_unary id -> Some (id, arg)
    | _ -> None
  in
  let unaries = IdSet.filter is_unary (funs_only f) in
  let mk_unaries t = match unary_arg t with
    | Some (id, arg) ->
      IdSet.fold
        (fun id acc -> TermSet.add (mk_app id [arg]) acc)
        (IdSet.filter (fun id2 -> fst id = fst id2) unaries)
        TermSet.empty
    | None -> TermSet.empty
  in
  let g1 =
    TermSet.fold
      (fun t acc -> TermSet.union (mk_unaries t) acc)
      g1 g1
  in
    if !Config.sl_mode then
      begin
        let eps = Axioms.get_eps f in
        let mk_eps t =
	  (*match t with
	  | Const _ ->*)
	  IdSet.fold
            (fun ep acc -> TermSet.add (Axioms.ep ep t) acc)
            eps
            TermSet.empty
          (*| _ -> TermSet.empty*)
        in
          TermSet.fold
            (fun t acc -> TermSet.union (mk_eps t) acc)
            g1 g1
      end
    else g1
*)

let instantiate fs =
  let gterms_f = ground_terms (mk_and fs) in
  let defs, instances = instantiate_with_terms true fs fs gterms_f in
  defs @ fs @ instances

