open Util
open Form
open Axioms

let add_class acc cl = 
  match cl with
  | [] -> acc 
  | _ -> cl :: acc
  

let congr_classes fs gterms =
  let term_index_map, num = 
    TermSet.fold 
      (fun t (tmap, c) -> (TermMap.add t c tmap, c + 1)) 
      gterms (TermMap.empty, 0) 
  in
  let puf = 
    List.fold_left 
      (fun puf -> function 
	| Eq (t1, t2) -> 
	    let t1_index = TermMap.find t1 term_index_map in
	    let t2_index = TermMap.find t2 term_index_map in
	    Puf.union puf (Puf.find puf t1_index) (Puf.find puf t2_index)
	| _ -> puf)
      (Puf.create num) fs
  in
  let class_map = 
    TermSet.fold 
      (fun t acc ->
	let t_rep = Puf.find puf 
	    (TermMap.find t term_index_map) in
	let cl = try IntMap.find t_rep acc with Not_found -> [] in
	IntMap.add t_rep (t :: cl) acc)
      gterms IntMap.empty
  in
  IntMap.fold (fun _ cl acc -> cl :: acc) class_map []
    
  
  (* match Prover.get_model f with
  | Some m -> 
      let proto_classes = TermSet.fold (fun t acc -> (Model.eval_term m t, t) :: acc) gterms [] in
      let sorted_classes = 
	List.sort (fun (v1, _) (v2, _) -> compare v1 v2) proto_classes 
      in
      let classes, _, cl = 
	List.fold_left
	  (fun (acc, lv, cl) (v, t) ->
	    match v with
	    | None -> (add_class acc cl, v, [t])
	    | Some _ -> 
		if v = lv then (acc, v, t :: cl) 
		else (add_class acc cl, v, [t]))
	  ([], None, []) sorted_classes
      in
      add_class classes cl 
  | None -> 
      (* ground clauses are already unsatisfiable, no instantiation required *)
      [] 
  TermSet.fold (fun t acc -> [t]::acc) gterms [] *)



let choose_rep_terms_interp classes funs1 funs2 =
  let find_rep symbs cl = 
    let candidates = List.filter (fun t -> IdSet.subset (funs (mk_eq t t)) symbs) cl in
    try
      List.find (function Const _ -> true | _ -> false) candidates
    with Not_found -> 
      match candidates with
      |	t :: _ -> t
      |	[] -> raise Not_found
  in
  let list_to_set cl =
    List.fold_left (fun acc t -> TermSet.add t acc) TermSet.empty cl
  in
  List.fold_left (fun (reps, defs, new_classes) cl ->
    try
      let cl_rep : term = find_rep funs1 cl in
      (cl_rep :: reps, defs, TermMap.add cl_rep (list_to_set cl) new_classes)
    with Not_found ->
      let cl_rep = mk_const (fresh_ident "rep") in
      let cl_def = find_rep funs2 cl in
      (cl_rep :: reps, mk_eq cl_rep cl_def :: defs, TermMap.add cl_rep (list_to_set cl) new_classes))
      (* (reps, defs, TermMap.add cl_rep (list_to_set cl) new_classes)) *)
    ([], [], TermMap.empty) classes

let choose_rep_terms classes =
  let find_rep cl = 
    try List.find (function Const _ -> true | _ -> false) cl
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

let generate_instances axioms terms rep_map =
  let ground_terms = TermMap.fold (fun _ -> TermSet.union) rep_map TermSet.empty in
  let instantiate subst_map acc axiom =
    let fun_terms = 
      let rec tt terms t =
	match t with  
	| FunApp (fn, [Var v]) -> ([v], fn) :: terms
	| FunApp (fn, [Var v1; Var v2]) -> ([v1; v2], fn) :: terms
	| FunApp (_, ts) -> List.fold_left tt terms ts
	| _ -> terms
      in collect_from_terms tt [] axiom
    in
    let is_local = 
      List.for_all 
	(fun (vs, fn) ->
	  TermSet.exists 
	    (function 
	      | FunApp (fn2, ts) when fn = fn2 -> 
		  List.for_all2 (fun v t ->
		    let rep = IdMap.find v subst_map in
		    let rep_class = TermMap.find rep rep_map in
		    TermSet.mem t rep_class) vs ts
	      |	_ -> false)
	    ground_terms)
	fun_terms
    in
    if is_local then subst subst_map axiom :: acc else acc
  in
  let partitioned_axioms = 
    let fv_axioms = List.map (fun f -> (fv f, f)) axioms in
    let sorted = List.sort (fun (vars1, _) (vars2, _) -> IdSet.compare vars1 vars2) fv_axioms in
    let classes, _, cl = 
      List.fold_left 
	(fun (acc, lvars, cl) (vars, f) ->
	  if lvars = vars then (acc, lvars, f :: cl)
	  else (add_class acc cl, vars, [f]))
	([], IdSet.empty, []) sorted
    in add_class classes cl	  
  in
  let gen axioms =
    let vars = id_set_to_list (fv (mk_and axioms)) in
    let subst_maps = 
      List.fold_left (fun subst_maps v ->
	let new_subst_maps = 
	  List.fold_left 
	    (fun acc t -> List.rev_map (IdMap.add v t) subst_maps @ acc)
	    [] terms
	in new_subst_maps)
	[IdMap.empty] vars
    in List.fold_left 
      (fun instances subst_map -> List.fold_left (instantiate subst_map) instances axioms)
      [] subst_maps
  in
  List.concat (List.map gen partitioned_axioms)


let instantiate f =
  let axioms_f, ground_f = extract_axioms f in
  let gterms_f = ground_terms (mk_and f) in
  let classes = congr_classes ground_f gterms_f in
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
  let instances_f = generate_instances axioms_f reps_f rep_map_f in
  defs_f @ ground_f @ instances_f

let instantiate_interp pf_a pf_b =
  let a_axioms, a_ground = extract_axioms pf_a in
  let b_axioms, b_ground = extract_axioms pf_b in
  let gterms = ground_terms (mk_and (pf_a @ pf_b)) in
  let classes = 
    Debug.phase "Computing congruence classes" (congr_classes (a_ground @ b_ground))
      gterms 
  in
  let _ = 
    if !Debug.verbose then
      ignore
	(List.fold_left (fun num cl ->
	  print_string ("Class " ^ string_of_int num ^ ": ");
	  List.iter (fun t -> print_string (string_of_term t ^ ", ")) cl; 
	  print_newline ();
	  num + 1) 1 classes)
  in
  let funs_a = funs (mk_and pf_a) in
  let funs_b = funs (mk_and pf_b) in
  let a_reps, b_defs, a_rep_map = choose_rep_terms_interp classes funs_a funs_b in
  let b_reps, a_defs, b_rep_map = choose_rep_terms_interp classes funs_b funs_a in
  let a_instances, b_instances = 
    Debug.phase "Generating instances" (fun () ->
      let a_instances = generate_instances a_axioms a_reps a_rep_map in
      let b_instances = generate_instances b_axioms b_reps b_rep_map in
      a_instances, b_instances) ()
  in
  a_defs @ a_ground @ a_instances, b_defs @ b_ground @ b_instances
