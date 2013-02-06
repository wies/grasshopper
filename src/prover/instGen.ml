open Util
open Form
open Axioms


let congr_classes fs gterms =
  let cc_graph = new CongruenceClosure.dag (TermSet.elements gterms) in
    List.iter
      (fun f -> match f with
	| Eq _ -> cc_graph#add_constr f
	| _ -> () )
      fs;
    cc_graph#get_cc

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
  let epr_axioms, axioms = 
    List.partition (fun f -> IdSet.is_empty (fv_in_fun_terms f)) axioms
  in
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
    if !Config.use_aggressive_inst || is_local then subst subst_map axiom :: acc else acc
  in
  let partitioned_axioms = 
    let add_class acc vars cl = 
      match cl with
      | [] -> acc
      | _ -> (vars, cl) :: acc
    in
    let fv_axioms = List.map (fun f -> (fv_in_fun_terms f, f)) axioms in
    let sorted = List.sort (fun (vars1, _) (vars2, _) -> IdSet.compare vars1 vars2) fv_axioms in
    let classes, vars, cl = 
      List.fold_left 
	(fun (acc, lvars, cl) (vars, f) ->
	  if lvars = vars then (acc, lvars, f :: cl)
	  else (add_class acc lvars cl, vars, [f]))
	([], IdSet.empty, []) sorted
    in add_class classes vars cl	  
  in
  let gen (vars, axioms) =
    (* let vars = IdSet.elements (fv (mk_and axioms)) in *)
    let subst_maps = 
      List.fold_left (fun subst_maps v ->
	let new_subst_maps = 
	  List.fold_left 
	    (fun acc t -> List.fold_left (fun acc s -> (IdMap.add v t s) :: acc) acc subst_maps)
	    [] terms
	in new_subst_maps)
	[IdMap.empty] (IdSet.elements vars)
    in List.fold_left 
      (fun instances subst_map -> List.fold_left (instantiate subst_map) instances axioms)
      [] subst_maps
  in
  epr_axioms @ rev_concat (List.rev_map gen partitioned_axioms)
  

let instantiate_with_terms fs gterms_f =
  let rec normalize acc = function
    | And fs :: gs -> normalize acc (fs @ gs)
    | f :: gs -> normalize (f :: acc) gs
    | [] -> List.rev acc
  in
  let normalized_fs = normalize [] fs in
  let axioms_f, ground_f = extract_axioms normalized_fs in
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

let get_ground_terms f =
  let g1 = ground_terms f in
  let is_unary id = not (Axioms.is_ep id) &&
                    not (Axioms.is_jp id) &&
                    not (Axioms.is_lb id)
  in
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

let instantiate fs =
  let gterms_f = get_ground_terms (mk_and fs) in
    instantiate_with_terms fs gterms_f

