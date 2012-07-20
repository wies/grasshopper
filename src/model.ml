open Util
open Form

type output_sort = 
    Int of int 
  | Bool of bool
	
type def = { input : int list;
	     output : output_sort}
type model = def list IdMap.t
  
let empty : model = IdMap.empty

let add_def id (i, o) model = 
  let defs = 
    try IdMap.find id model
    with Not_found -> []
  in
  IdMap.add id ({input=i; output=o} :: defs) model 
    
let filter_defs p model =
  IdMap.fold 
    (fun id defs fmodel ->
      match List.filter (p id) defs with
      | [] -> fmodel
      | fdefs -> IdMap.add id defs fmodel)
    model IdMap.empty

let fold f model init = 
  IdMap.fold 
    (fun id defs acc ->
      List.fold_left (fun acc def -> f id def acc) acc defs)
    model init
    
let const_map m =
  let consts = 
    IdMap.fold 
      (fun id defs acc ->
	match defs with
	| [def] when def.input = [] -> 
	    (match def.output with
	    | Int o -> IntMap.add o id acc
	    | _ -> acc)
	| _ -> acc)
      m IntMap.empty
  in
  IdMap.fold 
    (fun id defs acc ->
      List.fold_left (fun acc def ->
	List.fold_left (fun acc i ->
	  if IntMap.mem i acc then acc
	  else IntMap.add i (fresh_ident "c") acc)
	  acc def.input)
	acc defs)
    m consts
    
let to_clauses model =
  let const_map = const_map model in 
  let mk_rep n = mk_const (IntMap.find n const_map) in
  let constants = IntMap.fold (fun n _ acc -> mk_rep n :: acc) const_map [] in
  let form_of_def id def = 
    match def.output with
    | Bool b -> 
	let a = mk_pred id (List.map mk_rep def.input) in
	if b then a else mk_not a
    | Int out ->
	let rhs = mk_rep out in
	let lhs =
	  match def.input with
	  | [] -> mk_const id
	  | reps -> mk_app id (List.map mk_rep reps)
	in mk_eq lhs rhs
  in
  let def_forms =
    IdMap.fold 
      (fun id defs acc ->
	List.fold_left (fun acc def -> form_of_def id def :: acc) acc defs)
      model []
  in
  let diseqs = List.fold_left (fun acc c1 -> 
    List.fold_left (fun acc c2 ->
      if c1 = c2 then acc else [mk_not (mk_eq c1 c2)] :: acc) acc constants) 
      [] constants
  in
  diseqs @ List.map (fun f -> [f]) def_forms
	     
let to_form model = Clauses.to_form (to_clauses model)

let print_model model =
  print_form stdout (to_form model)
    
let print_model2 model =
  IdMap.iter
    (fun id defs ->
      print_string (str_of_ident id ^ " = ");
      match defs with
      | [def] when List.length def.input = 0 -> 
	  (match def.output with
	  | Int out -> Printf.printf " -> %d\n" out
	  | Bool out -> Printf.printf " -> %b\n" out)
      | _ ->
	  print_string "\n  [";
	  List.iter (fun def -> 
	    begin
	      match def.input with
	      | is -> 
		  Printf.printf "(%d" (List.hd is);
		  List.iter (Printf.printf ", %d") (List.tl is);
		  print_string ")"
	    end;
	    (match def.output with
	    | Int out -> Printf.printf " -> %d" out
	    | Bool out -> Printf.printf " -> %b" out);
	    print_string "\n   ")
	    defs;
	  print_string "]\n") model
    
let output_graphviz chan model =
  let output_flds () = 
    IdMap.iter 
      (fun id defs ->
	List.iter 
	  (fun def ->
	    match def.input with
	    | [i] ->
		(match def.output with
		| Int o -> Printf.fprintf chan "%d -> %d [label = %s]\n" i o (str_of_ident id) 
		| _ -> ())
	    | _ -> ())
	  defs) 
      model	
  in
  let output_reach () = 
    IdMap.iter 
      (fun id defs ->
	if not (Axioms.is_reach id) then () else
	let defs = List.map (fun def -> def.input) (List.filter (fun def -> def.output = Bool true) defs) in
	let reach = 
	  List.fold_left (fun acc -> function 
	    | [i11; i21; _] when i11 <> i21 ->
		if (List.for_all (function
		  | [i12; i22; i32] -> i11 <> i12 || i22 = i11 || 
		    List.exists (function
		      | [i13; i23; i33] ->
			  i11 = i13 && i23 = i21 && i33 = i32 
		      | _ -> false) defs
		  | _ -> true) defs)
		then IntMap.add i11 i21 acc
		else acc
	    | _ -> acc) IntMap.empty defs
	in
	IntMap.iter (fun i o -> Printf.fprintf chan "%d -> %d [label = %s, style=dashed]\n" i o (str_of_ident (Axioms.fun_of_reach id))) reach)
      model
  in
  let output_vars () = 
    IdMap.iter (fun id defs ->
      match defs with
      | [def] when List.length def.input = 0 ->
	  (match def.output with
	  | Int o -> 
	      Printf.fprintf chan "%s [shape=box]\n" (str_of_ident id);
	      Printf.fprintf chan "%s -> %d\n" (str_of_ident id) o 
	  | _ -> ())
      | _ -> ()) model
  in
  output_string chan "digraph Model {\n";
  output_vars ();
  output_reach ();
  output_flds ();
  output_string chan "}\n"
    
let eval_term model t = 
  let apply id args = 
    let defs = try IdMap.find id model with Not_found -> [] in
    try 
      let def = List.find (fun def -> def.input = args) defs in
      match def.output with
      | Int out -> out
      | Bool b -> failwith "expected Int"
    with Not_found -> begin
      match args with
      | [] -> failwith ("Model.class_of_term: constant " ^ str_of_ident id ^ " is undefined")
      | _ -> failwith ("Model.class_of_term: function " ^ str_of_ident id ^ " is not totally defined")
    end
  in 
  let rec eval = function
    | Var v -> failwith "Model.class_of_term: term is not ground"
    | Const id -> apply id []
    | FunApp (id, ts) ->
	let args = List.map eval ts in
	apply id args
  in try Some (eval t) with _ -> None
      
let prune model terms =
  fold (fun id def sm -> 
    let keep_def = 
      match def.input, def.output with
      | _ :: _ as inputs, Int _ -> 
	  TermSet.exists (function 
	    | FunApp (id', ts) when id = id' -> 
		List.fold_left2 
		  (fun acc t i -> acc && 
		    (match eval_term model t with
		    | Some i' -> i = i'
		    | None -> false))
		  true ts inputs
	    | _ -> false) terms
      | _ :: _ as inputs, Bool _ ->
	  List.for_all 
	    (fun i -> 
	      TermSet.exists 
		(fun t -> 
		  match eval_term model t with
		  | Some i' -> i = i'
		  | None -> false)
		terms)
	    inputs
      | _ -> true
    in
    if keep_def then add_def id (def.input, def.output) sm else sm)
    model empty
