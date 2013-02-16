open Util
open Form
open FormUtil


type def = { input : symbol list;
	     output : symbol}

type interpretation = def list SymbolMap.t

type model = {sign: signature; interp: interpretation}

let empty : model = {sign = SymbolMap.empty; interp = SymbolMap.empty}

let get_sig m = m.sign

let get_interp m = m.interp

let add_def sym (i, o) model = 
  let defs = 
    try SymbolMap.find sym model.interp
    with Not_found -> []
  in
  {model with interp = SymbolMap.add sym ({input=i; output=o} :: defs) model.interp}

let add_decl sym arity model =
  {model with sign = SymbolMap.add sym arity model.sign}

let decl_of sym model = SymbolMap.find sym model.sign

let defs_of sym model = 
  try SymbolMap.find sym model.interp with Not_found -> [] 


let filter_defs p model =
  SymbolMap.fold 
    (fun id defs fmodel ->
      match List.filter (p id) defs with
      | [] -> fmodel
      | fdefs -> SymbolMap.add id defs fmodel)
    model.interp SymbolMap.empty

let fold f model init = 
  SymbolMap.fold 
    (fun id defs acc ->
      List.fold_left (fun acc def -> f id def acc) acc defs)
    model.interp init
    
let const_map m =
  let consts = 
    SymbolMap.fold 
      (fun id defs acc ->
	match defs with
	| [def] when def.input = [] -> 
	    SymbolMap.add def.output id acc
	| _ -> acc)
      m.interp SymbolMap.empty
  in
  SymbolMap.fold 
    (fun id defs acc ->
      List.fold_left (fun acc def ->
	List.fold_left (fun acc i ->
	  if SymbolMap.mem i acc then acc
	  else SymbolMap.add i (FreeSym (fresh_ident "c")) acc)
	  acc def.input)
	acc defs)
    m.interp consts
    
let to_clauses model =
  let const_map = const_map model in 
  let mk_rep n = mk_const (SymbolMap.find n const_map) in
  let constants = SymbolMap.fold (fun n _ acc -> mk_rep n :: acc) const_map [] in
  let form_of_def sym def = 
    match def.output with
    | BoolConst b -> 
	let a = mk_atom sym (List.map mk_rep def.input) in
	if b then a else mk_not a
    | o ->
	let rhs = mk_rep o in
	let lhs = mk_app sym (List.map mk_rep def.input)
	in mk_eq lhs rhs
  in
  let def_forms =
    SymbolMap.fold 
      (fun id defs acc ->
	List.fold_left (fun acc def -> form_of_def id def :: acc) acc defs)
      model.interp []
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
  SymbolMap.iter
    (fun sym defs ->
      print_string (str_of_symbol sym ^ " = ");
      match defs with
      | [def] when List.length def.input = 0 -> 
	  Printf.printf " -> %s\n" (str_of_symbol def.output)
      | _ ->
	  print_string "\n  [";
	  List.iter (fun def -> 
	    begin
	      match def.input with
	      | is -> 
		  Printf.printf "(%s" (str_of_symbol (List.hd is));
		  List.iter (fun i -> Printf.printf ", %s" (str_of_symbol i)) (List.tl is);
		  print_string ")"
	    end;
	    Printf.printf " -> %s" (str_of_symbol def.output);
	    print_string "\n   ")
	    defs;
	  print_string "]\n") model.interp
    
let output_graphviz chan model =
  let const_map = const_map model in 
  let output_flds () = 
    List.iter 
      (fun def ->
	match def.input with
	| [fld; i] ->
	    let fld_sym = SymbolMap.find fld const_map in
	    Printf.fprintf chan "\"%s\" -> \"%s\" [label = \"%s\"]\n" 
	      (str_of_symbol i) (str_of_symbol def.output) (str_of_symbol fld_sym) 
	| _ -> ()) 
      (defs_of Read model)
  in
  let output_reach () = 
    let defs  = 
      Util.filter_map 
	(fun def -> def.output = BoolConst true) 
	(fun def -> (List.hd def.input, List.tl def.input))
	(defs_of ReachWO model)
    in
    let grouped_defs = 
      List.fold_left 
	(fun groups (fld, def) -> 
	  let fld_defs = try SymbolMap.find fld groups with Not_found -> [] in
	  SymbolMap.add fld (def :: fld_defs) groups
	)
	SymbolMap.empty defs
    in
    let process_fld fld defs =
      let reach = 
	List.fold_left (fun acc -> function 
	  | [i11; i21; _] when i11 <> i21 ->
	      if (List.for_all (function
		| [i12; i22; i32] -> 
		    i11 <> i12 || i22 = i11 || 
		    List.exists (function
		      | [i13; i23; i33] ->
			  i11 = i13 && i23 = i21 && i33 = i32 
		      | _ -> false) defs
		  | _ -> true) defs)
	      then SymbolMap.add i11 i21 acc
	      else acc
	  | _ -> acc) SymbolMap.empty defs
      in
      let fld_sym = SymbolMap.find fld const_map in
      SymbolMap.iter 
	(fun i o -> 
	  Printf.fprintf chan "\"%s\" -> \"%s\" [label = \"%s\", style=dashed]\n" 
	    (str_of_symbol i) (str_of_symbol o) (str_of_symbol fld_sym)
	) 
	reach
    in
    SymbolMap.iter process_fld grouped_defs
  in
  let output_vars () = 
    SymbolMap.iter (fun sym defs ->
      match decl_of sym model with
      |	([], Loc) ->
	  Printf.fprintf chan "\"%s\" [shape=box]\n" (str_of_symbol sym);
	  Printf.fprintf chan "\"%s\" -> \"%s\"\n" (str_of_symbol sym) (str_of_symbol (List.hd defs).output)
      | _ -> ()) model.interp
  in
  output_string chan "digraph Model {\n";
  output_vars ();
  output_reach ();
  output_flds ();
  output_string chan "}\n"
    
let eval_term model t = 
  let apply id args = 
    let defs = try SymbolMap.find id model.interp with Not_found -> [] in
    try 
      let def = List.find (fun def -> def.input = args) defs in
      def.output 
    with Not_found -> begin
      match args with
      | [] -> failwith ("Model.class_of_term: constant " ^ str_of_symbol id ^ " is undefined")
      | _ -> failwith ("Model.class_of_term: function " ^ str_of_symbol id ^ " is not totally defined")
    end
  in 
  let rec eval = function
    | Var _ -> failwith "Model.class_of_term: term is not ground"
    | App (sym, ts, _) ->
	let args = List.map eval ts in
	apply sym args
  in try Some (eval t) with _ -> None
      
(* 
let prune m terms =
  fold (fun sym def sm -> 
    let keep_def = 
      match def.input, def.output with
      | _ :: _ as inputs, Int _ -> 
	  TermSet.exists (function 
	    | App (sym', ts, _) when sym = sym' -> 
		List.fold_left2 
		  (fun acc t i -> acc && 
		    (match eval_term m t with
		    | Some i' -> i = i'
		    | None -> false))
		  true ts inputs
	    | _ -> false) terms
      | _ :: _ as inputs, Bool _ ->
	  List.for_all 
	    (fun i -> 
	      TermSet.exists 
		(fun t -> 
		  match eval_term m t with
		  | Some i' -> i = i'
		  | None -> false)
		terms)
	    inputs
      | _ -> true
    in
    if keep_def then add_def sym (def.input, def.output) sm else sm)
    m empty
*)
