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

let consts model =
  SymbolMap.fold 
    (fun id defs acc ->
      match defs with
      | [def] when def.input = [] -> SymbolSet.add id acc
      | _ -> acc)
    model.interp SymbolSet.empty
    
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

let eval_term model t = 
  let const_map = const_map model in 
  let apply sym args = 
    let defs = 
      try SymbolMap.find sym model.interp 
      with Not_found -> 
	try
	  let rep_sym = SymbolMap.find sym const_map in
	  SymbolMap.find rep_sym model.interp 
	with Not_found -> []
    in
    try 
      let def = List.find (fun def -> def.input = args) defs in
      def.output 
    with Not_found -> begin
      match args with
      | [] -> failwith ("Model.class_of_term: constant " ^ str_of_symbol sym ^ " is undefined")
      | _ -> failwith ("Model.class_of_term: function " ^ str_of_symbol sym ^ " is not totally defined")
    end
  in 
  let rec eval = function
    | Var _ -> failwith "Model.class_of_term: term is not ground"
    | App (sym, ts, _) ->
	let args = List.map eval ts in
	apply sym args
  in try Some (eval t) with _ ->  None

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
  let colors = ["blue"; "red"; "green"; "orange"; "darkviolet"] in
  let flds = 
    let read_flds = 
      List.fold_left 
	(fun flds def -> match def.input with
	| [fld; _] -> SymbolSet.add fld flds
	| _ -> flds)
	SymbolSet.empty (defs_of Read model)
    in
    List.fold_left 
      (fun flds def -> match def.input with
      | [fld; _; _; _] -> SymbolSet.add fld flds
      | _ -> flds)
      read_flds (defs_of Btwn model)
  in
  let fld_colors =
    Util.fold_left2 (fun acc fld color -> (fld, color)::acc) [] (SymbolSet.elements flds) colors
  in
  let get_label fld =
    let fld_sym = SymbolMap.find fld const_map in
    let color =
      try List.assoc fld fld_colors with Not_found -> "black"
    in
    Printf.sprintf "label=\"%s\", fontcolor=%s, color=%s" (str_of_symbol fld_sym) color color
  in
  let output_flds () = 
    List.iter 
      (fun def ->
	match def.input with
	| [fld; i] ->
	    let label = get_label fld in
	    Printf.fprintf chan "\"%s\" -> \"%s\" [%s]\n" 
	      (str_of_symbol i) (str_of_symbol def.output) label
	| _ -> ()) 
      (defs_of Read model)
  in
  let output_reach fld_colors = 
    let defs  = 
      Util.filter_map 
	(fun def -> def.output = BoolConst true) 
	(fun def -> (List.hd def.input, List.tl def.input))
	(defs_of Btwn model)
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
      let label = get_label fld in
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
      SymbolMap.iter 
	(fun i o -> 
	  match eval_term model (mk_read (mk_const fld) (mk_const i)) with
	  | Some o' when o = o' -> ()
	  | _ ->
	      Printf.fprintf chan "\"%s\" -> \"%s\" [%s, style=dashed]\n" 
		(str_of_symbol i) (str_of_symbol o) label
	) 
	reach
    in
    SymbolMap.iter process_fld grouped_defs
  in
  let output_vars () = 
    SymbolMap.iter (fun sym defs ->
      (*
      let decl = decl_of sym model in
      print_endline ((str_of_symbol sym) ^ " -> " ^
        (String.concat "," (List.map string_of_sort (fst decl))) ^
        ", " ^ (string_of_sort (snd decl)));
      *)
      match decl_of sym model with
      |	([], Loc) ->
	  Printf.fprintf chan "\"%s\" [shape=box]\n" (str_of_symbol sym);
	  Printf.fprintf chan "\"%s\" -> \"%s\"\n" (str_of_symbol sym) (str_of_symbol (List.hd defs).output)
      | _ -> ()) model.interp
  in
  let output_sets () =
    let print_sets () =
      (*TODO adapt for Elem*)
      let defs = defs_of Elem model in
      let csts = consts model in
      let sets =
        SymbolSet.filter
          (fun sym -> match decl_of sym model with ([], Set _) -> true | _ -> false)
          csts
      in
        SymbolSet.iter
          (fun set ->
            let set_value = Util.unopt (eval_term model (mk_const set)) in
            let set_defs = List.filter (fun def -> List.nth def.input 1 = set_value) defs in
            let in_set, not_in_set =
              List.partition
                (fun def -> match def.output with
                              BoolConst b -> b
                            | _ -> failwith "expected BoolConst _")
                set_defs
            in
            let in_set = List.map (fun d -> List.hd d.input) in_set in
            let not_in_set = List.map (fun d -> List.hd d.input) not_in_set in
            let in_set_rep = String.concat ", " (List.map str_of_symbol in_set) in
            let not_in_set_rep = String.concat ", " (List.map str_of_symbol not_in_set) in
              output_string chan "      <TR>\n";
              Printf.fprintf chan "        <TD>%s</TD><TD>%s</TD><TD>%s</TD>\n" (str_of_symbol set) in_set_rep not_in_set_rep;
              output_string chan "      </TR>\n"
          )
          sets
    in 
    (* table header *)
    output_string chan "{ rank = sink; Legend [shape=none, margin=0, label=<\n";
    output_string chan "    <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n";
    output_string chan "      <TR>\n";
    output_string chan "        <TD><B>Set</B></TD><TD><B>contains</B></TD><TD><B>excludes</B></TD>\n";
    output_string chan "      </TR>\n";
    (* print sets *)
    print_sets ();
    (* table footer *)
    output_string chan "</TABLE>\n";
    output_string chan ">];\n";
    output_string chan "}\n";

  in
  let output_graph () =
    output_string chan "digraph Model {\n";
    output_vars ();
    output_reach ();
    output_flds ();
    output_sets ();
    output_string chan "}\n"
  in
  output_graph ()
    

      
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
