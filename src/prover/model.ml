open Util
open Form
open FormUtil

exception Undefined

type base_value =
  | I of int
  | B of bool

module ValueMap = 
  Map.Make(struct
    type t = base_value list
    let compare = compare
  end)

module ValueSet = 
  Set.Make(struct
    type t = base_value
    let compare = compare
  end)

type value =
  | BaseVal of base_value
  | MapVal of base_value ValueMap.t * value
  | SetVal of ValueSet.t
  | TermVal of (ident * sort) list * term
  | Undef

let value_of_int i = BaseVal (I i)

let value_of_bool b = BaseVal (B b)

let value_of_set s = SetVal s

let equal v1 v2 =
  match v1, v2 with
  | SetVal s1, SetVal s2 ->
      ValueSet.equal s1 s2
  | _, _ -> v1 = v2

type interpretation = value SymbolMap.t

type model =
  { sign: signature; 
    card: int SortMap.t;
    intp: interpretation }

let empty : model = 
  { sign = SymbolMap.empty;
    card = SortMap.empty;
    intp = SymbolMap.empty }

let get_sign m = m.sign

let get_intp m = m.intp

let add_card model srt card = 
  { model with card = SortMap.add srt card model.card }

let add_decl model sym sort =
  { sign = SymbolMap.add sym sort model.sign;
    card = model.card;
    intp = SymbolMap.add sym Undef model.intp
  }

let add_interp model sym def =
  { model with intp = SymbolMap.add sym def model.intp }

let fun_write funv args res =
  let old_m, old_d = match funv with
  | MapVal (m, d) -> m, d
  | v -> ValueMap.empty, v
  in 
  MapVal (ValueMap.add args res old_m, old_d)

let get_base_value = function
  | BaseVal v -> v
  | _ -> raise Undefined

let interp model sym = 
  try SymbolMap.find sym model.intp 
  with Not_found -> raise Undefined

let interp_base model sym =
  get_base_value (interp model sym)

let rec eval model = function
  | Var (id, _) -> interp model (FreeSym id)
  | App (IntConst i, [], _) -> value_of_int i
  | App (BoolConst b, [], _) -> value_of_bool b
  | App (Read, [fld; ind], _) -> 
      fun_read model (eval model fld) [eval_base model ind]
  | App (Write, [fld; ind; upd], _) ->
      let indv = eval_base model ind in
      let updv = eval_base model upd in
      let fldv = eval model fld in
      fun_write fldv [indv] updv 
  | App (EntPnt, [fld; loc], _) -> raise Undefined (* todo *)
  | App (UMinus, [t], _) ->
      value_of_int (-(eval_int model t))
  | App (Plus as intop, [t1; t2], _)
  | App (Minus as intop, [t1; t2], _)
  | App (Mult as intop, [t1; t2], _)
  | App (Div as intop, [t1; t2], _) ->
      let f = match intop with
      | Plus -> (+)
      | Minus -> (-)
      | Mult -> ( * )
      | Div -> (/)
      | _ -> failwith "impossible"
      in value_of_int (f (eval_int model t1) (eval_int model t2))
  | App (Empty, [], _) -> value_of_set ValueSet.empty
  | App (SetEnum, ts, _) ->
      let s = 
        List.fold_left 
          (fun res t -> ValueSet.add (eval_base model t) res) 
          ValueSet.empty ts
      in value_of_set s
  | App (Union, ts, _) ->
      let s = 
        List.fold_left
          (fun res t -> ValueSet.union res (eval_set model t)) 
          ValueSet.empty ts
      in value_of_set s
  | App (Diff, [t1; t2], _) ->
      let s = 
        ValueSet.diff (eval_set model t1) (eval_set model t2)
      in value_of_set s
  | App (Eq, [t1; t2], _) ->
      value_of_bool (equal (eval model t1) (eval model t2))
  | App (LtEq as rel, [t1; t2], _)
  | App (GtEq as rel, [t1; t2], _)
  | App (Lt as rel, [t1; t2], _)
  | App (Gt as rel, [t1; t2], _) ->
      let r = match rel with
      | LtEq -> (<=) | GtEq -> (>=) | Lt -> (<) | Gt -> (>)
      | _ -> failwith "impossible"
      in 
      value_of_bool (r (eval_int model t1) (eval_int model t2))
  | App (Elem, [e; s], _) ->
      let ev = eval_base model e in
      let sv = eval_set model s in
      value_of_bool (ValueSet.mem ev sv)
  | App (SubsetEq, [s1; s2], _) ->
      let s1v = eval_set model s1 in
      let s2v = eval_set model s2 in
      value_of_bool (ValueSet.subset s1v s2v)
  | App (sym, [], _) -> 
      interp model sym
  | App (sym, ts, _) ->
      let args = List.map (eval_base model) ts in
      fun_read model (interp model sym) args
      
and fun_read model funv args =
  let rec fr = function
    | MapVal (m, d) ->
        (try BaseVal (ValueMap.find args m) with Not_found -> fr d)
    | TermVal (ids, t) ->
        let model1 = 
          List.fold_left2 
            (fun model1 (id, srt) arg -> 
              let m1 = add_decl model1 (FreeSym id) ([], srt) in
              add_interp m1 (FreeSym id) (BaseVal arg))
            model ids args
        in eval model1 t
    | v -> v
  in
  fr funv

and eval_base model t =
  get_base_value (eval model t)

and eval_int model t =
  match eval_base model t with
  | I i -> i
  | _ -> raise Undefined

and eval_bool model t =
  match eval_base model t with
  | B b -> b
  | _ -> raise Undefined

and eval_set model t =
  match eval model t with
  | SetVal s -> s
  | _ -> raise Undefined


let symbols_of_sort model srt =
  SymbolMap.fold 
    (fun id osrt acc ->
      if srt = osrt then SymbolSet.add id acc
      else acc)
    model.sign SymbolSet.empty
       
let output_graphviz chan model = ()
 
(*
let output_graphviz chan model =
  let const_map = const_map model in 
  let find_rep s = match s with
    | BoolConst _ | IntConst _ -> s
    | _ -> try SymbolMap.find s const_map with Not_found -> s
  in
  let colors1 = ["blue"; "red"; "green"; "orange"; "darkviolet"] in
  let colors2 = ["blueviolet"; "crimson"; "olivedrab"; "orangered"; "purple"] in
  let flds = values_of_tpe (Fld Loc) model in
  let fld_colors =
    Util.fold_left2 (fun acc fld color -> (fld, color)::acc) [] (SymbolSet.elements flds) colors1
  in
  let ep_colors =
    Util.fold_left2 (fun acc fld color -> (fld, color)::acc) [] (SymbolSet.elements flds) colors2
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
	| [fld; i] when SymbolSet.mem fld flds && SymbolMap.find i const_map <> Null ->
	    let label = get_label fld in
	    Printf.fprintf chan "\"%s\" -> \"%s\" [%s]\n" 
	      (str_of_symbol i) (str_of_symbol def.output) label
	| _ -> ()) 
      (defs_of Read model)
  in
  let output_reach () = 
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
  let output_eps () =
    List.iter
      (fun def ->
        let fld = List.hd def.input in
        let color = try List.assoc fld ep_colors with Not_found -> "black" in
        let label =
          let fld = find_rep fld in
          let set = find_rep (List.nth def.input 1) in
            "ep(" ^ (str_of_symbol fld) ^ ", " ^ (str_of_symbol set) ^ ")"
        in
        let i = List.nth def.input 2 in
        let o = def.output in
	  Printf.fprintf chan
            "\"%s\" -> \"%s\" [label=\"%s\", fontcolor=%s, color=%s, style=dotted]\n"
            (str_of_symbol i) (str_of_symbol o) label color color
      )
      (defs_of EntPnt model)
  in
  let output_locs () =
    let read = defs_of Read model in
    let eval fld loc =
      try Some (List.find (fun def -> def.input = [fld; loc]) read).output
      with Not_found -> None
    in
    let locs = values_of_tpe Loc model in
    let data_field = SymbolSet.union (values_of_tpe (Fld Int) model) (values_of_tpe (Fld Bool) model) in
      SymbolSet.iter
        (fun loc ->
          Printf.fprintf chan "  \"%s\" [shape=none, margin=0, label=<\n" (str_of_symbol loc);
          output_string chan "    <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n";
          Printf.fprintf chan "      <TR><TD><B>%s</B></TD></TR>\n" (str_of_symbol loc);
          SymbolSet.iter
            (fun fld ->
              let fld_str = str_of_symbol (find_rep fld) in
                match eval fld loc with
                | Some v -> Printf.fprintf chan "      <TR><TD><B>%s = %s</B></TD></TR>\n" fld_str (str_of_symbol v)
                | None -> ()
            )
            data_field;
          output_string chan "</TABLE>\n";
          output_string chan ">];\n"
        )
        locs
  in
  let output_loc_vars () = 
    SymbolMap.iter (fun sym defs ->
      (*
      let decl = decl_of sym model in
      print_endline ((str_of_symbol sym) ^ " -> " ^
        (String.concat "," (List.map string_of_sort (fst decl))) ^
        ", " ^ (string_of_sort (snd decl)));
      *)
      match decl_of sym model with
      |	([], Loc) ->
	  (*Printf.fprintf chan "\"%s\" [shape=box]\n" (str_of_symbol sym);*)
	  Printf.fprintf chan "\"%s\" -> \"%s\"\n" (str_of_symbol sym) (str_of_symbol (List.hd defs).output)
      | _ -> ()) model.interp
  in
  let l = ref 0 in
  let print_table_header title =
    l := !l + 1;
    output_string chan ("{ rank = sink; Legend"^(string_of_int !l)^" [shape=none, margin=0, label=<\n");
    output_string chan "    <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n";
    output_string chan "      <TR>\n";
    output_string chan ("        <TD><B>"^title^"</B></TD>\n");
    output_string chan "      </TR>\n";
  in
  let print_table_footer () =
    output_string chan "</TABLE>\n";
    output_string chan ">];\n";
    output_string chan "}\n";
  in
  let output_int_vars () = 
   let has_int =
     SymbolMap.exists (fun sym defs ->
        match decl_of sym model with
        | ([], Int) -> true
        | _ -> false) model.interp
  in
    let print_ints () =
      SymbolMap.iter (fun sym defs ->
        match decl_of sym model with
        | ([], Int) ->
            let str = str_of_symbol sym in
            let value = str_of_symbol (List.hd defs).output in
            Printf.fprintf chan "        <TR><TD>%s = %s</TD></TR>\n" str value
        | _ -> ()) model.interp
    in
    if has_int then
      begin
        print_table_header "ints";
        print_ints ();
        print_table_footer ()
      end
  in
  let output_sets () =
    let print_sets () =
      let defs = defs_of Elem model in
      let sets =
        SymbolMap.fold
          (fun sym defs acc -> 
            List.fold_left (fun acc def ->
              match decl_of sym model with 
              | (_, Set _) -> SymbolSet.add def.output acc
              | _ -> acc) acc defs)
          model.interp SymbolSet.empty
      in
        SymbolSet.iter
          (fun set ->
            (*let set_value = Util.unopt (eval_term model (mk_const set)) in*)
            let set_defs = List.filter (fun def -> List.nth def.input 1 = set) defs in
            let in_set =
              List.filter
                (fun def -> match def.output with
                              BoolConst b -> b
                            | _ -> failwith "expected BoolConst _")
                set_defs
            in
            let in_set = List.map (fun d -> List.hd d.input) in_set in
            let in_set_rep = String.concat ", " (List.map str_of_symbol in_set) in
            Printf.fprintf chan "        <TR><TD>%s = {%s}</TD></TR>\n" (str_of_symbol (find_rep set)) in_set_rep
          )
          sets
    in 
    print_table_header "sets";
    print_sets ();
    print_table_footer ()
  in
  (* functions and pred *)
  let output_freesyms () =
    let string_of_def sym def =
      let rin = List.map (fun x -> str_of_symbol (find_rep x)) def.input in
      let rout = str_of_symbol (find_rep def.output) in
        (str_of_symbol sym) ^ "(" ^ (String.concat ", " rin) ^ ") = " ^ rout
    in
    print_table_header "predicates/functions";
    SymbolMap.iter
      (fun sym (args, _) -> match sym with
        | FreeSym (id, _) when args <> [] && id <> "k" ->
          List.iter
            (fun def -> Printf.fprintf chan "      <TR><TD>%s</TD></TR>\n" (string_of_def sym def))
            (defs_of sym model)
        | _ -> ()
      )
      model.sign;
    print_table_footer ()
  in
  let output_graph () =
    output_string chan "digraph Model {\n";
    output_locs ();
    output_loc_vars ();
    output_reach ();
    output_eps ();
    output_flds ();
    output_sets ();
    output_int_vars ();
    output_freesyms ();
    output_string chan "}\n"
  in
  output_graph ()
    

      
*)
