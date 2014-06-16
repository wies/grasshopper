(** Models of GRASS formulas *)

open Util
open Form
open FormUtil

exception Undefined

type value =
  | I of int
  | B of bool

module ValueMap = 
  Map.Make(struct
    type t = value
    let compare = compare
  end)

module ValueListMap = 
  Map.Make(struct
    type t = value list
    let compare = compare
  end)

module ValueSet = 
  Set.Make(struct
    type t = value
    let compare = compare
  end)

module SortedValueMap =
  Map.Make(struct
    type t = value * sort
    let compare = compare
  end)

type ext_value =
  | BaseVal of value
  | MapVal of value ValueListMap.t * ext_value
  | SetVal of ValueSet.t
  | TermVal of (ident * sort) list * term
  | Undef

let value_of_int i = I i

let value_of_bool b = B b

let bool_of_value = function
  | B b -> b
  | _ -> raise Undefined

let int_of_value = function
  | I i -> i
  | _ -> raise Undefined

let string_of_value = function
  | I i -> string_of_int i
  | B b -> string_of_bool b

type interpretation = (value ValueListMap.t * ext_value) SortedSymbolMap.t

type ext_interpretation = ext_value SortedValueMap.t

type model =
  { mutable card: int SortMap.t;
    mutable intp: interpretation;
    mutable vals: ext_interpretation;
  }

let empty : model = 
  { card = SortMap.empty;
    intp = SortedSymbolMap.empty;
    vals = SortedValueMap.empty
  }

(*let get_arity model sym = SymbolMap.find sym m*)

let add_card model srt card = 
  { model with card = SortMap.add srt card model.card }

let add_interp model sym arity def =
  { model with intp = SortedSymbolMap.add (sym, arity) def model.intp }

let add_def model sym arity args v =
  let m, d = 
    try SortedSymbolMap.find (sym, arity) model.intp 
    with Not_found -> ValueListMap.empty, Undef
  in
  let new_m = ValueListMap.add args v m in
  { model with intp = SortedSymbolMap.add (sym, arity) (new_m, d) model.intp }

let add_default_val model sym arity v =
  let m, _ = 
    try SortedSymbolMap.find (sym, arity) model.intp 
    with Not_found -> ValueListMap.empty, Undef
  in
  { model with intp = SortedSymbolMap.add (sym, arity) (m, BaseVal v) model.intp }

let add_default_term model sym arity args t =
  let m, _ = 
    try SortedSymbolMap.find (sym, arity) model.intp 
    with Not_found -> ValueListMap.empty, Undef
  in
  let new_map = m, TermVal (args, t) in
  { model with intp = SortedSymbolMap.add (sym, arity) new_map model.intp }

let get_result_sort model sym arg_srts =
  SortedSymbolMap.fold 
    (fun (sym1, (arg_srts1, res_srt1)) _ srt_opt ->
      if sym1 = sym && arg_srts = arg_srts1 then Some res_srt1 else srt_opt)
    model.intp None
      
    

let find_map_value model v srt = 
  match SortedValueMap.find (v, Fld srt) model.vals with
  | MapVal (m, d) -> m, d
  | Undef -> ValueListMap.empty, Undef
  | _ -> raise Undefined

let find_set_value model v srt =
  match SortedValueMap.find (v, Set srt) model.vals with
  | SetVal s -> s
  | _ -> raise Undefined

let equal model v1 v2 srt =
  v1 = v2 ||
  let v1_val = SortedValueMap.find (v1, srt) model.vals in
  let v2_val = SortedValueMap.find (v2, srt) model.vals in
  match v1_val, v2_val with
  | SetVal s1, SetVal s2 ->
      ValueSet.equal s1 s2
  | _, _ -> false

let extend_interp model sym (arity: arity) args res =
  let _, res_srt = arity in
  (* update cardinality *)
  let card = SortMap.find res_srt model.card in
  model.card <- SortMap.add res_srt (card + 1) model.card;
  (* update base value mapping *)
  let m, d = 
    try SortedSymbolMap.find (sym, arity) model.intp 
    with Not_found -> ValueListMap.empty, Undef
  in
  let new_sym_intp = ValueListMap.add args (I card) m, d in
  model.intp <- SortedSymbolMap.add (sym, arity) new_sym_intp model.intp;
  (* update extended value mapping *)
  begin
    match res_srt with
    | Fld srt
    | Set srt ->
        model.vals <- SortedValueMap.add (I card, res_srt) res model.vals
    | _ -> ()
  end;
  I card
            
let rec eval model = function
  | Var (id, srt) -> 
      interp_symbol model (FreeSym id) ([], srt) []
  | App (IntConst i, [], _) -> 
      I i
  | App (BoolConst b, [], _) -> 
      B b
  | App (Read, [fld; ind], srt) -> 
      let fld_val = eval model fld in
      let ind_val = eval model ind in
      let arity = [Fld srt; Loc], srt in
      interp_symbol model Read arity [fld_val; ind_val]
  | App (Write, [fld; ind; upd], (Fld isrt as srt)) ->
      let ind_val = eval model ind in
      let upd_val = eval model upd in
      let fld_val = eval model fld in
      let arity = [srt; Loc; isrt], srt in
      (try interp_symbol model Write arity [fld_val; ind_val; upd_val]
      with Undefined ->
        let m, d = find_map_value model fld_val srt in
        let res = MapVal (ValueListMap.add [ind_val] upd_val m, d) in
        extend_interp model Write arity [fld_val; ind_val; upd_val] res)
  | App (UMinus, [t], _) ->
      I (-(eval_int model t))
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
      in I (f (eval_int model t1) (eval_int model t2))
  | App (Empty, [], Set srt) -> 
      let arity = ([], Set srt) in
      (try interp_symbol model Empty arity []
      with Undefined ->
        extend_interp model Empty arity [] (SetVal ValueSet.empty))
  | App (SetEnum, ts, (Set esrt as srt)) ->
      let t_vals = List.map (eval model) ts in
      let arity = [esrt], srt in
      (try interp_symbol model SetEnum arity t_vals
      with Undefined ->
        let res = 
          List.fold_left (fun s v -> ValueSet.add v s) ValueSet.empty t_vals 
        in
        extend_interp model SetEnum arity t_vals (SetVal res))
  | App (Union, ts, (Set esrt as srt)) ->
      let t_vals = List.map (eval model) ts in
      let arity = [srt], srt in
      (try interp_symbol model Union arity t_vals
      with Undefined ->
        let res = 
          List.fold_left
            (fun res v -> ValueSet.union res (find_set_value model v esrt)) 
            ValueSet.empty t_vals
        in extend_interp model Union arity t_vals (SetVal res))
  | App (Inter, t :: ts, (Set esrt as srt)) ->
      let t_val = eval model t in
      let t_vals = List.map (eval model) ts in
      let arity = [srt], srt in
      (try interp_symbol model Inter arity (t_val :: t_vals)
      with Undefined ->
        let res = 
          List.fold_left
            (fun res v -> ValueSet.inter res (find_set_value model v esrt))
            (find_set_value model t_val esrt) t_vals
        in extend_interp model Union arity t_vals (SetVal res))
  | App (Diff, [t1; t2], (Set esrt as srt)) ->
      let t1_val = eval model t1 in
      let t2_val = eval model t2 in
      let arity = [srt; srt], srt in
      (try interp_symbol model Diff arity [t1_val; t2_val]
      with Undefined ->
        let res = 
          ValueSet.diff 
            (find_set_value model t1_val esrt)
            (find_set_value model t2_val esrt)
        in extend_interp model Diff arity [t1_val; t2_val] (SetVal res))
  | App (Eq, [t1; t2], srt) ->
      B (equal model (eval model t1) (eval model t2) srt)
  | App (LtEq as rel, [t1; t2], _)
  | App (GtEq as rel, [t1; t2], _)
  | App (Lt as rel, [t1; t2], _)
  | App (Gt as rel, [t1; t2], _) ->
      let r = match rel with
      | LtEq -> (<=) | GtEq -> (>=) | Lt -> (<) | Gt -> (>)
      | _ -> failwith "impossible"
      in 
      B (r (eval_int model t1) (eval_int model t2))
  | App (Elem, [e; s], _) ->
      let e_val = eval model e in
      let srt = element_sort_of_set s in
      let s_val = find_set_value model (eval model s) srt in
      B (ValueSet.mem e_val s_val)
  | App (SubsetEq, [s1; s2], _) ->
      let srt = element_sort_of_set s1 in
      let s1_val = find_set_value model (eval model s1) srt in
      let s2_val = find_set_value model (eval model s2) srt in
      B (ValueSet.subset s1_val s2_val)
   | App (sym, args, srt) ->
      let arg_srts, arg_vals = 
        List.split (List.map (fun arg -> sort_of arg, eval model arg) args)
      in
      let arity = arg_srts, srt in
      interp_symbol model sym arity arg_vals 

and interp_symbol model sym arity args = 
  try 
    let m, d = SortedSymbolMap.find (sym, arity) model.intp in
    fun_app model (MapVal (m, d)) args
  with Not_found -> raise Undefined

and fun_app model funv args =
  let default = function
    | TermVal (ids, t) ->
        let model1 = 
          List.fold_left2 
            (fun model1 (id, srt) arg -> 
              add_def model1 (FreeSym id) ([], srt) [] arg)
            model ids args
        in eval model1 t
    | BaseVal v -> v
    | _ -> raise Undefined
  in
  let rec fr = function
    | MapVal (m, d) ->
        (try ValueListMap.find args m with Not_found -> default d)
    | _ -> raise Undefined
  in
  fr funv

and eval_int model t =
  match eval model t with
  | I i -> i
  | _ -> raise Undefined

and eval_bool model t =
  match eval model t with
  | B b -> b
  | _ -> raise Undefined

let is_defined model sym arity args =
  try 
    ignore (interp_symbol model sym arity args);
    true
  with Undefined -> false


let get_values_of_sort model srt =
  let card =
    try SortMap.find srt model.card 
    with Not_found -> 0
  in
  Util.generate_list value_of_int card

let get_symbols_of_sort model arity =
  SortedSymbolMap.fold 
    (fun (sym, arity1) _ symbols ->
      if arity1 = arity 
      then SymbolSet.add sym symbols
      else symbols)
    model.intp SymbolSet.empty

let finalize_values model =
  let loc_values = get_values_of_sort model Loc in
  let generate_sets () =
    List.iter (fun s ->
      let vset =
        List.fold_left (fun vset e ->
          let e_in_s = interp_symbol model Elem ([Loc; Set Loc], Bool) [e; s] in
          if bool_of_value e_in_s 
          then ValueSet.add e vset
          else vset)
          ValueSet.empty loc_values
      in
      model.vals <- SortedValueMap.add (s, Set Loc) (SetVal vset) model.vals)
      (get_values_of_sort model (Set Loc))
  in
  let generate_fields srt =
    List.iter (fun f ->
      let fmap =
        List.fold_left (fun fmap e ->
          try
            let f_of_e = interp_symbol model Read ([Fld srt; Loc], srt) [f; e] in
            ValueListMap.add [e] f_of_e fmap
          with Undefined -> fmap)
          ValueListMap.empty loc_values
      in
      model.vals <- SortedValueMap.add (f, Fld srt) (MapVal (fmap, Undef)) model.vals)
      (get_values_of_sort model (Fld srt))
  in
  generate_sets ();
  List.iter generate_fields [Loc; Int; Bool];
  model

let succ model fld x =
  let arity = [Fld Loc; Loc; Loc; Loc], Bool in
  let locs = get_values_of_sort model Loc in
  List.fold_left (fun s y ->
    if y <> x && 
      bool_of_value (interp_symbol model Btwn arity [fld; x; y; y]) &&
      (s == x || bool_of_value (interp_symbol model Btwn arity [fld; x; y; s]))
    then y else s)
    x locs
      

let output_graphviz chan model =
  (*let const_map = const_map model in 
     let find_rep s = match s with
     | BoolConst _ | IntConst _ -> s
     | _ -> try SymbolMap.find s const_map with Not_found -> s
     in*)
  let colors1 = ["blue"; "red"; "green"; "orange"; "darkviolet"] in
  let colors2 = ["blueviolet"; "crimson"; "olivedrab"; "orangered"; "purple"] in
  let flds = SymbolSet.elements (get_symbols_of_sort model ([], Fld Loc)) in
  let fld_map = List.map (fun sym -> sym, interp_symbol model sym ([], Fld Loc) []) flds in
  let locs = get_values_of_sort model Loc in
  let fld_colors =
    Util.fold_left2 (fun acc fld color -> ((fld, color)::acc)) [] flds colors1
  in
  let ep_colors =
    Util.fold_left2 (fun acc fld color -> (fld, color)::acc) [] flds colors2
  in
  let get_label fld =
    let color =
      try List.assoc fld fld_colors with Not_found -> "black"
    in
    Printf.sprintf "label=\"%s\", fontcolor=%s, color=%s" (str_of_symbol fld) color color
  in
  let string_of_sorted_value srt v = 
    match srt with
    | Int | Bool -> string_of_value v 
    | _ -> string_of_sort srt ^ "!" ^ string_of_value v in
  let string_of_loc_value l = string_of_sorted_value Loc l in 
  let output_flds () = 
    List.iter 
      (fun fld ->
        List.iter (fun l ->
          try
            if interp_symbol model Null ([], Loc) [] = l then () else
            let f = List.assoc fld fld_map in
            let m, d = find_map_value model f Loc in
            let r = fun_app model (MapVal (m, d)) [l] in
	    let label = get_label fld in
	    Printf.fprintf chan "\"%s\" -> \"%s\" [%s]\n" 
	      (string_of_loc_value l) (string_of_loc_value r) label
          with Undefined -> ())
          locs)
      flds
  in
  let output_reach () = 
    List.iter 
      (fun fld ->
        List.iter (fun l ->
          let f = List.assoc fld fld_map in
          let r = succ model f l in
          if is_defined model Read ([Fld Loc; Loc], Loc) [f; l] || r == l then () else
	  let label = get_label fld in
	  Printf.fprintf chan "\"%s\" -> \"%s\" [%s, style=dashed]\n" 
	    (string_of_loc_value l) (string_of_loc_value r) label)
          locs)
      flds
  in
  (*
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
   *)
  let output_locs () =
    let output_data_fields loc srt =
      SymbolSet.iter
        (fun fld ->
          try 
            let f = interp_symbol model fld ([], Fld srt) [] in
            let fld_str = str_of_symbol fld in
            let m, d = find_map_value model f srt in
            let v = fun_app model (MapVal (m, d)) [loc] in
            Printf.fprintf chan "      <tr><td><b>%s = %s</b></td></tr>\n" fld_str (string_of_value v)
          with Undefined -> ())
        (get_symbols_of_sort model ([], Fld srt))
    in
    List.iter
      (fun loc ->
        Printf.fprintf chan "  \"%s\" [shape=none, margin=0, label=<\n" (string_of_loc_value loc);
        output_string chan "    <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n";
        Printf.fprintf chan "      <tr><td><b>%s</b></td></tr>\n" (string_of_loc_value loc);
        output_data_fields loc Int;
        output_data_fields loc Bool;
        output_string chan "</table>\n";
        output_string chan ">];\n"
      )
      locs
  in
  let output_loc_vars () = 
    SymbolSet.iter (fun sym ->
      let v = interp_symbol model sym ([], Loc) [] in
      Printf.fprintf chan "\"%s\" -> \"%s\"\n" (str_of_symbol sym) (string_of_loc_value v))
   (get_symbols_of_sort model ([], Loc))
  in
  let print_table_header = 
    let l = ref 0 in
    fun title ->
      l := !l + 1;
      output_string chan ("{ rank = sink; Legend" ^ (string_of_int !l) ^ " [shape=none, margin=0, label=<\n");
      output_string chan "    <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n";
      output_string chan "      <tr>\n";
      output_string chan ("        <td><b>" ^ title ^ "</b></td>\n");
      output_string chan "      </tr>\n";
  in
  let print_table_footer () =
    output_string chan "</table>\n";
    output_string chan ">];\n";
    output_string chan "}\n";
  in
  (*
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
            Printf.fprintf chan "        <tr><td>%s = %s</td></tr>\n" str value
        | _ -> ()) model.interp
    in
    if has_int then
      begin
        print_table_header "ints";
        print_ints ();
        print_table_footer ()
      end
  in
  *)
  let output_sets () =
    let print_sets srt =
      let sets = get_symbols_of_sort model ([], Set srt) in
      SymbolSet.iter
        (fun set ->
          let s = interp_symbol model set ([], Set srt) [] in
          let s = find_set_value model s Loc in
          let vals = List.map (fun e ->  string_of_sorted_value srt e) (ValueSet.elements s) in
          let set_rep = String.concat ", " vals in
          Printf.fprintf chan "        <tr><td>%s = {%s}</td></tr>\n" (str_of_symbol set) set_rep
        )
        sets
    in 
    print_table_header "sets";
    print_sets Loc;
    print_sets Int;
    print_table_footer ()
  in
  (* functions and pred *)
  (*
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
            (fun def -> Printf.fprintf chan "      <tr><td>%s</td></tr>\n" (string_of_def sym def))
            (defs_of sym model)
        | _ -> ()
      )
      model.sign;
    print_table_footer ()
  in
   *)
  let output_graph () =
    output_string chan "digraph Model {\n";
    output_locs ();
    output_flds ();
    output_loc_vars ();
    output_reach ();
    (*output_eps ();*)
    output_sets ();
    (*output_int_vars ();
    output_freesyms ();*)
    output_string chan "}\n"
  in
  output_graph ()
    

      
