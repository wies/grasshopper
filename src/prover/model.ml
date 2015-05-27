(** {5 Models of GRASS formulas} *)

open Util
open Grass
open GrassUtil

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

module SortedValueListMap =
  Map.Make(struct
    type t = (value * sort) list
    let compare = compare
  end)

    
module SortedValueSet =
  Set.Make(struct
    type t = value * sort
    let compare = compare
  end)

type ext_value =
  | BaseVal of value
  | MapVal of value ValueListMap.t * ext_value
  | SetVal of ValueSet.t
  | TermVal of (ident * sort) list * term
  | FormVal of (ident * sort) list * form
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

let get_interp model sym arity =
  try SortedSymbolMap.find (sym, arity) model.intp
  with Not_found -> ValueListMap.empty, Undef

let add_def model sym arity args v =
  if Debug.is_debug 1 then print_endline (
      "add_def: " ^ (string_of_symbol sym) ^ ": " ^ (string_of_arity arity) ^
      " => " ^ (String.concat "," (List.map string_of_value args)) ^
      " => " ^ (string_of_value v));
  let m, d = get_interp model sym arity in
  let new_m = ValueListMap.add args v m in
  { model with intp = SortedSymbolMap.add (sym, arity) (new_m, d) model.intp }

let add_default_val model sym arity v =
  if Debug.is_debug 1 then print_endline (
      "add_default_val: " ^ (string_of_symbol sym) ^ ": " ^ (string_of_arity arity) ^
      " => " ^ (string_of_value v));
  let m, d = get_interp model sym arity in
  (match d with
  | Undef -> ()
  | BaseVal v1 when v = v1 -> ()
  | _ -> failwith "Model.add_default_val: inconsistent default values in model detected");
  { model with intp = SortedSymbolMap.add (sym, arity) (m, BaseVal v) model.intp }

let add_default_term model sym arity args t =
  let m, _ = get_interp model sym arity in
  let new_map = m, TermVal (args, t) in
  { model with intp = SortedSymbolMap.add (sym, arity) new_map model.intp }

let add_default_form model sym arity args f =
  let m, _ = get_interp model sym arity in
  let new_map = m, FormVal (args, f) in
  { model with intp = SortedSymbolMap.add (sym, arity) new_map model.intp }


let get_result_sort model sym arg_srts =
  SortedSymbolMap.fold 
    (fun (sym1, (arg_srts1, res_srt1)) _ srt_opt ->
      if sym1 = sym && arg_srts = arg_srts1 then Some res_srt1 else srt_opt)
    model.intp None
      

let find_map_value model v arg_srt res_srt = 
  match SortedValueMap.find (v, Map (arg_srt, res_srt)) model.vals with
  | MapVal (m, d) -> m, d
  | Undef -> ValueListMap.empty, Undef
  | _ -> raise Undefined

let find_set_value model v srt =
  try
    match SortedValueMap.find (v, Set srt) model.vals with
    | SetVal s -> s
    | _ -> raise Undefined
  with Not_found ->
    begin
      if Debug.is_debug 1 then
        begin
          print_string "Model.find_set_value: not found '";
          print_string ((string_of_value v) ^ "' of type ");
          print_endline (string_of_sort (Set srt))
        end;
      raise Undefined
    end

let equal model v1 v2 srt =
  v1 = v2 ||
  match srt with
  | Set _ ->
      let v1_val = 
        try SortedValueMap.find (v1, srt) model.vals 
        with Not_found -> raise Undefined
      in
      let v2_val = 
        try SortedValueMap.find (v2, srt) model.vals
        with Not_found -> raise Undefined
      in
      (match v1_val, v2_val with
      | SetVal s1, SetVal s2 ->
          ValueSet.equal s1 s2
      | _, _ -> false)
  | _ -> false
      
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
    | Map (Loc _, srt)
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
      let ind_srt = sort_of ind in
      let arity = [Map (ind_srt, srt); ind_srt], srt in
      let res = interp_symbol model Read arity [fld_val; ind_val] in
      res
  | App (Write, [fld; ind; upd], (Map (dsrt, rsrt) as srt)) ->
      let ind_val = eval model ind in
      let upd_val = eval model upd in
      let fld_val = eval model fld in
      let arity = [srt; dsrt; rsrt], srt in
      (try interp_symbol model Write arity [fld_val; ind_val; upd_val]
      with Undefined ->
        let m, d = find_map_value model fld_val (sort_of ind) srt in
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
  | App (Eq, [t1; t2], _) ->
      let res = equal model (eval model t1) (eval model t2) (sort_of t1) in
      B res
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
  with Not_found -> 
    begin
      if Debug.is_debug 1 then
        begin
          print_string "Model.interp_symbol: symbol not found '";
          print_string (string_of_symbol sym);
          print_string "' of type ";
          print_string (string_of_arity arity);
          print_endline " in:";
          SortedSymbolMap.iter (fun (s,a) _ -> print_endline ("  " ^ (string_of_symbol s) ^ ": " ^ string_of_arity a)) model.intp
        end;
      raise Undefined
    end

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

let eval_bool_opt model t =
  try Some (eval_bool model t) 
  with Undefined -> None

let eval_int_opt model t =
  try Some (eval_int model t)
  with Undefined -> None

let rec eval_form model = function
  | BoolOp (Not, [f]) ->
      Util.Opt.map not (eval_form model f)
  | BoolOp (And, fs) ->
      List.fold_left 
        (fun acc f ->
          match acc with
          | Some false -> Some false
          | Some true -> eval_form model f  
          | None -> None)
        (Some true) fs
  | BoolOp (Or, fs) ->
      List.fold_left 
        (fun acc f ->
          match acc with
          | Some false -> eval_form model f
          | Some true -> Some true
          | None -> None) 
        (Some false) fs
  | Atom (t, _) -> eval_bool_opt model t
  | Binder (b, [], f, _) -> eval_form model f
  | _ -> None

let is_defined model sym arity args =
  try 
    ignore (interp_symbol model sym arity args);
    true
  with Undefined -> false


let get_values_of_sort model srt =
  let vals = 
    SortedSymbolMap.fold (fun (sym, (arg_srts, res_srt)) (m, d) vals ->
      if res_srt = srt 
      then 
        let map_vals = 
          ValueListMap.fold (fun _ -> ValueSet.add) m vals
        in 
        match arg_srts, d with
        | _, BaseVal v -> ValueSet.add v map_vals
        | _, _ -> map_vals
      else vals)
      model.intp ValueSet.empty
  in
  ValueSet.elements vals

let get_loc_sorts model =
  SortedSymbolMap.fold
    (function
      | (_, (_, Loc srt)) -> fun _ srts -> SortSet.add srt srts
      | _ -> fun _ srts -> srts)
    model.intp SortSet.empty

let get_set_sorts model =
  SortedSymbolMap.fold
    (function
      | (_, (_, Set srt)) -> fun _ srts -> SortSet.add srt srts
      | _ -> fun _ srts -> srts)
    model.intp SortSet.empty

let get_map_sorts model =
  SortedSymbolMap.fold
    (function
      | (_, (_, (Map _ as srt))) -> fun _ srts -> SortSet.add srt srts
      | _ -> fun _ srts -> srts)
    model.intp SortSet.empty

let get_loc_fld_sorts model =
  SortedSymbolMap.fold
    (function
      | (_, (_, (Map (Loc _, Loc _) as srt))) -> fun _ srts -> SortSet.add srt srts
      | _ -> fun _ srts -> srts)
    model.intp SortSet.empty
    
    
let get_symbols_of_sort model arity =
  SortedSymbolMap.fold 
    (fun (sym, arity1) _ symbols ->
      if arity1 = arity 
      then SymbolSet.add sym symbols
      else symbols)
    model.intp SymbolSet.empty

let restrict_to_sign model sign =
  let new_intp =
    SortedSymbolMap.fold 
      (fun (sym, arity) def new_intp ->
        let arities = 
          try SymbolMap.find sym sign 
          with Not_found -> [] 
        in
        if List.mem arity arities 
        then SortedSymbolMap.add (sym, arity) def new_intp
        else new_intp)
      model.intp SortedSymbolMap.empty
  in { model with intp = new_intp }

let restrict_to_idents model ids =
  let new_intp =  
    SortedSymbolMap.fold 
      (fun (sym, arity) def new_intp ->
        match sym with
        | FreeSym id when not (IdSet.mem id ids) ->
            new_intp
        | _ ->
            SortedSymbolMap.add (sym, arity) def new_intp
      )
      model.intp SortedSymbolMap.empty
  in { model with intp = new_intp }
    

let rename_free_symbols model fn =
  let new_intp =
    SortedSymbolMap.fold
      (fun (sym, arity) def new_intp ->
        match sym with
        | FreeSym id -> 
            SortedSymbolMap.add (FreeSym (fn id), arity) def new_intp
        | _ ->
            SortedSymbolMap.add (sym, arity) def new_intp
      )
      model.intp SortedSymbolMap.empty
  in
  { model with intp = new_intp }

let succ model sid fld x =
  let loc_srt = Loc sid in
  let btwn_arity = [loc_field_sort sid; loc_srt; loc_srt; loc_srt], Bool in
  let locs = get_values_of_sort model loc_srt in
  List.fold_left (fun s y ->
    if y <> x && 
      bool_of_value (interp_symbol model Btwn btwn_arity [fld; x; y; y]) &&
      (s == x || bool_of_value (interp_symbol model Btwn btwn_arity [fld; x; y; s]))
    then y else s)
    x locs
      
let complete model =
  let locs srt = get_values_of_sort model (Loc srt) in
  let loc_flds srt = get_values_of_sort model (loc_field_sort srt) in
  let flds srt =
    try
      let loc_srt = Loc srt in
      let null = interp_symbol model Null ([], loc_srt) [] in
      let btwn_arity = [loc_field_sort srt; loc_srt; loc_srt; loc_srt], Bool in
      List.filter (fun f ->
        try 
          bool_of_value 
            (interp_symbol model Btwn btwn_arity [f; null; null; null])
        with Undefined -> false) (loc_flds srt)
    with Undefined -> []
  in
  let loc_srts = get_loc_sorts model in
  let new_model =
    SortSet.fold (fun srt model ->
      List.fold_left 
        (fun new_model fld ->
          List.fold_left 
            (fun new_model arg ->
              let res = succ model srt fld arg in
              let read_arity = [loc_field_sort srt; Loc srt], Loc srt in
              add_def new_model Read read_arity [fld; arg] res)
            new_model (locs srt))
        model (flds srt))
      loc_srts model
  in
  new_model


module PQ = PrioQueue.Make
    (struct
      type t = value * sort
      let compare = compare
    end)
    (struct
      type t = int
      let compare = compare
    end)
    
(** Find a term that evaluates to value [v] of sort [srt] in [model].*)
let find_term model =
  (* To find a smallest term that represents a given value in [model], we implement
     a variant of Dijkstra's algorithm that computes shortest hyperpaths in a hypergraph.
     The algorithm is adapted from this paper:
       Optimal Traversal of Directed Hypergraphs
       Georgio Ausiello, Giuseppe Italiano, and Umberto Nanni, 1992
   *)
  (* compute FD-graph of model *)
  let fedges, dedges, init_reach =
    SortedSymbolMap.fold 
      (fun (sym, (arg_srts, res_srt)) (m, d) (fedges, dedges, init_reach) ->
        match sym, res_srt with
        | _, Bool | _, Int | Write, _ -> (fedges, dedges, init_reach)
        | _ ->
            let m1 =
              match d with
              | BaseVal v ->
                  let arg_vals =
                    List.map (function
                      | Int -> [I 0]
                      | Bool -> [B false]
                      | srt -> get_values_of_sort model srt)
                      arg_srts
                  in
                  let arg_product =
                    List.fold_right (fun args arg_product ->
                      List.fold_left
                        (fun acc arg ->
                          List.fold_left
                            (fun acc args -> (arg :: args) :: acc)
                            acc arg_product)
                        [] args)
                      arg_vals [[]]
                  in
                  List.fold_left (fun m args ->
                    if ValueListMap.mem args m then m
                    else ValueListMap.add args v m)
                    m arg_product
              | _ -> m
            in
            ValueListMap.fold
              (fun args v (fedges, dedges, init_reach) ->
                let s = List.combine args arg_srts in
                let t = v, res_srt in
                let es =
                  try SortedValueListMap.find s fedges
                  with Not_found -> []
                in
                let fedges1 = SortedValueListMap.add s ((sym, t) :: es) fedges in
                let init_reach1 = SortedValueListMap.add s (List.length s) init_reach in
                let init_reach2 = SortedValueListMap.add [t] 1 init_reach1 in
                let dedges1, init_reach3 =
                  List.fold_left
                    (fun (dedges1, init_reach3) (_, srt as z) ->
                      let es =
                        try SortedValueMap.find z dedges1
                        with Not_found -> []
                      in
                      SortedValueMap.add z (s :: es) dedges1,
                      match srt with
                      | Bool | Int ->
                          SortedValueListMap.add [z] 0 init_reach3
                      | _ -> init_reach3
                    )
                    (dedges, init_reach2) s
                in
                fedges1, dedges1, init_reach3
              )
              m1 (fedges, dedges, init_reach)
      )
      model.intp (SortedValueListMap.empty, SortedValueMap.empty, SortedValueListMap.empty)
  in
  (* initialize remaining data structures *)
  let init_queue, init_reach, init_dist, init_prev =
    SortedSymbolMap.fold 
      (fun (sym, (arg_srts, res_srt)) (m, d) (init_queue, init_reach, init_dist, init_prev) ->
        let add v =
          let x = v, res_srt in
          PQ.insert x 0 init_queue,
          SortedValueListMap.add [x] 0 init_reach,
          SortedValueMap.add x 0 init_dist,
          SortedValueMap.add x (sym, []) init_prev
        in
        match arg_srts, d with
        | [], BaseVal v -> add v
        | [], Undef -> add (ValueListMap.find [] m)
        | _, _ ->
            init_queue, init_reach, init_dist, init_prev)
      model.intp (PQ.empty, init_reach, SortedValueMap.empty, SortedValueMap.empty)
  in
  (* auxiliary function for shortest path algorithm *)
  let scan t d_t (reach, dist, prev, queue) (sym, x) =
    let d_t_x = d_t + 1 in
    let reach_x = SortedValueListMap.find [x] reach in
    if reach_x = 1 then
      SortedValueListMap.add [x] 0 reach,
      SortedValueMap.add x d_t_x dist,
      SortedValueMap.add x (sym, t) prev,
      PQ.insert x d_t_x queue
    else if d_t_x < SortedValueMap.find x dist then
      reach, 
      SortedValueMap.add x d_t_x dist,
      SortedValueMap.add x (sym, t) prev,
      PQ.adjust (fun _ -> d_t_x) x queue
    else
      reach, dist, prev, queue
  in
  (* shortest path algorithm *)
  let rec shortest_paths reach dist prev queue =
    if PQ.is_empty queue then prev else
    let t, d_t, queue = PQ.extract_min queue in
    let get_fedges t =
      try SortedValueListMap.find t fedges
      with Not_found -> []
    in
    let reach, dist, prev, queue =
      List.fold_left (scan [t] d_t) (reach, dist, prev, queue) (get_fedges [t])
    in
    let dedges_t =
      try SortedValueMap.find t dedges
      with Not_found -> []
    in
    let reach, dist, prev, queue =
      List.fold_left
        (fun (reach, dist, prev, queue) z ->
          let reach_z = SortedValueListMap.find z reach - 1 in
          let reach1 = SortedValueListMap.add z reach_z reach in
          if reach_z = 0 then
            let d_z =
              List.fold_left
                (fun d_z x ->
                  let d_x = try SortedValueMap.find x dist with Not_found -> 0 in
                  d_z + d_x)
                0 z
            in
            List.fold_left (scan z d_z) (reach1, dist, prev, queue) (get_fedges z)
          else reach1, dist, prev, queue
        )
        (reach, dist, prev, queue)
        dedges_t
    in
    shortest_paths reach dist prev queue
  in
  (* compute shortest paths *)
  let prev = shortest_paths init_reach init_dist init_prev init_queue in
  let rec find (v, srt) =
    match srt with 
    | Bool -> mk_bool_term (bool_of_value v)
    | Int -> mk_int (int_of_value v)
    | _ ->
        let sym, vs = SortedValueMap.find (v, srt) prev in
        let args = List.map find vs in
        mk_app srt sym args
  in fun v srt -> find (v, srt)

let finalize_values model =
  let mk_finite_set srt s =
    let vset =
      List.fold_left (fun vset e ->
        let e_in_s = interp_symbol model Elem ([srt; Set srt], Bool) [e; s] in
        if bool_of_value e_in_s 
        then ValueSet.add e vset
        else vset)
        ValueSet.empty (get_values_of_sort model srt)
    in
    model.vals <- SortedValueMap.add (s, Set srt) (SetVal vset) model.vals
  in
  let mk_set srt s =
    let m, d = SortedSymbolMap.find (Elem, ([srt; Set srt], Bool)) model.intp in
    match d with
    | BaseVal (B false) -> 
        let vset =
          ValueListMap.fold 
            (fun vs v vset ->
              match vs with
              | [e; s1] when bool_of_value v && s1 = s ->
                  ValueSet.add e vset
              | _ -> vset)
            m ValueSet.empty
        in
        model.vals <- SortedValueMap.add (s, Set srt) (SetVal vset) model.vals
    | _ -> ()
  in
  let generate_sets srt =
    let rec is_finite_set_sort = function
      | Bool -> true
      | Loc _ -> true
      | Set srt -> is_finite_set_sort srt
      | Map (dsrt, rsrt) ->
          is_finite_set_sort dsrt && is_finite_set_sort rsrt
      | Array _ -> true
      | ArrayCell _ -> true
      | FreeSrt _ -> true
      | _ -> false
    in
    List.iter
      (if is_finite_set_sort srt then mk_finite_set srt else mk_set srt)
      (get_values_of_sort model (Set srt))
  in
  let generate_fields srt =
    let dsrt = dom_sort srt in
    let rsrt = range_sort srt in
    List.iter
      (fun f ->
        let fmap =
          List.fold_left (fun fmap e ->
            try
              let f_of_e = interp_symbol model Read ([srt; dsrt], rsrt) [f; e] in
              ValueListMap.add [e] f_of_e fmap
            with Undefined -> fmap)
            ValueListMap.empty
            (get_values_of_sort model dsrt)
        in
        model.vals <- SortedValueMap.add (f, srt) (MapVal (fmap, Undef)) model.vals)
      (get_values_of_sort model srt)
  in
  SortSet.iter generate_sets (get_set_sorts model);
  SortSet.iter generate_fields (get_map_sorts model);
  model

(** Printing *)
            
let string_of_sorted_value srt v =
  let rec elim_loc = function
    | Loc srt -> elim_loc srt
    | Set srt -> Set (elim_loc srt)
    | Array srt -> Array (elim_loc srt)
    | ArrayCell srt -> ArrayCell (elim_loc srt)
    | Map (dsrt, rsrt) -> Map (elim_loc dsrt, elim_loc rsrt)
    | srt -> srt
  in
  match srt with
  | Int | Bool -> string_of_value v
  | _ ->
      let srt_str =
        Str.global_replace (Str.regexp "<") "&lt;"
          (Str.global_replace (Str.regexp ">") "&gt;" (string_of_sort (elim_loc srt)))
      in
      srt_str ^ "!" ^ string_of_value v

let output_json chan model =
  let string_of_sorted_value srt v = 
    "\"" ^ string_of_sorted_value srt v ^ "\""
  in
  let output_set s esrt =
    let vals = List.map (fun e ->  string_of_sorted_value esrt e) s in
    let set_rep = String.concat ", " vals in
    output_string chan ("[" ^ set_rep ^ "]")
  in
  let null_val srt = eval model (mk_null srt) in
  let output_value sym srt =
    match srt with
    | Loc _ | Bool | Int -> 
        let v = interp_symbol model sym ([], srt) [] in
        output_string chan (string_of_sorted_value srt v)
    | Set esrt ->
        (try
          let set = interp_symbol model sym ([], srt) [] in
          let s = find_set_value model set esrt in
          output_set (ValueSet.elements s) esrt
        with Undefined -> output_set [] esrt (* fix me *))
    | Map (dsrt, rsrt) ->
        let fld = interp_symbol model sym ([], srt) [] in
        let args = get_values_of_sort model dsrt in
        let arg_res = 
          Util.flat_map 
            (fun arg ->
              try
                let res = interp_symbol model Read ([srt; dsrt], rsrt) [fld; arg] in
                if is_loc_sort dsrt &&
                  (arg = null_val (struct_sort_of_sort dsrt) ||
                  res = null_val (struct_sort_of_sort dsrt))
                then [] 
                else  [(arg, res)]
              with Undefined -> [])
            args
        in
        output_string chan "[";
        Util.output_list chan 
          (fun (arg, res) -> 
            Printf.fprintf chan "{\"arg\": %s, \"res\": %s}" 
              (string_of_sorted_value dsrt arg) (string_of_sorted_value rsrt res)
          )
          ", " arg_res;
        output_string chan "]"
    | _ -> ()
  in
  let output_id ov id srt =
    Printf.fprintf chan "{\"name\": \"%s\", \"type\": \"%s\", \"value\": "
      id (string_of_sort srt);
    ov ();
    Printf.fprintf chan "}"
  in
  let output_symbol (sym, srt) = 
    output_string chan ", ";
    output_id (fun () -> output_value sym srt) (string_of_symbol sym) srt
  in
  let defs = 
    SortedSymbolMap.fold 
      (fun (sym, arity) _ defs ->
        match sym, arity with
        | (FreeSym _, ([], srt))
        | (Null, ([], srt)) -> (sym, srt) :: defs
        | _, _ -> defs) 
      model.intp []
  in
  output_string chan "[";
  SortSet.iter (fun srt ->
    let locs = get_values_of_sort model (Loc srt) in
    output_id (fun () -> output_set locs (Loc srt)) (string_of_sort (Loc srt)) (Set (Loc srt)))
    (get_loc_sorts model);
  List.iter output_symbol defs;
  output_string chan "]"
  
let output_graphviz chan model terms =
  let find_term = find_term model in
  let colors1 = ["blue"; "red"; "green"; "orange"; "darkviolet"] in
  let colors2 = ["blueviolet"; "crimson"; "olivedrab"; "orangered"; "purple"] in
  let loc_sorts = get_loc_sorts model in
  let fld_srts = get_loc_fld_sorts model in
  let all_flds =
    Util.flat_map
      (fun srt ->
        List.map (fun fld -> (srt, fld))
          (get_values_of_sort model srt))
      (SortSet.elements fld_srts)
  in
  let fld_colors =
    Util.fold_left2 (fun acc fld color -> ((fld, color)::acc)) [] all_flds colors1
  in
  let ep_colors =
    Util.fold_left2 (fun acc fld color -> (fld, color)::acc) [] all_flds colors2
  in
  let get_label fsrt fld =
    let color =
      try List.assoc (fsrt, fld) fld_colors with Not_found -> "black"
    in
    let f = find_term fld fsrt in
    Printf.sprintf "label=\"%s\", fontcolor=%s, color=%s" (string_of_term f) color color
  in
  let string_of_loc_value srt l = string_of_sorted_value srt l in
  let output_graph srt =
    let flds = get_values_of_sort model (loc_field_sort srt) in
    let locs = get_values_of_sort model (Loc srt) in
    let read_arity = [loc_field_sort srt; Loc srt], Loc srt in
    let rsrts =
      SortSet.fold
        (function
          | Map (Loc srt1, Loc rsrt) when srt1 = srt -> SortSet.add rsrt
          | _ -> fun rsrts -> rsrts)
        fld_srts SortSet.empty
    in
    let output_flds rsrt =
      let filter_null r =
        (not !Config.model_null_edge) &&
        (interp_symbol model Null ([], Loc rsrt) [] = r)
      in
      let fld_srt = Map (Loc srt, Loc rsrt) in
      let flds = get_values_of_sort model fld_srt in
      let read_arity = [fld_srt; Loc srt], Loc rsrt in
      List.iter 
        (fun f ->
          List.iter (fun l ->
            try
              let r = interp_symbol model Read read_arity [f; l] in
              if filter_null r then () else
	      let label = get_label fld_srt f in
	      Printf.fprintf chan "\"%s\" -> \"%s\" [%s]\n" 
	        (string_of_loc_value srt l) (string_of_loc_value rsrt r) label
            with Not_found -> ())
            locs)
        flds
    in
    let output_array () =
      match srt with
      | Array esrt ->
          let cell_srt = Loc (ArrayCell esrt) in
          let cell_locs = get_values_of_sort model cell_srt in
          List.iter (fun l ->
            try
              List.iter (fun c ->
                let l1 = interp_symbol model ArrayOfCell ([cell_srt], Loc (Array esrt)) [c] in
                if l1 = l then begin
                  Printf.fprintf chan "\"%s\" -> \"%s\" [label=\"array\"]\n" 
	            (string_of_loc_value (ArrayCell esrt) c) (string_of_loc_value srt l);
                  let cells = interp_symbol model ArrayCells ([Loc (Array esrt)], Map (Int, cell_srt)) [l] in
                  let i = interp_symbol model IndexOfCell ([cell_srt], Int) [c] in
                  let c1 = interp_symbol model Read ([Map (Int, cell_srt); Int], cell_srt) [cells; i] in
                  if c1 = c then
                    Printf.fprintf chan "\"%s\" -> \"%s\" [label=\"%d\"]\n" 
	              (string_of_loc_value srt l) (string_of_loc_value (ArrayCell esrt) c) (int_of_value i)                    
                end)
                cell_locs
            with Not_found | Undefined -> ())
            locs
      | _ -> ()
    in
    let output_reach () = 
      List.iter 
        (fun f ->
          List.iter (fun l ->
            let r = succ model srt f l in
            if is_defined model Read read_arity [f; l] || r == l then () else
	    let label = get_label (loc_field_sort srt) f in
	    Printf.fprintf chan "\"%s\" -> \"%s\" [%s, style=dashed]\n" 
	      (string_of_loc_value srt l) (string_of_loc_value srt r) label)
            locs)
        flds
    in
    let output_eps () =
      let arg_srts = [loc_field_sort srt; Set (Loc srt); Loc srt] in
      let m, _ = get_interp model EntPnt (arg_srts, Loc srt) in
      ValueListMap.iter (function 
        | [f; s; l] -> fun v ->
            let fld = find_term f (loc_field_sort srt) in
            let set = find_term s (Set (Loc srt)) in
            let color = try List.assoc (srt, f) ep_colors with Not_found -> "black" in
            let label =
              "ep(" ^ (string_of_term fld) ^ ", " ^ (string_of_term set) ^ ")"
            in
	    Printf.fprintf chan
              "\"%s\" -> \"%s\" [label=\"%s\", fontcolor=%s, color=%s, style=dotted]\n"
              (string_of_loc_value srt l) (string_of_loc_value srt v) label color color
        | _ -> fun v -> ()) 
        m
    in
    let output_locs () =
      let output_data_fields loc rsrt =
        SymbolSet.iter
          (fun fld ->
            try 
              let f = interp_symbol model fld ([], field_sort srt rsrt) [] in
              let fld_str = string_of_symbol fld in
              let m, d = find_map_value model f (Loc srt) rsrt in
              let v = fun_app model (MapVal (m, d)) [loc] in
              Printf.fprintf chan "      <tr><td><b>%s = %s</b></td></tr>\n" fld_str (string_of_value v)
            with Undefined -> ())
          (get_symbols_of_sort model ([], field_sort srt rsrt))
      in
      List.iter
        (fun loc ->
          Printf.fprintf chan "  \"%s\" [shape=none, margin=0, label=<\n" (string_of_loc_value srt loc);
          output_string chan "    <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n";
          Printf.fprintf chan "      <tr><td><b>%s</b></td></tr>\n" (string_of_loc_value srt loc);
          output_data_fields loc Int;
          output_data_fields loc Bool;
          output_string chan "</table>\n";
          output_string chan ">];\n"
        )
        locs
    in
    let output_loc_vars () = 
      SymbolSet.iter (fun sym ->
        let v = interp_symbol model sym ([], Loc srt) [] in
        Printf.fprintf chan "\"%s\" -> \"%s\"\n" (string_of_symbol sym) (string_of_loc_value srt v))
        (get_symbols_of_sort model ([], Loc srt))
    in
    output_locs ();
    SortSet.iter output_flds rsrts;
    output_array ();
    output_loc_vars ();
    output_reach ();
    output_eps ();
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
  let output_int_vars () = 
    let ints = get_symbols_of_sort model ([], Int) in
    let print_ints () =
      SymbolSet.iter 
        (fun sym ->
          let str = string_of_symbol sym in
          let value = interp_symbol model sym ([], Int) [] in
          Printf.fprintf chan "        <tr><td>%s = %s</td></tr>\n" 
            str (string_of_value value)
        ) ints
    in
    if not (SymbolSet.is_empty ints) then
      begin
        print_table_header "ints";
        print_ints ();
        print_table_footer ()
      end
  in
  let output_sets () =
    let print_sets srt =
      TermSet.iter
        (function
          | App (FreeSym _, _, Set srt1) as set_t when srt = srt1 ->
              (try
                let set = eval model set_t in
                let s = find_set_value model set srt in
                let vals = List.map (fun e ->  string_of_sorted_value srt e) (ValueSet.elements s) in
                let set_rep = String.concat ", " vals in
                Printf.fprintf chan "        <tr><td>%s == {%s}</td></tr>\n" (string_of_term set_t) set_rep
              with Failure _ | Undefined -> ())
          | _ -> ())
        terms
    in
    print_table_header "sets";
    SortSet.iter (fun srt -> print_sets (Loc srt)) loc_sorts;
    print_sets Int;
    print_table_footer ()
  in
  (* functions and pred *)
  let output_freesyms () =
    print_table_header "predicates and functions";
    TermSet.iter 
      (function
        | (App (FreeSym _, _, (Bool as srt)) as t)
        (*| (App (FreeSym _, _, (Set _ as srt)) as t)*)
        | (App (FreeSym _, _ :: _, (Int as srt)) as t)
        | (App (FreeSym _, _ :: _, (Loc _ as srt)) as t)
        | (App (IndexOfCell, _, srt) as t) ->
            (try
              let res =
                eval model t
              in
              (*let res_t = find_term res srt in
              if t <> res_t then*)
                Printf.fprintf chan "      <tr><td>%s == %s</td></tr>\n"
                  (string_of_term t) (string_of_sorted_value srt res) (*(string_of_term res_t)*)
            with _ -> ())
        | _ -> ()
      ) terms;
    print_table_footer ()
  in
  let output_graph () =
    output_string chan "digraph Model {\n";
    SortSet.iter output_graph loc_sorts;
    output_sets ();
    output_int_vars ();
    output_freesyms ();
    output_string chan "}\n"
  in
  output_graph ()
    

      
