(** {5 Models of GRASS formulas} *)

open Util
open Grass
open GrassUtil

exception Undefined

type value =
  | I of Int64.t
  | B of bool
  | ADT of ident * value list
        
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

let value_of_int i = I (Int64.of_int i)
let value_of_int64 i = I i

let value_of_bool b = B b

let bool_of_value = function
  | B b -> b
  | _ -> raise Undefined

let int_of_value = function
  | I i -> i
  | _ -> raise Undefined

let rec string_of_value = function
  | I i -> Int64.to_string i
  | B b -> string_of_bool b
  | ADT (id, vs) ->
      Printf.sprintf "%s(%s)"
        (string_of_ident id)
        (List.map string_of_value vs |>
        String.concat ", ")

let string_of_sorted_value srt v =
  let rec elim_loc = function
    | Loc srt -> elim_loc srt
    | Set srt -> Set (elim_loc srt)
    | Array srt -> Array (elim_loc srt)
    | ArrayCell srt -> ArrayCell (elim_loc srt)
    | Map (dsrts, rsrt) -> Map (List.map elim_loc dsrts, elim_loc rsrt)
    | srt -> srt
  in
  match srt with
  | Int | Bool | Adt _ -> string_of_value v
  | _ ->
      let srt_str = string_of_sort (elim_loc srt) in
      srt_str ^ "!" ^ string_of_value v

type interpretation = (value ValueListMap.t * ext_value) SortedSymbolMap.t

type ext_interpretation = ext_value SortedValueMap.t

type model =
  { mutable card: int SortMap.t;
    mutable intp: interpretation;
    mutable vals: ext_interpretation;
    sign: arity list SymbolMap.t;
  }

let empty : model = 
  { card = SortMap.empty;
    intp = SortedSymbolMap.empty;
    vals = SortedValueMap.empty;
    sign = SymbolMap.empty;
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
  if Debug.is_debug 2 then print_endline (
      "add_def: " ^ (string_of_symbol sym) ^ ": " ^ (string_of_arity arity) ^
      " => " ^ (String.concat "," (List.map string_of_value args)) ^
      " => " ^ (string_of_value v));
  let m, d = get_interp model sym arity in
  let new_m = ValueListMap.add args v m in
  { model with intp = SortedSymbolMap.add (sym, arity) (new_m, d) model.intp }

let add_default_val model sym arity v =
  if Debug.is_debug 2 then print_endline (
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
      

let find_map_value model v arg_srts res_srt = 
  try
    match SortedValueMap.find (v, Map (arg_srts, res_srt)) model.vals with
    | MapVal (m, d) -> m, d
    | Undef -> ValueListMap.empty, Undef
    | _ -> raise Undefined
  with Not_found -> raise Undefined

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
  let card =
    try SortMap.find res_srt model.card
    with Not_found -> 0
  in
  model.card <- SortMap.add res_srt (card + 1) model.card;
  (* update base value mapping *)
  let m, d = 
    try SortedSymbolMap.find (sym, arity) model.intp 
    with Not_found -> ValueListMap.empty, Undef
  in
  let new_sym_intp = ValueListMap.add args (value_of_int card) m, d in
  model.intp <- SortedSymbolMap.add (sym, arity) new_sym_intp model.intp;
  (* update extended value mapping *)
  begin
    match res_srt with
    | Map (Loc _ :: _, srt)
    | Set srt ->
        model.vals <- SortedValueMap.add (value_of_int card, res_srt) res model.vals
    | _ -> ()
  end;
  value_of_int card
            
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
      let arity = [Map ([ind_srt], srt); ind_srt], srt in
      let res = interp_symbol model Read arity [fld_val; ind_val] in
      res
  | App (Write, fld :: (_ :: _ as ind_upd), (Map (dsrts, rsrt) as srt)) ->
      let ind_upd_vals = List.map (eval model) ind_upd in
      let arity = srt :: dsrts @ [rsrt], srt in
      let fld_val = eval model fld in
      (try interp_symbol model Write arity (fld_val :: ind_upd_vals)
      with Undefined ->
        let upd_ind_vals = List.rev ind_upd_vals in
        let upd_val = List.hd upd_ind_vals in
        let ind_val = List.rev (List.tl upd_ind_vals) in
        let m, d = find_map_value model fld_val dsrts srt in
        let res = MapVal (ValueListMap.add ind_val upd_val m, d) in
        extend_interp model Write arity (fld_val :: ind_upd_vals) res)
  | App (UMinus, [t], _) ->
      I (Int64.mul Int64.minus_one (eval_int model t))
  | App (Plus as intop, [t1; t2], _)
  | App (Minus as intop, [t1; t2], _)
  | App (Mult as intop, [t1; t2], _)
  | App (Div as intop, [t1; t2], _) ->
      let f = match intop with
      | Plus -> Int64.add
      | Minus -> Int64.sub
      | Mult -> Int64.mul
      | Div -> Int64.div
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
      let i1 = eval_int model t1 in
      let i2 = eval_int model t2 in
      let c = Int64.compare i1 i2 in
      let r = match rel with
      | LtEq -> (<=) | GtEq -> (>=) | Lt -> (<) | Gt -> (>)
      | _ -> failwith "impossible"
      in 
      B (r c 0)
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
   | App (Ite, [c; t; e], _) ->
      (match eval model c with
        | B true -> eval model t
        | B false -> eval model e
        | _ -> failwith "ITE expects a boolean condition"
      )
   | App (sym, args, srt) ->
      let arg_srts, arg_vals = 
        List.split (List.map (fun arg -> sort_of arg, eval model arg) args)
      in
      let arity = arg_srts, srt in
      interp_symbol model sym arity arg_vals 

and interp_symbol model sym arity args =
  match sym with
  | Constructor id -> ADT (id, args)
  | Destructor id ->
    (match args with
    | [ADT (cons, args)] ->
      (* Find the defn of constructor cons *)
      let adt_defs =
        (match arity with
        | ([Adt(_, adt_defs)], _) -> adt_defs
        | _ -> failwith "Destructor has unexpected sort");
      in
      let cons_def =
        find_map (fun (a, adt_def) ->
          find_map (fun (id, def) ->
            if id = cons then Some def else None) adt_def)
          adt_defs
        |> Opt.lazy_get_or_else (fun () -> failwith "Couldn't find constructor")
      in
      (* Look for the position corresponding to destructor id *)
      List.combine cons_def args
      |> List.find (fun ((des_id, _), v) -> des_id = id)
      |> snd
    | _ -> failwith "Destructor applied to non-ADT args")
  | _ ->
      SortedSymbolMap.find_opt (sym, arity) model.intp |>
      Opt.map (fun (m, d) -> fun_app model (MapVal (m, d)) args) |>
      Opt.lazy_get_or_else (fun () ->
        if Debug.is_debug 2 then
          begin
            print_string "Model.interp_symbol: symbol not found '";
            print_string (string_of_symbol sym);
            print_string "' of type ";
            print_string (string_of_arity arity);
            print_endline " in:";
            SortedSymbolMap.iter (fun (s,a) _ -> print_endline ("  " ^ (string_of_symbol s) ^ ": " ^ string_of_arity a)) model.intp;
            flush_all ()
          end;
        raise Undefined)

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


(* TODO: precompute/cache this?
  We could have an eval function that takes a (value, sort) and returns the GRASS
  value. It could use the ext_interpretation to cache these?
  Right now code is repeated here and in ModelPrinting to evaluate 
  sets/functions/adts.
*)
let get_values_of_sort model srt =
  let vals = 
    SortedSymbolMap.fold (fun (sym, (arg_srts, res_srt)) (m, d) vals ->
      (* make a list of indices of arg_srts that = srt *)
      let indices =
        let indices = ref IntSet.empty in
        arg_srts |> List.iteri (fun i a -> if a = srt then indices := IntSet.add i !indices);
        !indices
      in
      (* now go through keys of m and add projection to indices to vals *)
      let vals =
        ValueListMap.fold (fun args _ vals ->
            let res = ref ValueSet.empty in
            args |> List.iteri (fun i a ->
              if IntSet.mem i indices then res := ValueSet.add a !res);
            ValueSet.union !res vals
          ) m vals
      in
      (* Then if res_srt = srt, also take d and the range of m *)
      let vals =
        if res_srt = srt 
        then 
          let map_vals = 
            ValueListMap.fold (fun _ -> ValueSet.add) m vals
          in 
          match arg_srts, d with
          | _, BaseVal v -> ValueSet.add v map_vals
          | _, _ -> map_vals
        else vals
      in
      (* If sym is a constant value of an ADT type, also check its components *)
      match d, res_srt with
      | BaseVal v, Adt (ty, adt_defs) ->
        let ty_def = List.assoc ty adt_defs in
        (try
          (match interp_symbol model sym ([], res_srt) [] with
          | ADT (cons, args) ->
            let cons_def = List.assoc cons ty_def in
            List.combine args cons_def
            |> List.fold_left
                (fun vals (v, (_, v_srt)) ->
                  if v_srt = srt then ValueSet.add v vals else vals)
                vals
          | _ -> failwith "Expected ADT value")
        with Undefined -> vals)
      | _ -> vals
      )
      model.intp ValueSet.empty
  in
  ValueSet.elements vals

let get_sorts model =
  SortedSymbolMap.fold
    (fun (_, (_, srt)) -> fun _ srts -> SortSet.add srt srts)
    model.intp SortSet.empty

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
      | (_, (arg_srts, (Map _ as srt))) -> fun _ srts ->
        let srts = 
          List.fold_left (fun srts ->
              (function | Map _ as s -> SortSet.add s srts | _ -> srts)
            ) srts arg_srts 
        in
        SortSet.add srt srts
      | _ -> fun _ srts -> srts)
    model.intp SortSet.empty

let get_loc_fld_sorts model =
  SortedSymbolMap.fold
    (function
      | (_, (_, (Map (Loc _ :: _, Loc _) as srt))) -> fun _ srts -> SortSet.add srt srts
      | _ -> fun _ srts -> srts)
    model.intp SortSet.empty
    
    
let get_symbols_of_sort model arity =
  SortedSymbolMap.fold 
    (fun (sym, arity1) _ symbols ->
      if arity1 = arity 
      then SymbolSet.add sym symbols
      else symbols)
    model.intp SymbolSet.empty

let get_constants model =
  SortedSymbolMap.fold 
    (fun (sym, arity) _ symbols ->
      match arity with
      | ([], _) -> SymbolSet.add sym symbols
      | (_, _) -> symbols)
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
    try
      if y <> x && 
      bool_of_value (interp_symbol model Btwn btwn_arity [fld; x; y; y]) &&
      (s == x || bool_of_value (interp_symbol model Btwn btwn_arity [fld; x; y; s]))
      then y else s
    with Undefined -> s)
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
        | _, Bool | _, Int (*| Write, _*) -> (fedges, dedges, init_reach)
        | _ ->
            let m1 =
              match d with
              | BaseVal v ->
                  let arg_vals =
                    List.map (function
                      | Int -> [I Int64.zero]
                      | Bool -> [B false]
                      | srt ->
                          match get_values_of_sort model srt with
                          | v1 :: v2 :: v3 :: _ -> [v1; v2; v3]
                          | vs -> vs)
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
    | Int -> mk_int64 (int_of_value v)
    | _ ->
        let sym, vs = SortedValueMap.find (v, srt) prev in
        if List.mem (v, srt) vs then failwith "fixme";
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
      | Map (dsrts, rsrt) ->
          List.for_all is_finite_set_sort dsrts && is_finite_set_sort rsrt
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
    match dom_sort srt with
    | [dsrt] ->
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
    | _ -> ()
  in
  SortSet.iter generate_sets (get_set_sorts model);
  SortSet.iter generate_fields (get_map_sorts model);
  model


(** Utils to pretty print sets and maps *)

let rec pr_sorted_value model ppf (term, srt) =
  try
    (match srt with
    | Set s ->
      let cnt = find_set_value model term s in
      pr_set model s ppf cnt
    | Map (arg_s, res_s) ->
      let map_val, def_val = find_map_value model term arg_s res_s in
      pr_map model (arg_s, res_s) ppf (map_val, def_val)
    | _ ->
      Format.fprintf ppf "%s" (string_of_sorted_value srt term))
  with Undefined ->
      Format.fprintf ppf "%s" (string_of_sorted_value srt term)

and pr_sorted_value_list model ppf svals =
  pr_list_comma (pr_sorted_value model) ppf svals

and pr_sorted_ext_value model srt ppf = function
  | BaseVal v -> pr_sorted_value model ppf (v, srt)
  | MapVal (m, d) ->
    (match srt with
    | Map (s1, s2) -> pr_map model (s1, s2) ppf (m, d)
    | _ -> failwith "Got map value with non-map sort")
  | SetVal v ->
    (match srt with
    | Set srt -> pr_set model srt ppf v
    | _ -> failwith "Got set value with non-set sort")
  | TermVal _
  | FormVal _
  | Undef -> Format.fprintf ppf "Undef"

and pr_map model (arg_s, res_s) ppf (map, def_val) =
  let pr_map_elem ppf (args, v) = 
    Format.fprintf ppf "%a: %a"
      (pr_sorted_value_list model) (List.combine args arg_s)
      (pr_sorted_value model) (v, res_s)
  in
  Format.fprintf ppf "{@[<hv 2>%a@]}(__default: %a)"
    (pr_list_comma pr_map_elem) (ValueListMap.bindings map)
    (pr_sorted_ext_value model res_s) def_val

and pr_set model srt ppf vs =
  Format.fprintf ppf "{@[<hv 2>%a@]}" (pr_sorted_value_list model)
    (ValueSet.elements vs |> List.map (fun v -> (v, srt)))

let string_of_eval model srt v =
  string_of_format (pr_sorted_value model) (v, srt)