(** {5 Models of GRASS formulas} *)

open Util
open Grass
open GrassUtil

let value_of_int srt i = mk_app srt (Value (Int64.of_int i)) []
let value_of_int64 srt i = mk_app srt (Value i) []

let bool_opt_of_value = function
  | App (BoolConst b, _, _) -> Some b
  | _ -> None

let bool_of_value = function
  | App (BoolConst b, _, _) -> b
  | _ -> false

        
let int_opt_of_value = function
  | App (IntConst i, _, _) -> Some i
  | _ -> None

let string_of_value v = string_of_term v 

type definition = (ident * sort) list * term
    
type interpretation = definition SortedSymbolMap.t

type model =
  { mutable univ: TermSet.t SortMap.t;
    mutable intp: interpretation;
    sign: arity list SymbolMap.t;
    cache: (sorted_ident * term list, term) Hashtbl.t
  }

let empty : model = 
  { univ = SortMap.empty;
    intp = SortedSymbolMap.empty;
    sign = SymbolMap.empty;
    cache = Hashtbl.create 1024
  }

(*let get_arity model sym = SymbolMap.find sym m*)

let get_values_of_sort model srt =
  SortMap.find_opt srt model.univ |> Opt.get_or_else TermSet.empty
    
let add_univ model t =
  let srt = sort_of t in
  let old_univ = get_values_of_sort model srt in
  let new_univ = TermSet.add t old_univ in
  model.univ <- SortMap.add srt new_univ model.univ

let add_interp model sym arity args def =
  { model with intp = SortedSymbolMap.add (sym, arity) (args, def) model.intp }

let get_interp model sym arity =
  SortedSymbolMap.find (sym, arity) model.intp

let get_result_sort model sym arg_srts =
  SortedSymbolMap.fold 
    (fun (sym1, (arg_srts1, res_srt1)) _ srt_opt ->
      if sym1 = sym && arg_srts = arg_srts1 then Some res_srt1 else srt_opt)
    model.intp None

let equal model v1 v2 srt =
  v1 = v2 

let extend_interp model sym (arity: arity) args res =
  (* update interpretation *)
  let params, def = get_interp model sym arity in
  let new_def =
    let cond =
      List.map2 (fun (id, srt) a -> mk_eq_term (mk_var srt id) a) params args |>
      mk_app Bool AndTerm
    in
    mk_ite cond res def
  in
  model.intp <- SortedSymbolMap.add (sym, arity) (params, new_def) model.intp;
  model
  
let rec eval model = function
  | Var (id, srt) -> 
      interp_symbol model (FreeSym id) ([], srt) []
  | App ((IntConst _ | BoolConst _ | Value _), [], _) as t -> t
  | App (Read, [fld; ind], srt) -> 
      let fld_val = eval model fld in
      let ind_val = eval model ind in
      let ind_srt = sort_of ind in
      let arity = [Map ([ind_srt], srt); ind_srt], srt in
      interp_symbol model Read arity [fld_val; ind_val]
  | App (Write, fld :: (_ :: _ as ind_upd), (Map (dsrts, rsrt) as srt)) ->
      let ind_upd_vals = List.map (eval model) ind_upd in
      let arity = srt :: dsrts @ [rsrt], srt in
      let fld_val = eval model fld in
      interp_symbol model Write arity (fld_val :: ind_upd_vals)
  | App (UMinus, [t], _) ->
      eval_int model t |>
      Opt.map (fun i -> mk_int64 (Int64.mul Int64.minus_one i)) |>
      Opt.get_or_else (mk_undefined Int)
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
      in
      eval_int model t1 |> Opt.flat_map (fun
        i1 -> eval_int model t2 |> Opt.map (fun
        i2 -> mk_int64 (f i1 i2))) |>
      Opt.get_or_else (mk_undefined Int)
  | App (Eq, [t1; t2], _) ->
      let res = equal model (eval model t1) (eval model t2) (sort_of t1) in
      mk_bool_term res
  | App (LtEq as rel, [t1; t2], _)
  | App (GtEq as rel, [t1; t2], _)
  | App (Lt as rel, [t1; t2], _)
  | App (Gt as rel, [t1; t2], _) ->
      eval_int model t1 |> Opt.flat_map (fun
        i1 -> eval_int model t2 |> Opt.map (fun
        i2 -> 
          let c = Int64.compare i1 i2 in
          let r = match rel with
          | LtEq -> (<=) | GtEq -> (>=) | Lt -> (<) | Gt -> (>)
          | _ -> failwith "impossible"
          in 
          mk_bool_term (r c 0))) |>
      Opt.get_or_else (mk_undefined Bool)
   | App (Ite, [c; t; e], _) ->
      (match eval model c |> bool_opt_of_value with
        | Some true -> eval model t
        | Some false -> eval model e
        | None -> mk_undefined (sort_of e)
      )
   | App (AndTerm, f1 :: fs, _) ->
       (match eval model f1 |> bool_opt_of_value with
       | Some true -> eval model (App (AndTerm, fs, Bool))
       | Some false -> mk_false_term
       | None -> mk_undefined Bool)
   | App (AndTerm, [], _) -> mk_true_term
   | App (OrTerm, f1 :: fs, _) ->
       (match eval model f1 |> bool_opt_of_value with
       | Some false -> eval model (App (OrTerm, fs, Bool))
       | Some true -> mk_true_term
       | None -> mk_undefined Bool)
   | App (OrTerm, [], _) -> mk_false_term
   | App (sym, args, srt) ->
      let arg_srts, arg_vals = 
        List.split (List.map (fun arg -> sort_of arg, eval model arg) args)
      in
      let arity = arg_srts, srt in
      interp_symbol model sym arity arg_vals 

and interp_symbol model sym arity args =
  match sym with
  | Constructor id -> mk_constr (snd arity) id args
  | Destructor id ->
    (match args with
    | [App (Constructor cons, args, _)] ->
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
      Opt.map (fun (ids, t) ->
        let model1 = 
          List.fold_left2 
            (fun model1 (id, srt) arg -> 
              add_interp model1 (FreeSym id) ([], srt) [] arg)
            model ids args
        in
        eval model1 t) |>
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
        mk_undefined (snd arity))

and eval_int model t =
  eval model t |> int_opt_of_value

and eval_bool model t =
  eval model t |> bool_opt_of_value 

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
  | Atom (t, _) -> eval_bool model t
  | Binder (b, [], f, _) -> eval_form model f
  | _ -> None

let is_defined model sym arity args =
  match interp_symbol model sym arity args with
  | App (Undefined, _, _) -> true
  | _ -> false

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
  TermSet.fold (fun y s ->
    if y <> x && 
      bool_of_value (interp_symbol model Btwn btwn_arity [fld; x; y; y]) &&
      (s == x || bool_of_value (interp_symbol model Btwn btwn_arity [fld; x; y; s]))
    then y else s)
    locs x 
      
let complete model =
  let locs srt = get_values_of_sort model (Loc srt) in
  let loc_flds srt = get_values_of_sort model (loc_field_sort srt) in
  let flds srt =
    let loc_srt = Loc srt in
    let null = interp_symbol model Null ([], loc_srt) [] in
    let btwn_arity = [loc_field_sort srt; loc_srt; loc_srt; loc_srt], Bool in
    TermSet.filter (fun f ->
      let is_reach_fld = interp_symbol model Btwn btwn_arity [f; null; null; null] in
      bool_of_value is_reach_fld)
      (loc_flds srt)
  in
  let loc_srts = get_loc_sorts model in
  let new_model =
    SortSet.fold (fun srt model ->
      TermSet.fold
        (fun fld new_model ->
          TermSet.fold
            (fun arg new_model ->
              let res = succ model srt fld arg in
              let read_arity = [loc_field_sort srt; Loc srt], Loc srt in
              extend_interp new_model Read read_arity [fld; arg] res)
            (locs srt) new_model)
        (flds srt) model)
      loc_srts model
  in
  new_model


let get_defs model sym arity =
  let params, def = SortedSymbolMap.find (sym, arity) model.intp in
  let add id arg args_list =
    List.map (IdMap.add id arg) args_list
  in
  let rec ea args_list = function
    | App (AndTerm, ts, _) ->
        List.fold_left ea args_list ts
    | App (OrTerm, ts, _) ->
        Util.flat_map (ea args_list) ts
    | App (Ite, [c; t; e], Bool) ->
        ea args_list (App (OrTerm, [App (AndTerm, [c; t], Bool); e], Bool))
    | App (Eq, [Var (id, _); arg], _) ->
        add id arg args_list
    | App (Eq, [App (Ite, [c; t; e], _); App (Value _, _, _) as v], _) ->
        ea args_list (App (Ite, [c; App (Eq, [t; v], Bool); App (Eq, [e; v], Bool)], Bool))
    | App (Eq, [App (Value i1, _, _); App (Value i2, _, _)], _) when i1 <> i2 -> []
    | _ -> args_list
  in
  let rec get_defs defs arg_lists = function
    | App (Ite, [c; t; e], _) ->
        let defs_e = get_defs defs arg_lists e in
        get_defs defs_e (ea arg_lists c) t
    | App (Value _, _, _) as v ->
        List.map (fun args -> args, v) arg_lists @ defs
    | App ((OrTerm | AndTerm), _, _) as t ->
        let arg_lists = ea arg_lists t in
        List.map (fun args -> args, mk_true_term) arg_lists @ defs
    | _ -> defs
  in
  let defs = get_defs [] [IdMap.empty] def in
  let process_def args v =
    if IdMap.is_empty args then [], Some v else
    let ts =
      List.fold_right (fun (id, _) ts ->
        IdMap.find_opt id args
        |> Opt.map (fun t -> t :: ts)
        |> Opt.get_or_else [])
        params []
    in
    if List.length ts <> List.length params then [], None
    else [ts, v], None
  in
  List.fold_left (fun (defs, default) (args, v) ->
    let defs1, default1 = process_def args v in
    defs1 @ defs, Opt.lazy_or_else (fun () -> default1) default)
    ([], None) defs
  
module PQ = PrioQueue.Make
    (struct
      type t = term
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
      (fun (sym, (arg_srts, res_srt)) def (fedges, dedges, init_reach) ->
        match sym, res_srt with
        | _, Bool | _, Int (*| Write, _*) -> (fedges, dedges, init_reach)
        | _ ->
            let m, _ = get_defs model sym (arg_srts, res_srt) in
            let m1 =
              if m <> []
              then TermListMap.of_seq (List.to_seq m)
              else
              let arg_vals =
                List.map (function
                  | Int -> [mk_int 0]
                  | Bool -> [mk_false_term]
                  | srt ->
                      match get_values_of_sort model srt |> TermSet.elements with
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
                if TermListMap.mem args m then m
                else
                  let v = interp_symbol model sym (arg_srts, res_srt) args in
                  TermListMap.add args v m)
                TermListMap.empty arg_product
            in
            TermListMap.fold
              (fun args v (fedges, dedges, init_reach) ->
                let s = args in
                let t = v in
                let es =
                  TermListMap.find_opt s fedges |>
                  Opt.get_or_else []
                in
                let fedges1 = TermListMap.add s ((sym, t) :: es) fedges in
                let init_reach1 = TermListMap.add s (List.length s) init_reach in
                let init_reach2 = TermListMap.add [t] 1 init_reach1 in
                let dedges1, init_reach3 =
                  List.fold_left
                    (fun (dedges1, init_reach3) z ->
                      let es =
                        TermMap.find_opt z dedges1 |>
                        Opt.get_or_else []
                      in
                      TermMap.add z (s :: es) dedges1,
                      match sort_of z with
                      | Bool | Int ->
                          TermListMap.add [z] 0 init_reach3
                      | _ -> init_reach3
                    )
                    (dedges, init_reach2) s
                in
                fedges1, dedges1, init_reach3
              )
              m1 (fedges, dedges, init_reach)
      )
      model.intp (TermListMap.empty, TermMap.empty, TermListMap.empty)
  in
  (* initialize remaining data structures *)
  let init_queue, init_reach, init_dist, init_prev =
    SortedSymbolMap.fold 
      (fun (sym, (arg_srts, res_srt)) def (init_queue, init_reach, init_dist, init_prev) ->
        let add () =
          let x = interp_symbol model sym (arg_srts, res_srt) [] in
          PQ.insert x 0 init_queue,
          TermListMap.add [x] 0 init_reach,
          TermMap.add x 0 init_dist,
          TermMap.add x (sym, []) init_prev
        in
        match arg_srts with
        | [] -> add ()
        | _ ->
            init_queue, init_reach, init_dist, init_prev)
      model.intp (PQ.empty, init_reach, TermMap.empty, TermMap.empty)
  in
  (* auxiliary function for shortest path algorithm *)
  let scan t d_t (reach, dist, prev, queue) (sym, x) =
    let d_t_x = d_t + 1 in
    let reach_x = TermListMap.find [x] reach in
    if reach_x = 1 then
      TermListMap.add [x] 0 reach,
      TermMap.add x d_t_x dist,
      TermMap.add x (sym, t) prev,
      PQ.insert x d_t_x queue
    else if d_t_x < TermMap.find x dist then
      reach, 
      TermMap.add x d_t_x dist,
      TermMap.add x (sym, t) prev,
      PQ.adjust (fun _ -> d_t_x) x queue
    else
      reach, dist, prev, queue
  in
  (* shortest path algorithm *)
  let rec shortest_paths reach dist prev queue =
    if PQ.is_empty queue then prev else
    let t, d_t, queue = PQ.extract_min queue in
    let get_fedges t =
      TermListMap.find_opt t fedges |>
      Opt.get_or_else []
    in
    let reach, dist, prev, queue =
      List.fold_left (scan [t] d_t) (reach, dist, prev, queue) (get_fedges [t])
    in
    let dedges_t =
      TermMap.find_opt t dedges |>
      Opt.get_or_else []
    in
    let reach, dist, prev, queue =
      List.fold_left
        (fun (reach, dist, prev, queue) z ->
          let reach_z = TermListMap.find z reach - 1 in
          let reach1 = TermListMap.add z reach_z reach in
          if reach_z = 0 then
            let d_z =
              List.fold_left
                (fun d_z x ->
                  let d_x = TermMap.find_opt x dist |> Opt.get_or_else 0 in
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
  let rec find v =
    let srt = sort_of v in
    match srt with 
    | Bool | Int -> v
    | _ ->
        let sym, vs = TermMap.find v prev in
        if List.mem v vs then failwith "fixme";
        let args = List.map find vs in
        mk_app srt sym args
  in find

let get_set_of_value model s =
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
  let elem_srt = element_sort_of_set s in
  if not @@ is_finite_set_sort elem_srt then s else
  let vals = get_values_of_sort model elem_srt in
  let vset =
    TermSet.fold
      (fun e vset ->
        let e_in_s = interp_symbol model Elem ([elem_srt; Set elem_srt], Bool) [e; s] in
        if bool_of_value e_in_s 
        then e :: vset
        else vset)
      vals []
  in
  mk_app (Set elem_srt) SetEnum vset

let get_map_of_value model m =
  let srt = sort_of m in
  match dom_sort srt with
  | [dsrt] ->
      let rsrt = range_sort srt in
      let fmap =
        TermSet.fold (fun e fmap ->
          let f_of_e = interp_symbol model Read ([srt; dsrt], rsrt) [m; e] in
          ([e], f_of_e) :: fmap)
          (get_values_of_sort model dsrt)
          []
      in
      Either.First fmap
  | _ -> Either.Second m


(** Utils to pretty print sets and maps *)

let rec pr_value model ppf term =
  match sort_of term with
  | Set _ ->
      let set = get_set_of_value model term in
      pr_term ppf set
  | Map (arg_s, res_s) ->
      get_map_of_value model term |>
      Either.fold (pr_map (fun ppf _ -> Format.fprintf ppf ",@ ") ppf) (pr_term ppf)
  | _ ->
      pr_term ppf term
          
and pr_value_list model ppf svals =
  pr_list_comma (pr_value model) ppf svals

and pr_map sep ppf ts =
  let pr_map_elem ppf (arg, res) = 
    Format.fprintf ppf "%a -> %a"
      pr_term_list arg
      pr_term res
  in
  Format.fprintf ppf "{@[<hv 2>%a@]}"
    (pr_list 0 sep (fun _ -> pr_map_elem)) ts

let string_of_value model v =
  string_of_format (pr_value model) v
