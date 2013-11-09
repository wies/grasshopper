open Form
open Util

(* TODO try to fill in the types of partially typed formula.
 * use some kind of most general unifier (simple backtrack-free version should be enough)
 *)

type my_sort =
  | TBool | TLoc | TInt
  | TFree of ident
  | TSet of my_sort 
  | TFld of my_sort
  | TVar of int
  | TStar of my_sort (* repeated args *)
  | TFun of my_sort list * my_sort

let rec my_sort_to_string t = match t with
  | TBool -> "bool"
  | TLoc -> "loc"
  | TInt -> "Int"
  | TFree id -> str_of_ident id
  | TSet s -> "Set("^(my_sort_to_string s)^")"
  | TFld s -> "Fld("^(my_sort_to_string s)^")"
  | TVar i -> "V"^(string_of_int i)
  | TStar s -> (my_sort_to_string s)^"*"
  | TFun (args, ret) -> String.concat " -> " (List.map my_sort_to_string (args @ [ret]))

let rec to_my_sort t = match t with
  | Bool  -> TBool
  | Loc   -> TLoc
  | Int   -> TInt
  | FreeSrt id -> TFree id
  | Set s -> TSet (to_my_sort s)
  | Fld s -> TFld (to_my_sort s)

let to_sort ?what s =
  let rec process s = 
    match s with
    | TBool -> Bool
    | TLoc -> Loc
    | TInt -> Int
    | TFree id -> FreeSrt id
    | TSet s -> Set (process s)
    | TFld s -> Fld (process s)
    | TVar _ ->
      Debug.notice ("converting " ^(my_sort_to_string s)^ " to Loc.\n");
      Loc
    | TStar _ | TFun _ -> failwith ("cannot convert '" ^(my_sort_to_string s)^"' to basic sort")
  in
  try
    process s
  with Failure f ->
    begin
      match what with
      | Some t -> failwith (f ^ " in  "^t)
      | None -> failwith f
    end

module TpeMap = Map.Make(struct
    type t = my_sort
    let compare = compare
  end)

module TpeSet = Set.Make(struct
    type t = my_sort
    let compare = compare
  end)

(* bottom-up *)
let subst map tpe =
  let sub t =
    try TpeMap.find t map with Not_found -> t
  in
  let rec process t = match t with
    | TSet t -> sub (TSet (process t))
    | TFld t -> sub (TFld (process t))
    | TStar t -> sub (TStar (process t))
    | TFun (args, ret) -> sub (TFun (List.map process args, process ret))
    | other -> sub other
  in
    process tpe

(* top-down *)
let subst_td map tpe =
  let sub t =
    try TpeMap.find t map with Not_found -> t
  in
  let rec process t = match sub t with
    | TSet t -> TSet (process t)
    | TFld t -> TFld (process t)
    | TStar t -> TStar (process t)
    | TFun (args, ret) -> TFun (List.map process args, process ret)
    | other -> other
  in
    process tpe

let args_type tpe args = match tpe with
  | TFun (ts, _) ->
    let rec process t a = match (t, a) with
      | ([TStar tpe], y::ys) -> tpe :: (process t ys)
      | ((TStar tpe)::xs, y::ys) -> failwith "TStar is not the last type of a sequence"
      | (x::xs, y::ys) -> x :: (process xs ys)
      | ([], []) | ([TStar _], []) -> []
      | ([], _) -> failwith "too many arguments"
      | (_, []) -> failwith "not enough arguments"
    in
      process ts args
  | other ->
    assert (args = []);
    []

let return_type tpe = match tpe with
  | TFun (_, r) -> r
  | TStar t -> t
  | other -> other

let rec type_var tpe = match tpe with
  | TVar _ -> TpeSet.singleton tpe
  | TSet t | TFld t | TStar t -> type_var t
  | TFun (args, ret) ->
    List.fold_left
      (fun acc t -> TpeSet.union acc (type_var t))
      (type_var ret)
      args
  | other -> TpeSet.empty

let fresh_param =
  let cnt = ref 0 in
    (fun () ->
      cnt := !cnt + 1;
      TVar !cnt
    )

let fresh_type t =
  let vars = type_var t in
  let map =
    TpeSet.fold
      (fun v acc -> TpeMap.add v (fresh_param ()) acc)
      vars
      TpeMap.empty
  in
    subst map t

let param1 = fresh_param ()
let param2 = fresh_param ()

(* This does not include BoolConst, IntConst, and FreeSym *)
let symbol_types =
  List.fold_left
    (fun acc (k, v) -> SymbolMap.add k v acc)
    SymbolMap.empty
    [(Null, TLoc);
     (Read, TFun ([TFld param1; TLoc], param1));
     (Write, TFun ([TFld param1; TLoc; param1], TFld param1) );
     (EntPnt, TFun ([TFld TLoc; TSet TLoc; TLoc], TLoc));
     (UMinus, TFun ([TInt], TInt) );
     (Plus, TFun ([TStar TInt], TInt));
     (Minus, TFun ([TInt; TInt], TInt) );
     (Mult, TFun ([TStar TInt], TInt));
     (Div, TFun ([TInt; TInt], TInt));
     (Empty, TSet param1);
     (SetEnum, TFun ([TStar param1], TSet param1));
     (Union, TFun ([TStar (TSet param1)], TSet param1));
     (Inter, TFun ([TStar (TSet param1)], TSet param1));
     (Diff, TFun ([TSet param1; TSet param1], TSet param1));
     (Eq, TFun ([param1; param1], TBool));
     (LtEq, TFun ([TInt; TInt], TBool));
     (GtEq, TFun ([TInt; TInt], TBool));
     (Lt, TFun ([TInt; TInt], TBool));
     (Gt, TFun ([TInt; TInt], TBool));
     (Btwn, TFun ([TFld TLoc; TLoc; TLoc; TLoc], TBool));
     (Frame, TFun ([TSet TLoc; TSet TLoc; TFld param1; TFld param1], TBool));
     (Elem, TFun ([param1; TSet param1], TBool));
     (SubsetEq, TFun ([TSet param1; TSet param1], TBool))
    ]

(*********************************************************)

(* Due to polymorphism we need to uniquely identify symbols.
 * Thus we will replace everything by free symbols and keep track of what is what.
 *)
let preprocess f =
  let symbolify_list fct lst =
    let rec process lst = match lst with
      | x :: xs ->
        let (a1,b1,c1) = fct x in
        let (a2,b2,c2) = process xs in
          (a1 @ a2, b1 @ b2, c1 :: c2)
      | [] -> ([], [], [])
    in
      process lst
  in
  let mk_tpe args ret_opt =
    let params = List.map (fun _ -> fresh_param ()) args in
    let ret = match ret_opt with Some t -> to_my_sort t | None -> fresh_param () in
    if (args <> []) then TFun (params, ret)
    else ret
  in
  let rec symbolify f = match f with
    | Var _ as v -> ([], [], v)
    | App (sym, ts, srt_opt) ->
      begin
        let (a, b, args) = symbolify_list symbolify ts in
        let new_sym, tpe = match sym with 
          | BoolConst _ -> (sym, TBool)
          | IntConst _ -> (sym, TInt)
          | FreeSym _ -> (sym, mk_tpe args srt_opt)
          | sym ->
            let tpe = fresh_type (SymbolMap.find sym symbol_types) in
              if not (TpeSet.is_empty (type_var tpe)) then
                begin
                  let id = FormUtil.fresh_ident "typing" in
                    (FreeSym id, tpe)
                end
              else
                (sym, tpe)
        in
        let args_t = args_type tpe args in
        let ret_t = match srt_opt with
          | Some s -> to_my_sort s
          | None -> return_type tpe
        in
        let t = match args_t with
          | [] -> ret_t
          | xs -> TFun (args_t, ret_t)
        in
          ( (new_sym, sym) :: a,
            (new_sym, t) :: b,
            App (new_sym, args, srt_opt) )
      end
  in
  let rec symbolify2 f = match f with
    | Atom t -> 
      let (a, b, c) = symbolify t in
        (a, b, Atom c)
    | BoolOp (op, lst) ->
      let (a, b, lst2) = symbolify_list symbolify2 lst in
        (a, b, BoolOp (op, lst2))
    | Binder (bnd, vars, form, annot) ->
      let (a, b, c) = symbolify2 form in
        (a, b, Binder (bnd, vars, c, annot))
  in
  let (defs, defs_t, f) = symbolify2 f in
    if false && Debug.is_debug () then
      begin
        print_endline "symbols defs:";
        List.iter (fun (s1, s2) -> print_endline ("  " ^(str_of_symbol s1) ^ " -> " ^ (str_of_symbol s2)) ) defs;
        print_endline "symbols types:";
        List.iter (fun (s, t) -> print_endline ("  " ^(str_of_symbol s) ^ " -> " ^ (my_sort_to_string t)) ) defs_t;
        print_endline "processed formula:";
        print_endline (string_of_form f)
      end;
    let map_d = List.fold_left (fun acc (k,v) -> SymbolMap.add k v acc) SymbolMap.empty defs in
    let map_t = List.fold_left (fun acc (k,v) -> SymbolMap.add k v acc) SymbolMap.empty defs_t in
      (map_d, map_t, f)

(* typing equations *)
let equations env f =
  let rec deal_with_the_args tpe args ret_opt =
    let init_eqs = match ret_opt with
      | Some t -> [(return_type tpe, to_my_sort t)]
      | None -> []
    in
    let ats = args_type tpe args in
    let args_eqs =
      List.map2
        (fun t arg ->
          let (tpe, eq) = process_term arg in
            (t, tpe) :: eq
        )
        ats
        args
    in
      init_eqs @ (List.flatten args_eqs)
  and process_term t = match t with
    | Var (id, Some (tpe)) -> (to_my_sort tpe, [])
    | Var (id, None) -> failwith "the Var should be typed (for the moment)."
    | App (sym, ts, srt_opt) ->
      let tpe = SymbolMap.find sym env in
      let eqs = deal_with_the_args tpe ts srt_opt in
        (return_type tpe, eqs)
  in
  let rec process_form f = match f with
    | Atom t -> 
      let (t, eqs) = process_term t in
        (t, TBool) :: eqs
    | BoolOp (_, lst) -> Util.flat_map process_form lst
    | Binder (_, _, form, _) -> process_form form
  in
  let eqs = process_form f in
    if false && Debug.is_debug () then
      begin
        print_endline "eqs:";
        List.iter
          (fun (t1, t2) ->
            if t1 <> t2 then
              print_endline ("  " ^(my_sort_to_string t1) ^ " = " ^ (my_sort_to_string t2)) 
          )
          eqs
      end;
    eqs

(* solve the equations using unification *)
let unify eqs =
  let update_subst subst t1 t2 =
    TpeMap.add t1 t2 subst
  in
  let rec process map t1 t2 = match (subst_td map t1, subst_td map t2) with
    | (x, y) when x = y -> map 
    | ((TVar _ as x), y) | (y, (TVar _ as x)) ->
      assert (not (TpeSet.mem x (type_var y)));
      update_subst map x y
    | (TSet t3, TSet t4) -> process map t3 t4
    | (TFld t3, TFld t4) -> process map t3 t4
    | (TStar t3, TStar t4) | (TStar t3, t4) | (t4, TStar t3) -> process map t3 t4
    | (TFun (a1, r1), TFun (a2, r2)) ->
      List.fold_left2 process (process map r1 r2) a1 a2
    | (t1, t2) -> failwith ("ill-typed: " ^ (my_sort_to_string t1) ^ " = " ^ (my_sort_to_string t2))
  in
  let mgu = List.fold_left (fun acc (t1, t2) -> process acc t1 t2) TpeMap.empty eqs in
    mgu

let fill_type defs env mgu f =
  let env = SymbolMap.map (subst_td mgu) env in
  let compare t srt_opt = match srt_opt with
    | Some t2 -> assert (t = t2); t
    | None -> t
  in
  let rec fill_term t = match t with
    | Var _ as v -> v
    | App (sym, ts, srt_opt) ->
      begin
        let ts = List.map fill_term ts in
        let orignal_sym = SymbolMap.find sym defs in
        let srt = SymbolMap.find sym env in
        let ret = to_sort (return_type srt) ~what:(str_of_symbol orignal_sym) in
          App (orignal_sym, ts, Some (compare ret srt_opt))
      end
  in
    FormUtil.map_terms fill_term f

let typing f =
  let (defs, env, f) = preprocess f in
  let eqs = equations env f in
  let mgu = unify eqs in
    fill_type defs env mgu f
