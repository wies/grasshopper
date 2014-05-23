(** Utility functions for manipulating SL formulas *)

open Sl
open Symbols

let mk_loc_set d =
  let tpe = Some (Form.Set Form.Loc) in
    FormUtil.mk_free_const ?srt:tpe d

let mk_loc_set_var d =
  let tpe = Some (Form.Set Form.Loc) in
    FormUtil.mk_var ?srt:tpe d

let mk_loc d =
  if (fst d = "null") then FormUtil.mk_null
  else FormUtil.mk_free_const ?srt:(Some (Form.Loc)) d

let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)
let mk_domain_var d v = FormUtil.mk_elem v (mk_loc_set_var d)
let emptyset = FormUtil.mk_empty (Some (Form.Set Form.Loc))
let empty_t domain = FormUtil.mk_eq emptyset domain
let empty domain = empty_t (mk_loc_set domain)
let empty_var domain = empty_t (mk_loc_set_var domain)

let mk_pure p = Pure p
let mk_true = mk_pure FormUtil.mk_true
let mk_false = mk_pure FormUtil.mk_false
let mk_eq a b = mk_pure (FormUtil.mk_eq a b)
let mk_not a = BoolOp(Form.Not, [a])
let mk_and a b = BoolOp (Form.And, [a; b])
let mk_or a b = BoolOp (Form.Or, [a; b])
let mk_sep_star a b = 
  match (a, b) with
  | Atom (Emp, []), _ -> b
  | _, Atom (Emp, []) -> a
  | _, _ -> SepOp (SepStar, a, b)
let mk_sep_plus a b =
  match (a, b) with
  | Atom (Emp, []), _ -> b
  | _, Atom (Emp, []) -> a
  | _, _ -> SepOp (SepPlus, a, b)
let mk_sep_wand a b = SepOp (SepWand, a, b)
let mk_atom s args = Atom (s, args)
let mk_emp = mk_atom Emp []
let mk_cell t = mk_atom Region [FormUtil.mk_setenum [t]]
let mk_region r = mk_atom Region [r]
let mk_pred p ts = mk_atom (Pred p) ts
let mk_pts f a b = 
  mk_sep_star (mk_eq (FormUtil.mk_read f a) b) (mk_cell a)
let mk_sep_star_lst args = List.fold_left mk_sep_star mk_emp args
(*let mk_prev_pts a b = mk_pred (get_symbol "ptsTo") [fprev_pts; a; b]*)
(*let mk_ls a b = mk_pred (get_symbol "lseg") [a; b]*)
(*let mk_dls a b c d = mk_pred (get_symbol "dlseg") [a; b; c; d]*)

(*
let mk_spatial_pred name args =
  match find_symbol name with
  | Some s ->
    if List.length args = s.arity then
      mk_atom (Pred (name, 0)) args
    else
      failwith (name ^ " expect " ^(string_of_int (s.arity))^
                " found (" ^(String.concat ", " (List.map Form.string_of_term args))^ ")")
  | None -> failwith ("unknown spatial predicate " ^ name)
*)

let rec map_id fct f = match f with
  | Pure p -> Pure (FormUtil.map_id fct p)
  | Atom (s, args) -> mk_atom s (List.map (FormUtil.map_id_term fct) args)
  | BoolOp (op, fs) -> BoolOp (op, List.map (map_id fct) fs)
  | SepOp (op, f1, f2) -> SepOp (op, map_id fct f1, map_id fct f2)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
    map_id get f

let subst_consts_fun subst f =
  let rec map f = 
    match f with
    | Pure g -> Pure (FormUtil.subst_consts_fun subst g)
    | Atom (p, args) -> 
        mk_atom p (List.map (FormUtil.subst_consts_fun_term subst) args)
    | BoolOp (op, fs) -> BoolOp (op, List.map map fs)
    | SepOp (op, f1, f2) -> SepOp (op, map f1, map f2)
  in
  map f

let subst_consts subst f =
  let rec map f = match f with
    | Pure g -> Pure (FormUtil.subst_consts subst g)
    | Atom (p, args) -> 
        mk_atom p (List.map (FormUtil.subst_consts_term subst) args)
    | BoolOp (op, fs) -> BoolOp (op, List.map map fs)
    | SepOp (op, f1, f2) -> SepOp (op, map f1, map f2)
  in
  map f

let subst_preds subst f =
  let rec map f =
    match f with
    | Atom (Pred p, args) -> 
        subst p args
    | BoolOp (op, fs) -> BoolOp (op, List.map map fs)
    | SepOp (op, f1, f2) -> SepOp (op, map f1, map f2)
    | f -> f
  in map f

let free_consts f =
  let rec fc acc = function
    | Pure g -> IdSet.union acc (FormUtil.free_consts g)
    | BoolOp (op, fs) -> List.fold_left fc acc fs
    | SepOp (_, f1, f2) ->  fc (fc acc f1) f2
    | Atom (p, args) -> List.fold_left FormUtil.free_consts_term_acc acc args
  in fc IdSet.empty f

let rec fold_atoms fct acc f = match f with
  | BoolOp (op, fs) -> List.fold_left (fold_atoms fct) acc fs
  | SepOp (_, f1, f2) -> fold_atoms fct (fold_atoms fct acc f1) f2
  | Atom _ -> fct acc f
  | _ -> acc

let preds f =
  let p acc = function
    | Atom (Pred pred, _) -> IdSet.add pred acc 
    | _ -> acc
  in fold_atoms p IdSet.empty f

let preds_full f =
  let p acc = function
    | Atom (Pred _, _) as a -> SlSet.add a acc 
    | _ -> acc
  in fold_atoms p SlSet.empty f

let rec get_clauses f = match f with
  | Form.BoolOp (Form.And, lst) ->  List.flatten (List.map get_clauses lst)
  (*| Form.Comment (c, f) -> List.map (fun x -> Form.Comment (c,x)) (get_clauses f)*)
  | other -> [other]

