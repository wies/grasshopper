(** Utility functions for manipulating SL formulas *)

open Sl
open Symbols

let pos_of_sl_form = function
  | Pure (_, pos)
  | Atom (_, _, pos)
  | SepOp (_, _, _, pos)
  | BoolOp (_, _, pos) 
  | Binder (_, _, _, pos) -> pos

let mk_loc_set d =
  let srt = Form.Set Form.Loc in
    FormUtil.mk_free_const srt d

let mk_loc_set_var d =
  let srt = Form.Set Form.Loc in
    FormUtil.mk_var srt d

let mk_loc d =
  if fst d = "null" then FormUtil.mk_null
  else FormUtil.mk_free_const (Form.Loc) d

let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)
let mk_domain_var d v = FormUtil.mk_elem v (mk_loc_set_var d)
let emptyset = FormUtil.mk_empty (Form.Set Form.Loc)
let empty_t domain = FormUtil.mk_eq emptyset domain
let empty domain = empty_t (mk_loc_set domain)
let empty_var domain = empty_t (mk_loc_set_var domain)

let mk_pure ?pos p = Pure (p, pos)
let mk_true = mk_pure FormUtil.mk_true
let mk_false = mk_pure FormUtil.mk_false
let mk_eq ?pos a b = mk_pure ?pos:pos (FormUtil.mk_eq a b)
let mk_not ?pos a = BoolOp(Form.Not, [a], pos)
let mk_and ?pos a b = BoolOp (Form.And, [a; b], pos)
let mk_or ?pos a b = BoolOp (Form.Or, [a; b], pos)
let mk_sep_star ?pos a b = 
  match (a, b) with
  | Atom (Emp, [], _), _ -> b
  | _, Atom (Emp, [], _) -> a
  | _, _ -> SepOp (SepStar, a, b, pos)
let mk_sep_plus ?pos a b =
  match (a, b) with
  | Atom (Emp, [], _), _ -> b
  | _, Atom (Emp, [], _) -> a
  | _, _ -> SepOp (SepPlus, a, b, pos)
let mk_sep_incl ?pos a b = SepOp (SepIncl, a, b, pos)
let mk_atom ?pos s args = Atom (s, args, pos)
let mk_emp = mk_atom Emp []
let mk_cell ?pos t = mk_atom ?pos:pos Region [FormUtil.mk_setenum [t]]
let mk_region ?pos r = mk_atom ?pos:pos Region [r]
let mk_pred ?pos p ts = mk_atom ?pos:pos (Pred p) ts
let mk_pts ?pos f a b = 
  mk_sep_star ?pos:pos (mk_eq ?pos:pos (FormUtil.mk_read f a) b) (mk_cell ?pos:pos a)
let mk_sep_star_lst args = List.fold_left mk_sep_star mk_emp args
let mk_exists ?pos vs f = Binder (Form.Exists, vs, f, pos)
let mk_forall ?pos vs f = Binder (Form.Forall, vs, f, pos)

let rec map_id fct f = match f with
  | Pure (p, pos) -> Pure (FormUtil.map_id fct p, pos)
  | Atom (s, args, pos) -> mk_atom ?pos:pos s (List.map (FormUtil.map_id_term fct) args)
  | BoolOp (op, fs, pos) -> BoolOp (op, List.map (map_id fct) fs, pos)
  | SepOp (op, f1, f2, pos) -> SepOp (op, map_id fct f1, map_id fct f2, pos)
  | Binder (b, vs, f, pos) -> Binder (b, vs, map_id fct f, pos)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
  map_id get f

let subst_consts_fun subst f =
  let rec map f = 
    match f with
    | Pure (g, pos) -> Pure (FormUtil.subst_consts_fun subst g, pos)
    | Atom (p, args, pos) -> 
        mk_atom ?pos:pos p (List.map (FormUtil.subst_consts_fun_term subst) args)
    | BoolOp (op, fs, pos) -> BoolOp (op, List.map map fs, pos)
    | SepOp (op, f1, f2, pos) -> SepOp (op, map f1, map f2, pos)
    | Binder (b, vs, f, pos) -> Binder (b, vs, map f, pos)
  in
  map f

let subst_consts subst f =
  let rec map f = match f with
    | Pure (g, pos) -> Pure (FormUtil.subst_consts subst g, pos)
    | Atom (p, args, pos) -> 
        mk_atom ?pos:pos p (List.map (FormUtil.subst_consts_term subst) args)
    | BoolOp (op, fs, pos) -> BoolOp (op, List.map map fs, pos)
    | SepOp (op, f1, f2, pos) -> SepOp (op, map f1, map f2, pos)
    | Binder (b, vs, f, pos) -> Binder (b, vs, map f, pos)
  in
  map f

let subst_preds subst f =
  let rec map f =
    match f with
    | Atom (Pred p, args, pos) -> 
        subst p args pos
    | BoolOp (op, fs, pos) -> BoolOp (op, List.map map fs, pos)
    | SepOp (op, f1, f2, pos) -> SepOp (op, map f1, map f2, pos)
    | Binder (b, vs, f, pos) -> Binder (b, vs, map f, pos)
    | f -> f
  in map f

let free_consts f =
  let rec fc acc = function
    | Pure (g, _) -> IdSet.union acc (FormUtil.free_consts g)
    | Atom (p, args, _) -> List.fold_left FormUtil.free_consts_term_acc acc args
    | BoolOp (op, fs, _) -> List.fold_left fc acc fs
    | SepOp (_, f1, f2, _) ->  fc (fc acc f1) f2
    | Binder (b, vs, f, _) -> fc acc f
  in fc IdSet.empty f

let rec fold_atoms fct acc f = 
  match f with
  | Binder (b, vs, f, _) -> fold_atoms fct acc f
  | BoolOp (op, fs, _) -> List.fold_left (fold_atoms fct) acc fs
  | SepOp (_, f1, f2, _) -> fold_atoms fct (fold_atoms fct acc f1) f2
  | Atom _ -> fct acc f
  | _ -> acc

let preds f =
  let p acc = function
    | Atom (Pred pred, _, _) -> IdSet.add pred acc 
    | _ -> acc
  in fold_atoms p IdSet.empty f

let preds_full f =
  let p acc = function
    | Atom (Pred _, _, _) as a -> SlSet.add a acc 
    | _ -> acc
  in fold_atoms p SlSet.empty f

let rec get_clauses f = match f with
  | Form.BoolOp (Form.And, lst) ->  List.flatten (List.map get_clauses lst)
  | other -> [other]

let prenex_form f = 
  let combine acc bvs f =
    let acc_vs = 
      List.fold_left 
        (fun vs (_, srt_vs') -> 
          let vs' = List.rev_map fst srt_vs' in
          IdSet.union (FormUtil.id_set_of_list vs') vs) 
        IdSet.empty acc 
    in
    let bvs1, f1 = List.fold_right 
        (fun (b, vs) (bvs1, f1) -> 
          let vs1, subst = 
            List.fold_right 
              (fun (v, srt) (vs1, subst) ->
                if IdSet.mem v acc_vs then
                  let v' = FormUtil.fresh_ident (FormUtil.name v) in
                  (v', srt) :: vs1, IdMap.add v v' subst
                else (v, srt) :: vs1, subst
              )
              vs ([], IdMap.empty)
          in
          (b, vs1) :: bvs1, subst_id subst f1
        )
        bvs ([], f)
    in 
    bvs1 @ acc, f1
  in
  let dualize bvs =
    List.map (fun (b, vs) -> (FormUtil.dualize_binder b, vs)) bvs
  in
  let rec pf = function
    | BoolOp (op, fs, pos) -> 
        let bvs1, fs1 = pf_fs fs in
        let bvs2 = match op with
        | Form.Not -> dualize bvs1 
        | _ -> bvs1 
        in
        bvs2, BoolOp (op, fs1, pos)
    | SepOp (op, f1, f2, pos) ->
        let bvs1, f1 = pf f1 in
        let bvs2, f2 = pf f2 in
        let bvs, f22 = combine bvs1 bvs2 f2 in
        bvs, SepOp (op, f1, f22, pos)
    | Binder (b, vs, f, _) -> 
        let bvs1, f1 = pf f in
        let bvs2 = match bvs1 with
        | (b', vs') :: bvs' when b = b' -> (b, vs @ vs') :: bvs'
        | _ -> (b, vs) :: bvs1
        in
        bvs2, f1
    | f -> [], f
  and pf_fs fs =
    List.fold_right 
      (fun f (bvs2, fs2) ->
        let bvs1, f1 = pf f in
        let new_bvs2, f2 = combine bvs2 bvs1 f1 in
        new_bvs2, f2 :: fs2)
      fs ([], [])
  in
  let bvs, f1 = pf f in
  List.fold_right (fun (b, vs) f -> Binder (b, vs, f, None)) bvs f1
