(** Utility functions for manipulating SL formulas *)

open Sl

let pos_of_sl_form = function
  | Pure (_, pos)
  | Atom (_, _, pos)
  | SepOp (_, _, _, pos)
  | BoolOp (_, _, pos) 
  | Binder (_, _, _, pos) -> pos

let mk_loc_set struct_srt d =
  let srt = Grass.Set (Grass.Loc struct_srt) in
    GrassUtil.mk_free_const srt d

let mk_loc_set_var struct_srt d =
  let srt = Grass.Set (Grass.Loc struct_srt) in
    GrassUtil.mk_var srt d

let mk_loc struct_srt d =
  if fst d = "null" then GrassUtil.mk_null struct_srt
  else GrassUtil.mk_free_const (Grass.Loc struct_srt) d

let emptyset      struct_srt        = GrassUtil.mk_empty (Grass.Set (Grass.Loc struct_srt))
let empty_t       struct_srt domain = GrassUtil.mk_eq (emptyset struct_srt) domain
let empty         struct_srt domain = empty_t struct_srt (mk_loc_set struct_srt domain)

(* the domain is a map id -> Set<Loc<id>> *)

let struct_srts_from_domains domains =
  SortMap.fold
    (fun k _ acc -> SortSet.add k acc)
    domains
    SortSet.empty

let replace_domains_elt domains struct_srt v =
  SortMap.add struct_srt v domains

let mk_empty_domains struct_srts =
  SortSet.fold
    (fun srt acc -> SortMap.add srt (emptyset srt) acc)
    struct_srts
    SortMap.empty

let mk_empty_domains_except struct_srts struct_srt prefix =
  let emp = mk_empty_domains struct_srts in
  let v = GrassUtil.fresh_ident prefix in
  replace_domains_elt emp struct_srt (mk_loc_set_var struct_srt v)

let mk_fresh_var_domains struct_srts prefix =
  SortSet.fold
    (fun srt acc ->
      let v = GrassUtil.fresh_ident prefix in
      SortMap.add srt (mk_loc_set_var srt v) acc
    )
    struct_srts
    SortMap.empty

let map_domains fct domains1 domains2 =
  List.map2
    (fun (ssrt, t1) (_, t2) -> fct ssrt t1 t2)
    (SortMap.bindings domains1)
    (SortMap.bindings domains2)

let mk_domains_disjoint domains1 domains2 =
  map_domains
    (fun ssrt t1 t2 -> GrassUtil.smk_disjoint t1 t2)
    domains1
    domains2

let mk_domains_eq domains1 domains2 =
  map_domains
    (fun _ t1 t2 -> GrassUtil.mk_eq t1 t2)
    domains1
    domains2
  
let mk_union_domains domains1 domains2 =
  SortMap.mapi
    (fun srt t1 ->
      let t2 = SortMap.find srt domains2 in
        GrassUtil.mk_union [t1; t2]
    )
    domains1

let mk_pure ?pos p = Pure (p, pos)
let mk_true = mk_pure GrassUtil.mk_true
let mk_false = mk_pure GrassUtil.mk_false
let mk_eq ?pos a b = mk_pure ?pos:pos (GrassUtil.mk_eq a b)
let mk_not ?pos a = BoolOp(Grass.Not, [a], pos)
let mk_and ?pos a b = BoolOp (Grass.And, [a; b], pos)
let mk_or ?pos a b = BoolOp (Grass.Or, [a; b], pos)
let mk_implies ?pos a b = BoolOp (Grass.Or, [BoolOp (Grass.Not, [a], None); b], pos)
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
let mk_emp pos = mk_atom ?pos:pos Emp []
let mk_cell ?pos t = mk_atom ?pos:pos Region [GrassUtil.mk_setenum [t]]
let mk_region ?pos r = mk_atom ?pos:pos Region [r]
let mk_pred ?pos p ts = mk_atom ?pos:pos (Pred p) ts
let mk_pts ?pos f a b = 
  mk_sep_star ?pos:pos (mk_eq ?pos:pos (GrassUtil.mk_read f [a]) b) (mk_cell ?pos:pos a)
let mk_sep_star_lst ?pos:pos args = List.fold_left (mk_sep_star ?pos:pos) (mk_emp pos) args
let mk_exists ?pos vs f = Binder (Grass.Exists, vs, f, pos)
let mk_forall ?pos vs f = Binder (Grass.Forall, vs, f, pos)

let free_symbols f = 
  let rec fsym acc = function
    | Pure (f, _) -> IdSet.union acc (GrassUtil.free_symbols f)
    | SepOp (_, f1, f2, _) -> fsym (fsym acc f1) f2
    | BoolOp (_, fs, _) -> List.fold_left fsym acc fs
    | Atom (s, args, _) ->
        let acc1 = match s with
          | Pred id -> IdSet.add id acc
          | _ -> acc
        in
        List.fold_left 
          GrassUtil.free_symbols_term_acc 
          acc1 args
    | Binder (b, vs, f, _) -> fsym acc f
  in
  fsym IdSet.empty f

let map_pure_and_terms ffct tfct f =
  let rec m = function 
  | Pure (p, pos) -> Pure (ffct p, pos)
  | Atom (s, args, pos) -> mk_atom ?pos:pos s (List.map tfct args)
  | BoolOp (op, fs, pos) -> BoolOp (op, List.map m fs, pos)
  | SepOp (op, f1, f2, pos) -> SepOp (op, m f1, m f2, pos)
  | Binder (b, vs, f, pos) -> Binder (b, vs, m f, pos)
  in m f
    
let rec map_terms fct = map_pure_and_terms (GrassUtil.map_terms fct) fct
    
let rec map_id fct = map_pure_and_terms (GrassUtil.map_id fct) (GrassUtil.map_id_term fct)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
  map_id get f

let subst_consts_fun subst f =
  map_pure_and_terms (GrassUtil.subst_consts_fun subst) (GrassUtil.subst_consts_fun_term subst) f

let subst_consts subst f =
  map_pure_and_terms (GrassUtil.subst_consts subst) (GrassUtil.subst_consts_term subst) f

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

let subst_funs fct f =
  map_pure_and_terms (GrassUtil.subst_funs fct) (GrassUtil.subst_funs_term fct) f
    
let rec fold_terms fct acc f = 
  match f with
  | Binder (b, vs, f, _) -> fold_terms fct acc f
  | BoolOp (op, fs, _) -> List.fold_left (fold_terms fct) acc fs
  | SepOp (_, f1, f2, _) -> fold_terms fct (fold_terms fct acc f1) f2
  | Atom (_, args, _) -> List.fold_left fct acc args
  | Pure (g, _) -> GrassUtil.fold_terms fct acc g

let free_consts f =
  fold_terms GrassUtil.free_consts_term_acc IdSet.empty f
 
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
  | Grass.BoolOp (Grass.And, lst) ->  List.flatten (List.map get_clauses lst)
  | other -> [other]

let prenex_form f = 
  let combine acc bvs f =
    let acc_vs = 
      List.fold_left 
        (fun vs (_, srt_vs') -> 
          let vs' = List.rev_map fst srt_vs' in
          IdSet.union (GrassUtil.id_set_of_list vs') vs) 
        IdSet.empty acc 
    in
    let bvs1, f1 = List.fold_right 
        (fun (b, vs) (bvs1, f1) -> 
          let vs1, subst = 
            List.fold_right 
              (fun (v, srt) (vs1, subst) ->
                if IdSet.mem v acc_vs then
                  let v' = GrassUtil.fresh_ident (GrassUtil.name v) in
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
    List.map (fun (b, vs) -> (GrassUtil.dualize_binder b, vs)) bvs
  in
  let rec pf = function
    | BoolOp (op, fs, pos) -> 
        let bvs1, fs1 = pf_fs fs in
        let bvs2 = match op with
        | Grass.Not -> dualize bvs1 
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
  List.fold_right (fun (b, vs) f -> Binder (b, vs, f, pos_of_sl_form f)) bvs f1
