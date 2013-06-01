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

let reachWo a b c = FormUtil.mk_reachwo (fpts) a b c
let btwn a b c = FormUtil.mk_btwn (fpts) a b c
let reach a b = if !Config.use_btwn then btwn a b b else reachWo a b b
let mk_domain d v = FormUtil.mk_elem v (mk_loc_set d)
let mk_domain_var d v = FormUtil.mk_elem v (mk_loc_set_var d)
let emptyset = FormUtil.mk_empty (Some (Form.Set Form.Loc))
let empty_t domain = FormUtil.mk_eq emptyset domain
let empty domain = empty_t (mk_loc_set domain)
let empty_var domain = empty_t (mk_loc_set_var domain)
let list_set_def id1 id2 domain =
  FormUtil.mk_iff
    (FormUtil.smk_and 
       [if !Config.use_btwn 
        then btwn id1 Axioms.loc1 id2
        else reachWo id1 Axioms.loc1 id2;
        FormUtil.mk_neq Axioms.loc1 id2])
    (mk_domain domain Axioms.loc1)

let mk_pure p = Pure p
let mk_true = mk_pure FormUtil.mk_true
let mk_false = mk_pure FormUtil.mk_false
let mk_eq a b = mk_pure (FormUtil.mk_eq a b)
let mk_not a = Not a
let mk_and a b = And [a; b]
let mk_or a b = Or [a; b]
let mk_sep a b = 
  match (a, b) with
  | (Atom (Emp, []), _) -> b
  | (_, Atom (Emp, [])) -> a
  | (SepConj aa, SepConj bb) -> SepConj (aa @ bb)
  | (a, SepConj bb) -> SepConj (a :: bb)
  | (SepConj aa, b) -> SepConj (aa @ [b]) 
  | _ -> SepConj [a; b]
let mk_pred s args = Atom (s, args)
let mk_emp = mk_pred Emp []
let mk_cell a = mk_pred Cell [a]
let mk_pts f a b = 
  mk_sep (mk_eq (FormUtil.mk_read f a) b) (mk_cell a)
let mk_sep_lst args = List.fold_left mk_sep mk_emp args
(*let mk_prev_pts a b = mk_pred (get_symbol "ptsTo") [fprev_pts; a; b]*)
(*let mk_ls a b = mk_pred (get_symbol "lseg") [a; b]*)
(*let mk_dls a b c d = mk_pred (get_symbol "dlseg") [a; b; c; d]*)

let mk_spatial_pred name args =
  match find_symbol name with
  | Some s ->
    if List.length args = s.arity then
      mk_pred (Pred (name, 0)) args
    else
      failwith (name ^ " expect " ^(string_of_int (s.arity))^
                " found (" ^(String.concat ", " (List.map Form.string_of_term args))^ ")")
  | None -> failwith ("unknown spatial predicate " ^ name)


let rec map_id fct f = match f with
  | Pure p -> Pure (FormUtil.map_id fct p)
  | Not t ->  Not (map_id fct t)
  | And lst -> And (List.map (map_id fct) lst)
  | Or lst -> Or (List.map (map_id fct) lst)
  | Atom (s, args) -> mk_pred s (List.map (FormUtil.map_id_term fct) args)
  | SepConj lst -> SepConj (List.map (map_id fct) lst)

let subst_id subst f =
  let get id =
    try IdMap.find id subst with Not_found -> id
  in
    map_id get f

let subst_consts_fun subst f =
  let rec map f = 
    match f with
    | Pure g -> Pure (FormUtil.subst_consts_fun subst g)
    | Not f ->  Not (map f)
    | And fs -> And (List.map map fs)
    | Or fs -> Or (List.map map fs)
    | Atom (p, args) -> 
        mk_pred p (List.map (FormUtil.subst_consts_fun_term subst) args)
    | SepConj fs -> SepConj (List.map map fs)
  in
  map f

let subst_consts subst f =
  let rec map f = match f with
    | Pure g -> Pure (FormUtil.subst_consts subst g)
    | Not f ->  Not (map f)
    | And fs -> And (List.map map fs)
    | Or fs -> Or (List.map map fs)
    | Atom (p, args) -> 
        mk_pred p (List.map (FormUtil.subst_consts_term subst) args)
    | SepConj fs -> SepConj (List.map map fs)
  in
    map f

let free_consts_sl f =
  let rec fc acc = function
    | Pure g -> IdSet.union acc (FormUtil.free_consts g)
    | Not f -> fc acc f
    | Or fs 
    | And fs 
    | SepConj fs -> List.fold_left fc acc fs
    | Atom (p, args) -> List.fold_left FormUtil.free_consts_term_acc acc args
  in fc IdSet.empty f


let rec get_clauses f = match f with
  | Form.BoolOp (Form.And, lst) ->  List.flatten (List.map get_clauses lst)
  (*| Form.Comment (c, f) -> List.map (fun x -> Form.Comment (c,x)) (get_clauses f)*)
  | other -> [other]

