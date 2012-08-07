open Form
open Axioms

type stmnt =
  | VarUpdate of ident * term
  | FunUpdate of ident * term * term
  | New of ident
  | Assume of form
  | Label of string

type path = stmnt list

let add_jp_terms pf_a pf_b =
  let consts f =
    IdMap.fold 
      (fun id decl acc -> if (not decl.is_pred) && decl.arity = 0 then IdSet.add id acc else acc)
      (sign f) IdSet.empty
  in
  let shared_consts = 
    let shared_consts0 = 
      IdSet.inter (consts (mk_and pf_a)) (consts (mk_and pf_b)) 
    in
    IdSet.remove null_id shared_consts0 
  in
  let shared_funs = 
    IdSet.inter (unary_funs (mk_and pf_a)) (unary_funs (mk_and pf_b))
  in
  let rec jpt acc cs =
    if IdSet.is_empty cs then acc else
    let c = IdSet.choose cs in
    let new_cs = IdSet.remove c cs in
    let new_acc = 
      IdSet.fold (fun fn acc ->
	IdSet.fold 
	  (fun c1 acc ->
	    let eq = mk_eq (jp fn (mk_const c) (mk_const c1)) null in
	    mk_or [eq; mk_not eq] :: acc)
	  new_cs acc)
	shared_funs acc
    in jpt new_acc new_cs
  in 
  pf_a @ jpt [] shared_consts, pf_b

let ssa_partial ident_map path =
  let subst_ident id ident_map =
    try 
      IdMap.find id ident_map
    with Not_found -> id
  in
  let fresh_ident id ident_map =
    let name, m = subst_ident id ident_map in
    let new_id = (name, m + 1) in
    let new_ident_map = 
      IdMap.add (jp_id id) (jp_id new_id) 
	(IdMap.add (reach_id id) (reach_id new_id)
	   (IdMap.add id new_id ident_map))
    in
    new_id, new_ident_map
  in
  let rec pf segs fs ident_map = function
    | [] -> (List.rev (List.rev fs :: segs), ident_map)
    | st :: stmnts -> match st with
      | Assume f ->
	  pf segs (subst_id ident_map f :: fs) ident_map stmnts
      | VarUpdate (id, t) ->
	  let t1 = subst_id_term ident_map t in
	  let id1, ident_map1 = fresh_ident id ident_map in
	  pf segs (mk_eq (mk_const id1) t1 :: fs) ident_map1 stmnts
      | FunUpdate (id0, ind, upd) ->
	  let ind1 = subst_id_term ident_map ind in
	  let upd1 = subst_id_term ident_map upd in
	  let id = subst_ident id0 ident_map in
	  let id1, ident_map1 = fresh_ident id0 ident_map in
	  let axioms = update_axioms id id1 ind1 upd1 in
	  pf segs (List.rev_append axioms fs) ident_map1 stmnts
      |	New id ->
	  let id1, ident_map1 = fresh_ident id ident_map in
	  let alloc = subst_ident alloc_id ident_map1 in
	  let alloc1, ident_map2 = fresh_ident alloc_id ident_map1 in
	  let axioms = alloc_update_axioms id1 alloc alloc1 in
	  pf segs (List.rev_append axioms fs) ident_map2 stmnts
      |	Label _ ->
	  pf (List.rev fs :: segs) [] ident_map stmnts
  in
    pf [] [] ident_map path


let ssa_form path = fst (ssa_partial IdMap.empty path)

let path_form path =
  let pf_a, pf_b =
    match ssa_form path with
    | [pf_a; pf_b] -> pf_a, pf_b
    | _ -> failwith "Path should contain exactly one cut point."
  in
  let pf_a, pf_b = 
    if !with_jp_axioms then add_jp_terms pf_a pf_b 
    else pf_a, pf_b
  in
  match add_axioms [pf_a; pf_b] with
  | [a; b] -> (a, b)
  | _ -> failwith "add_axioms did not return two elements"
    
