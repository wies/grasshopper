open Form
open FormUtil
open Axioms
open Entails

type expr =
  | Term of term
  | Call of ident * expr list

type stmnt =
  | VarUpdate of ident * expr 
  | FunUpdate of ident * term * expr
  | New of ident
  | Dispose of term
  | Assume of Sl.form
  | AssumeGrass of form
  | Assert of Sl.form * string option
  | AssertGrass of form * string option
  | Block of stmnt list
  | While of form * Sl.form * stmnt
  | Ite of form * stmnt * stmnt
  | Return of term

type procedure = {
  name: ident;
  args: ident list;
  precondition: Sl.form;
  postcondition: Sl.form;
  body: stmnt
}

let alloc_id = (mk_ident "Alloc")

let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

let rec desugar stmnt = 
  let rec derefs acc = function
  | App (Read, [fld; loc], _) ->
      derefs (derefs (TermSet.add loc acc) fld) loc
  | App (_, ts, _) -> List.fold_left derefs acc ts
  | _ -> acc
  in
  let rec derefs_expr acc = function
  | Term t -> derefs acc t
  | Call (_, es) -> List.fold_left derefs_expr acc es
  in
  let assert_alloc ds =
    TermSet.fold 
      (fun loc acc -> 
        AssertGrass (mk_elem loc alloc_set, Some "alloc_check") :: acc
      )
      ds [] 
  in
  match stmnt with
  | VarUpdate (_, e) ->
      let ds = derefs_expr TermSet.empty e in
      Block (assert_alloc ds @ [stmnt])
  | FunUpdate (_, t, e) -> 
      let ds = derefs_expr (derefs TermSet.empty t) e in
      Block (assert_alloc ds @ [stmnt])
  | Dispose id ->
      Block (assert_alloc (TermSet.singleton id) @ [stmnt])
  | Block stmnts ->
      Block (List.map desugar stmnts)
  | While (cond, inv, s) -> 
      let s1 = desugar s in
      While (cond, inv, s1)
  | Ite (cond, is, es) ->
      let is1 = desugar is in
      let es1 = desugar es in
      Ite (cond, is1, es1)
  | Return t ->
      let ds = derefs TermSet.empty t in
      Block (assert_alloc ds @ [stmnt])
  | _ -> stmnt


let rec assigned_all stmnt = match stmnt with
  | Assume _ | AssumeGrass _ | Assert _ | AssertGrass _ | Return _  | FunUpdate (_, _, _) -> IdSet.empty
  | VarUpdate (t, _) -> IdSet.singleton t
  | Dispose _ | New _ -> IdSet.empty
  | Block lst -> List.fold_left (fun acc s -> IdSet.union acc (assigned_all s)) IdSet.empty lst
  | While (_, _, s) -> assigned_all s
  | Ite (_, s1, s2) -> IdSet.union (assigned_all s1) (assigned_all s2)

let rec assigned_loc stmnt = match stmnt with
  | Assume _ | AssumeGrass _ | Assert _ | AssertGrass _ | Return _  | FunUpdate (_, _, _) | VarUpdate (_, _) -> IdSet.empty
  | New t -> IdSet.singleton t
  | Dispose _ -> IdSet.empty
  | Block lst -> List.fold_left (fun acc s -> IdSet.union acc (assigned_loc s)) IdSet.empty lst
  | While (_, _, s) -> assigned_loc s
  | Ite (_, s1, s2) -> IdSet.union (assigned_loc s1) (assigned_loc s2)

let rec assigned_fld stmnt = match stmnt with
  | Assume _ | AssumeGrass _ | Assert _ | AssertGrass _ | Return _ -> IdSet.empty
  | FunUpdate (t, _, _) -> IdSet.singleton t
  | Dispose _ | New _ | VarUpdate _  -> IdSet.empty
  | Block lst -> List.fold_left (fun acc s -> IdSet.union acc (assigned_fld s)) IdSet.empty lst
  | While (_, _, s) -> assigned_fld s
  | Ite (_, s1, s2) -> IdSet.union (assigned_fld s1) (assigned_fld s2)

let assigned stmnt =
  let locs = assigned_loc stmnt in
  let all  = assigned_all stmnt in
  let flds = assigned_fld stmnt in
    [ IdSet.elements all, None;
      IdSet.elements locs, Some Loc;
      IdSet.elements flds, None ]

let rec change_heap stmnt = match stmnt with
  | Assume _ | AssumeGrass _ | Assert _ | AssertGrass _ | Return _ | VarUpdate _ -> false
  | FunUpdate _ | New _ | Dispose _ -> true
  | Block lst -> List.exists change_heap lst
  | While (_, _, s) -> change_heap s
  | Ite (_, s1, s2) -> (change_heap s1) || (change_heap s2)


let alloc_axioms () = 
  let alc = mk_not (mk_elem mk_null alloc_set) in
  if !Config.with_alloc_axioms then [mk_axiom "alloc_init" alc] else []

let latest_alloc subst =
  if IdMap.mem alloc_id subst
  then IdMap.find alloc_id subst
  else alloc_id

let to_grass h f subst = subst_id subst (Sl.to_grass h (Sl.subst_id subst f))
let to_grass_negated h f subst = subst_id subst (Sl.to_grass_negated h (Sl.subst_id subst f))
let to_grass_not_contained h f subst = subst_id subst (Sl.to_grass_not_contained h (Sl.subst_id subst f))

