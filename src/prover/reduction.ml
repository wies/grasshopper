open Util
open Form
open FormUtil
open InstGen

(** Skolemization 
 ** assumes that f is in negation normal form *)
let skolemize f =
  let rec sk vs = function
    | BoolOp (op, fs) -> BoolOp (op, List.map (sk vs) fs)
    | Binder (Forall, bvs, f, a) ->
	let vs1 = 
	  List.fold_left 
	    (fun vs1 (id, srt) -> IdMap.add id srt vs1) vs bvs 
	in
	Binder (Forall, bvs, sk vs1 f, a)
    | Binder (Exists, bvs, f, a) ->
	let ts = IdMap.fold (fun id srt ts -> mk_var ~srt:srt id :: ts) vs [] in
	let sm = List.fold_left 
	    (fun sm (id, srt) -> 
	      let sk_fn = FreeSym (fresh_ident ("sk_" ^ (str_of_ident id))) in
	      IdMap.add id (mk_app ~srt:srt sk_fn ts) sm) 
	    IdMap.empty bvs
	in 
	annotate (subst sm (sk vs f)) a
    | f -> f
  in sk IdMap.empty f

(** Reduce all set constraints to constraints over unary predicates
 ** assumes that f is in negation normal form *)
let reduce_sets =
  let e = fresh_ident "?e" in
  let get_base_sort s =
    match sort_of s with
    | Some (Set srt) -> srt
    | _ -> failwith "untyped or illtyped set expression"
  in
  let rec elim_neq = 
    let e = fresh_ident "?e" in
    function
      |	BoolOp (Not, [Atom (App (Eq, [s1; s2], _))]) as f ->
	  (match sort_of s1 with
	  | Some (Set srt) ->
	      let ve = mk_var ~srt:srt e in
	      mk_exists [(e, srt)] (mk_or [mk_and [mk_elem ve s1; mk_not (mk_elem ve s2)];
					   mk_and [mk_elem ve s2; mk_not (mk_elem ve s1)]])
	  | _ -> f)
      |	BoolOp (Not, [Atom (App (SubsetEq, [s1; s2], _))]) ->
	  let srt = get_base_sort s1 in
	  let ve = mk_var ~srt:srt e in
	  mk_exists [(e, srt)] (mk_and [mk_elem ve s1; mk_not (mk_elem ve s2)])
      |	BoolOp (op, fs) -> BoolOp (op, List.map elim_neq fs)
      |	Binder (b, vs, f, a) -> Binder (b, vs, elim_neq f, a)
      |	f -> f
  in
  let encode_set_exp srt e s =
    let rec ese = function
      |	App (Empty, [], _) -> mk_false
      |	App (FreeSym id, [], _) -> mk_pred id [e]
      |	App (Union, sets, _) -> mk_or (List.map ese sets)
      |	App (Inter, sets, _) -> mk_and (List.map ese sets)
      |	App (Diff, [s1; s2], _) -> mk_and [ese s1; mk_not (ese s2)]
      |	App (SetEnum, ts, _) -> mk_or (List.map (mk_eq e) ts)
      |	Var _ -> failwith "encode_set_exp: tried to eliminate quantified set variable"
      |	_ -> failwith "encode_set_exp: tried to encode non-set expression"
    in ese s
  in
  let rec elim_sets = function
    | Atom (App (Elem, [e; s], _)) ->
	let srt = get_base_sort s in
	encode_set_exp srt e s
    | Atom (App (Eq, [s1; s2], _)) as f ->
	(match sort_of s1 with
	  | Some (Set srt) ->
	      let ve = mk_var ~srt:srt e in
	      let es1 = encode_set_exp srt ve s1 in
	      let es2 = encode_set_exp srt ve s2 in
	      mk_forall [(e, srt)] (mk_iff es1 es2)
	  | _ -> f)
    | Atom (App (SubsetEq, [s1; s2], _)) ->
	let srt = get_base_sort s1 in
	let ve = mk_var ~srt:srt e in
	let es1 = encode_set_exp srt ve s1 in
	let es2 = encode_set_exp srt ve s2 in
	mk_forall [(e, srt)] (mk_implies es1 es2)
    | BoolOp (op, fs) -> BoolOp (op, List.map elim_sets fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, elim_sets f, a)
    | f -> f
  in
  fun f ->
    let f1 = elim_neq f in
    elim_sets f1
  
let open_axioms openCond axioms = 
  let open_axiom = function
  | Binder (b, vs, f, a) -> 
      Binder (b, List.filter (~~ (openCond f)) vs, f, a)
  | f -> f
  in List.map open_axiom axioms

let isFld f = function (_, Fld _) -> true | _ -> false

let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars


(** Adds instantiated theory axioms for graph reachability to formula f
 ** assumes that f is typed *)
let reduce_reach fs =
  let gts = TermSet.add mk_null (ground_terms (mk_and fs)) in
  (* instantiate the variables of sort fld in all reachability axioms *)
  let basic_pt_flds = TermSet.filter (has_sort (Fld Loc) &&& is_free_const) gts in
  let reachwo_ax = open_axioms isFld (Axioms.reachwo_axioms ()) in
  let defs, reachwo_ax1 = instantiate_with_terms false fs reachwo_ax basic_pt_flds in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let defs2, reachwo_ax2 = instantiate_with_terms true fs (open_axioms isFunVar reachwo_ax1) gts in
  (* generate instances of all update axioms *)
  let write_ax = open_axioms isFunVar (Axioms.write_axioms ()) in
  let defs3, write_ax1 = instantiate_with_terms true fs write_ax gts in
  defs @ defs2 @ defs3 @ fs, write_ax1 @ reachwo_ax2


(** Reduces the given formula to the target theory fragment, as specified by the configuration *)
let reduce f = 
  let rec split_ands acc = function
    | BoolOp(And, fs) :: gs -> split_ands acc (fs @ gs)
    | f :: gs -> split_ands (f :: acc) gs
    | [] -> List.rev acc
  in
  let f1 = nnf f in
  let fs1 = split_ands [] [f1] in
  let fs2 = List.map reduce_sets fs1 in
  let fs3 = List.map skolemize fs2 in
  let fs4, reach_axioms = reduce_reach fs3 in
  fs4 @ reach_axioms
