open Util
open Form
open FormUtil
open InstGen

(** Skolemization 
 ** assumes that f is in negation normal form *)
let skolemize f =
  let rec sk vs = function
    | BoolOp (op, fs) -> smk_op op (List.map (sk vs) fs)
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
    
(** Propagate existentially quantified variables upward in the formula
 ** assume that f is in negation normal form *)
let propagate_exists f =
  let rec merge sm zs xs ys ys2 =
    match xs, ys with
    | (x, srt1) :: xs1, (y, srt2) :: ys1 ->
        if srt1 = srt2
        then merge (IdMap.add x (mk_var ~srt:srt1 y) sm) zs xs1 (ys2 @ ys) []
        else merge sm ((x, srt1) :: zs) xs ys1 ((y, srt2) :: ys2)
    | [], _ -> sm, ys @ zs
    | _, [] -> 
        if ys2 = [] then sm, xs @ zs
        else merge sm (List.hd xs :: zs) (List.tl xs) ys2 []
  in
  let rec prop = function
    | BoolOp (Or, fs) ->
        let fs1, vs = 
          List.fold_right (fun f (fs2, vs2) ->
            let f1, vs1 = prop f in
            let sm, vs = merge IdMap.empty [] vs1 vs2 [] in
            subst sm f1 :: fs2, vs) 
            fs ([], [])
        in BoolOp (Or, fs1), vs
    | BoolOp (And, fs) ->
        let fs1, vss = List.split (List.map prop fs) in
        BoolOp (And, fs1), List.concat vss
    | Binder (Exists, vs, f, a) -> 
        let vars = fv f in
        let vs0 = List.filter (fun (v, _) -> IdSet.mem v vars) vs in
        let sm, vs1 = 
          List.fold_left 
            (fun (sm, vs1) (v, srt) -> 
              let v1 = fresh_ident (name v) in
              IdMap.add v (mk_var ~srt:srt v1) sm, (v1, srt) :: vs1)
            (IdMap.empty, []) vs0
        in
        let f1 = subst sm f in
        (match a with 
        | [] -> f1, vs1
        | _ -> Binder (Exists, [], f1, a), vs1)
    | Binder (Forall, vs, f, a) ->
        let f1, vs1 = prop f in
        (match vs with
        | [] -> Binder (Forall, vs, f1, a), vs1
        | _ -> Binder (Forall, vs, mk_exists vs1 f1, a), [])
    | f -> f, []
  in
  let f1, vs = prop f in 
  mk_exists vs f1

(** Eliminate all implicit and explicit existential quantifiers using skolemization
 ** assumes that f is typed and in negation normal form *)
let reduce_exists =
  let e = fresh_ident "?e" in
  let rec elim_neq = function
    | BoolOp (Not, [Atom (App (Eq, [s1; s2], _))]) as f ->
	(match sort_of s1 with
	| Some (Set srt) ->
	    let ve = mk_var ~srt:srt e in
	    mk_exists [(e, srt)] (mk_or [mk_and [mk_elem ve s1; mk_not (mk_elem ve s2)];
					 mk_and [mk_elem ve s2; mk_not (mk_elem ve s1)]])
	| _ -> f)
    | BoolOp (Not, [Atom (App (SubsetEq, [s1; s2], _))]) ->
	let srt = element_sort_of_set s1 in
	let ve = mk_var ~srt:srt e in
	mk_exists [(e, srt)] (mk_and [mk_elem ve s1; mk_not (mk_elem ve s2)])
    | BoolOp (op, fs) -> BoolOp (op, List.map elim_neq fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, elim_neq f, a)
    | f -> f
  in
  fun f -> 
    let f1 = elim_neq f in
    let f2 = propagate_exists f1 in
    skolemize f2

let factorize_axioms fs =
  let rec extract f axioms = match f with
    | Binder (Forall, (_ :: _ as vs), f1, a) -> 
        let p = mk_atom (FreeSym (fresh_ident "Axiom")) [] in
        let fact_axiom = annotate (mk_or [mk_not p; Binder (Forall, vs, f1, [])]) a in
	p, fact_axiom :: axioms
    | BoolOp (op, fs) -> 
	let fs1, axioms = 
	  List.fold_right 
	    (fun f (fs1, axioms) ->
	      let f1, axioms1 = extract f axioms in 
	      f1 :: fs1, axioms1)
	    fs ([], axioms)
	in 
	BoolOp (op, fs1), axioms
    | f -> f, axioms
  in
  let process (axioms, fs1) f = match f with
    | Binder (Forall, _, _, _) -> f :: fs1, axioms
    | _ -> 
        let f1, axioms1 = extract f axioms in
        f1 :: fs1, axioms1
  in 
  let fs1, axioms = List.fold_left process ([], []) fs in
  axioms @ fs1

(** Reduce all set constraints to constraints over unary predicates
 ** assumes that f is typed and in negation normal form *)
let reduce_sets_to_predicates =
  let e = fresh_ident "?e" in
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
  let mk_ep id = mk_free_app ~srt:Loc ((str_of_symbol EntPnt ^ "_" ^ str_of_ident id), 0) in
  let rec abstract_set_consts = function
    | App (EntPnt, [fld; set; loc], srt) ->
	(match set with
	| App (FreeSym id, [], _) ->
	    mk_ep id [abstract_set_consts fld; abstract_set_consts loc]
	| App (Empty, [], _) -> abstract_set_consts loc
	| _ -> failwith "abstract_set_consts: tried to abstract non-flat set expression")
    (* | App (FreeSym id, ts) -> *)
    | App (sym, ts, srt) -> App (sym, List.map abstract_set_consts ts, srt)
    | t -> t
  in
  let rec elim_sets = function
    | Atom (App (Elem, [e; s], _)) ->
	let srt = element_sort_of_set s in
	encode_set_exp srt (abstract_set_consts e) s
    | Atom (App (Eq, [s1; s2], _)) ->
	(match sort_of s1 with
	  | Some (Set srt) ->
	      let ve = mk_var ~srt:srt e in
	      let es1 = encode_set_exp srt ve s1 in
	      let es2 = encode_set_exp srt ve s2 in
	      mk_forall [(e, srt)] (mk_iff es1 es2)
	  | _ -> 
	      let s11 = abstract_set_consts s1 in
	      let s21 = abstract_set_consts s2 in
	      mk_eq s11 s21
	)
    | Atom (App (SubsetEq, [s1; s2], _)) ->
	let srt = element_sort_of_set s1 in
	let ve = mk_var ~srt:srt e in
	let es1 = encode_set_exp srt ve s1 in
	let es2 = encode_set_exp srt ve s2 in
	mk_forall [(e, srt)] (mk_implies es1 es2)
    | Atom t -> Atom (abstract_set_consts t)
    | BoolOp (op, fs) -> BoolOp (op, List.map elim_sets fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, elim_sets f, a)
  in
  fun fs gts -> List.map elim_sets fs, TermSet.fold (fun t gts1 -> TermSet.add (abstract_set_consts t) gts1) gts TermSet.empty
  

(** Reduce all frame predicates to constraints over sets and entry points. *)
let reduce_frame fs =
  let expand_frame x x' a a' f f' =
    let replacement_alloc =
      let nxa = mk_diff a x in
      [ mk_not (mk_elem mk_null a');
        mk_subseteq x' a';
        mk_subseteq nxa a';
        mk_subseteq a' (mk_union [x'; nxa])
      ]
    in

    let replacement_pts =
      mk_forall [Axioms.l1]
        (mk_implies
           (mk_not (mk_elem Axioms.loc1 x))
           (mk_eq (mk_read f Axioms.loc1) (mk_read f' Axioms.loc1))
        )
    in

    let replacement_reach =
      let ep v = mk_ep f x v in
      let reach1 x y z = mk_reachwo f  x y z in
      let reach2 x y z = mk_reachwo f' x y z in
      let open Axioms in
      (mk_forall [l1;l2;l3]
         (mk_implies
            (reach1 loc1 loc2 (ep loc1))
            (mk_iff 
               (reach1 loc1 loc2 loc3)
               (reach2 loc1 loc2 loc3))
         )
      ) :: (mk_forall [l1;l2;l3]
              (mk_implies
                 (mk_and [mk_not (mk_elem loc1 x); mk_eq loc1 (ep loc1)])
                 (mk_iff (reach1 loc1 loc2 loc3) (reach2 loc1 loc2 loc3))
              )
           ) :: []
    in
    
    let included = mk_subseteq x a in
    let preserve = mk_subseteq (mk_inter [a; x']) x in
    let axioms =
      included :: preserve ::
      replacement_pts ::
      replacement_alloc @
      replacement_reach
    in
    mk_and axioms
  in
  let rec process f = match f with
    | Atom (App (Frame, [x;x';a;a';f;f'], _)) -> expand_frame x x' a a' f f'
    | Atom t -> Atom t
    | BoolOp (op, fs) -> BoolOp (op, List.map process fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, process f, a)
  in
  List.map process fs
  
let open_axioms openCond axioms = 
  let rec open_axiom = function
  | Binder (b, vs, f, a) -> 
      Binder (b, List.filter (~~ (openCond f)) vs, f, a)
  | BoolOp (op, fs) -> BoolOp (op, List.map open_axiom fs)
  | f -> f
  in List.map open_axiom axioms

let isFld f = function (_, Fld _) -> true | _ -> false

let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars


(** Reduce all set constraints by adding appropriate instances of the axioms of set operations.
 ** assumes that f is typed and in negation normal form *)
let reduce_sets_with_axioms fs gts =
  let rec simplify_term = function
    (* todo: flatten unions, intersections, and enumerations *)
    | App (SubsetEq, [t1; t2], _) -> 
        let s = mk_free_const ?srt:(sort_of t1) (fresh_ident "S") in
        App (Eq, [t1; mk_union [t2; s]], Some Bool)
    | t -> t
  in
  let rec simplify = function
    | BoolOp (op, fs) -> BoolOp (op, List.map simplify fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, simplify f, a)
    | Atom t -> Atom (simplify_term t)
  in
  let fs1 = List.map simplify fs in
  let gts1 = TermSet.union gts (ground_terms (mk_and fs1)) in
  let classes = CongruenceClosure.congr_classes fs1 gts1 in
  let set_ax = open_axioms isFunVar (Axioms.set_axioms ()) in
  let set_ax1 = instantiate_with_terms true set_ax classes in
  rev_concat [fs1; set_ax1], gts1

let reduce_sets fs gts =
  if !Config.keep_sets 
  then reduce_sets_with_axioms fs gts 
  else reduce_sets_to_predicates fs gts

(** Adds instantiated theory axioms for the entry point function to formula f
 ** assumes that f is typed and that all frame predicates have been reduced *)
let reduce_ep fs =
  let gts = TermSet.add mk_null (ground_terms (mk_and fs)) in
  let loc_gts = TermSet.filter (has_sort Loc) gts in
  (* generate ep terms *)
  let rec get_ep_terms eps = function
    | App (EntPnt, ts, _) as t -> List.fold_left get_ep_terms (TermSet.add t eps) ts
    | App (_, ts, _) -> List.fold_left get_ep_terms eps ts
    | _ -> eps
  in
  let ep_terms_free = fold_terms get_ep_terms TermSet.empty (mk_and fs) in
  let gts_eps = 
    TermSet.fold 
      (fun t eps ->
	match t with
	| App (EntPnt, [fld; set; loc], srt) -> 
	    TermSet.fold (fun t eps -> TermSet.add (App (EntPnt, [fld; set; t], srt)) eps) loc_gts eps
	| _ -> eps
      )
      ep_terms_free gts
  in 
  (* instantiate the variables of sort Fld and Set in all ep axioms *)
  let classes = CongruenceClosure.congr_classes fs gts_eps in
  let ep_ax = open_axioms isFunVar (Axioms.ep_axioms ()) in
  let ep_ax1 = instantiate_with_terms true ep_ax classes in
  fs, ep_ax1, gts_eps

(** Adds instantiated theory axioms for graph reachability to formula f
 ** assumes that f is typed *)
let reduce_reach fs gts =
  let basic_pt_flds = TermSet.filter (has_sort (Fld Loc) &&& is_free_const) gts in
  (* instantiate null axioms *)
  let classes =  CongruenceClosure.congr_classes fs gts in
  (* let _ = List.iter (List.iter (fun t -> print_endline (string_of_term t))) classes in *)
  let null_ax = open_axioms isFld (Axioms.null_axioms ()) in
  let null_ax1 = instantiate_with_terms false null_ax (CongruenceClosure.restrict_classes classes basic_pt_flds) in
  let fs1 = null_ax1 @ fs in
  (* propagate read terms *)
  let gts1 = 
    let writes = 
      TermSet.fold 
	(fun t acc -> match t with
	|  App (Write, fld :: _, _) as fld' -> (fld, fld') :: acc
	| _ -> acc
	)
	gts []
    in
    let reads =
      TermSet.fold
	(fun t acc -> match t with
	|  App (Read, [fld; arg], _) -> (fld, arg) :: acc
	| _ -> acc
	)
	gts []
    in
    let rec propagate gts reads =
      let new_reads, new_gts = 
	List.fold_left 
	  (fun (new_reads, new_gts) (fld, arg) ->
	    try 
	      let fld' = List.assoc fld writes in 
	      (*let _ = print_endline ("adding term " ^ string_of_term (mk_read fld' arg)) in*)
	      (fld', arg) :: new_reads, TermSet.add (mk_read fld' arg) new_gts
	    with Not_found -> new_reads, new_gts
	  )
	  ([], gts) reads
      in
      match new_reads with
      |	[] -> new_gts 
      |	_ -> propagate new_gts new_reads
    in propagate (TermSet.union gts (ground_terms (smk_and null_ax1))) reads
  in
  let classes1 = CongruenceClosure.congr_classes fs1 gts1 in
  (* instantiate the variables of sort Fld in all reachability axioms *)
  let basic_reach_flds = 
    fold_terms (fun flds -> function
      | App (ReachWO, fld :: _, _) -> TermSet.add fld flds
      | _ -> flds)
      TermSet.empty (smk_and fs1)
  in
  (*let non_updated_flds = 
    TermSet.filter 
      (fun t -> List.for_all 
	  (function 
	    | (App (Write, _, _)) -> false 
	    | _ -> true) (CongruenceClosure.class_of t classes))
      basic_pt_flds
  in*)
  let reach_ax = open_axioms isFld (Axioms.reachwo_axioms ()) in
  let reach_ax1 = instantiate_with_terms false reach_ax (CongruenceClosure.restrict_classes classes1 basic_reach_flds) in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let reach_ax2 = instantiate_with_terms true (open_axioms isFunVar reach_ax1) classes1 in
  (* generate instances of all update axioms *)
  let write_ax = open_axioms isFunVar (Axioms.write_axioms ()) in
  let write_ax1 = instantiate_with_terms true write_ax classes1 in
  fs1, rev_concat [write_ax1; reach_ax2], gts1

let reduce_remaining fs gts =
  let classes = CongruenceClosure.congr_classes fs gts in
  let fs1 = open_axioms isFunVar fs in
  instantiate_with_terms true fs1 classes

(** Reduces the given formula to the target theory fragment, as specified by the configuration 
 ** assumes that f is typed *)
let reduce f = 
  let rec split_ands acc = function
    | BoolOp(And, fs) :: gs -> split_ands acc (fs @ gs)
    | f :: gs -> split_ands (f :: acc) gs
    | [] -> List.rev acc
  in
  let f1 = nnf f in
  let fs1 = split_ands [] [f1] in
  let fs2 = reduce_frame fs1 in
  let fs2 = List.map reduce_exists fs2 in
  let fs21 = factorize_axioms fs2 in
  (* no reduction step should introduce implicit or explicit existential quantifiers after this point *)
  let fs3, ep_axioms, gts = reduce_ep fs21 in
  let fs4, gts1 = reduce_sets (fs3 @ ep_axioms) gts in
  let fs5, reach_axioms, gts2 = reduce_reach fs4 gts1 in
  let fs6 = reduce_remaining fs5 gts in
  rev_concat [fs6; reach_axioms]
