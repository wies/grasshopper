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
        then merge (IdMap.add x (mk_var ~srt:srt1 y) sm) ((y, srt2) :: zs) xs1 (ys2 @ ys1) []
        else merge sm zs xs ys1 ((y, srt2) :: ys2)
    | [], _ -> sm, ys @ ys2 @ zs
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
            (*print_forms stdout [f1];
            List.iter (fun id -> Printf.printf "%s, " (str_of_ident (fst id))) vs1;
            print_newline ();
            List.iter (fun id -> Printf.printf "%s, " (str_of_ident (fst id))) vs2;
            print_newline ();
            IdMap.iter (fun id t -> Printf.printf "%s -> %s, " (str_of_ident id) (string_of_term t)) sm;
            print_newline ();*)
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
	    mk_exists [(e, srt)] (mk_or [mk_and [smk_elem ve s1; mk_not (smk_elem ve s2)];
					 mk_and [smk_elem ve s2; mk_not (smk_elem ve s1)]])
	| _ -> f)
    | BoolOp (Not, [Atom (App (SubsetEq, [s1; s2], _))]) ->
	let srt = element_sort_of_set s1 in
	let ve = mk_var ~srt:srt e in
	mk_exists [(e, srt)] (mk_and [smk_elem ve s1; mk_not (smk_elem ve s2)])
    | BoolOp (op, fs) -> BoolOp (op, List.map elim_neq fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, elim_neq f, a)
    | f -> f
  in
  fun f -> 
    let f1 = elim_neq f in
    let f2 = propagate_exists f1 in
    (*let _ = print_endline "Befor propagation: " in
    let _ = print_forms stdout [f1] in
    let _ = print_endline "After propagation: " in
    let _ = print_forms stdout [f2] in*)
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
    let nxa = mk_diff a x in
    let replacement_alloc =
      [ mk_not (smk_elem mk_null a');
        (* mk_subseteq x' a';
        mk_subseteq nxa a'; *)
        mk_eq a' (mk_union [x'; nxa])
      ]
    in

    let replacement_pts =
      mk_forall [Axioms.l1]
        (mk_implies
           (mk_not (smk_elem Axioms.loc1 nxa))
           (mk_eq (mk_read f Axioms.loc1) (mk_read f' Axioms.loc1))
        )
    in

    let replacement_reach =
      let ep v = mk_ep f x v in
      let reachwo_f = Axioms.reachwo_Fld f in
      let reach_f x y z = 
        if !Config.use_btwn 
        then mk_btwn f x z y
        else mk_reachwo f x y z 
      in
      let reach_f' x y z = 
        if !Config.use_btwn 
        then mk_btwn f' x z y
        else mk_reachwo f' x y z 
      in
      let open Axioms in
      [mk_axiom "reach_frame1"
         (mk_implies
            (reachwo_f loc1 loc2 (ep loc1))
            (mk_iff 
               (reach_f loc1 loc2 loc3)
               (reach_f' loc1 loc2 loc3)));
       mk_axiom "reach_frame2"
         (mk_implies
            (mk_and [mk_not (smk_elem loc1 x); mk_eq loc1 (ep loc1)])
            (mk_iff (reach_f loc1 loc2 loc3) (reach_f' loc1 loc2 loc3)))
     ]
    in
    
    let included = mk_subseteq x a in
    let preserve = mk_subseteq (mk_inter [a; x']) x in
    let axioms =
      included :: (*preserve ::*)
      replacement_pts ::
      replacement_alloc @
      replacement_reach
    in
    mk_and axioms
  in
  let rec process f = match f with
    | Atom (App (Frame, [x;x';a;a';f;f'], _)) -> 
        expand_frame x x' a a' f f'
    | Atom t -> Atom t
    | BoolOp (op, fs) -> BoolOp (op, List.map process fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, process f, a)
  in
  List.map process fs
  
let open_axioms openCond axioms = 
  if !Config.instantiate then
    let rec open_axiom = function
      | Binder (b, vs, f, a) -> 
          Binder (b, List.filter (~~ (openCond f)) vs, f, a)
      | BoolOp (op, fs) -> BoolOp (op, List.map open_axiom fs)
      | f -> f
    in List.map open_axiom axioms
  else axioms

let isFld f = function (_, Fld _) -> true | _ -> false

let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars


(** Reduce all set constraints by adding appropriate instances of the axioms of set operations.
 ** assumes that f is typed and in negation normal form *)
let reduce_sets_with_axioms fs gts =
  let split ts = List.fold_left (fun (ts1, ts2) t -> (ts2, t :: ts1)) ([], []) ts in
  let rec unflatten = function
    | App (Union, [t], _) 
    | App (Inter, [t], _) -> unflatten t
    | App (Union, [], srt) -> mk_empty srt
    | App (Union, ts, srt) ->
        let ts1, ts2 = split ts in
        App (Union, [unflatten (mk_union ts1); unflatten (mk_union ts2)], srt)
    | App (sym, ts, srt) -> App (sym, List.map unflatten ts, srt)
    | t -> t
  in
  let rec simplify_term = function
    (* todo: flatten unions, intersections, and enumerations *)
    | App (SubsetEq, [t1; t2], _) -> 
        let t11 = unflatten t1 in
        let t21 = unflatten t2 in
        let s = mk_free_const ?srt:(sort_of t11) (fresh_ident "S") in
        App (Eq, [t11; mk_union [t21; s]], Some Bool)
    | t -> unflatten t
  in
  let rec simplify = function
    | BoolOp (op, fs) -> BoolOp (op, List.map simplify fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, simplify f, a)
    | Atom t -> Atom (simplify_term t)
  in
  let fs1 = List.map simplify fs in
  let gts = TermSet.fold (fun t gts1 -> TermSet.add (unflatten t) gts1) gts TermSet.empty in
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
  let fld_partition, fld_map, fields = 
    let max, fld_map, fields = 
      TermSet.fold (fun t (n, fld_map, fields) -> match t with
      | App (_, _, Some (Fld _)) as fld -> 
          n+1, TermMap.add fld n fld_map, TermSet.add fld fields
      | _ -> n, fld_map, fields)
        gts (0, TermMap.empty, TermSet.empty)
    in
    let rec collect_eq partition = function
      | BoolOp (Not, f) -> partition
      | BoolOp (op, fs) -> List.fold_left collect_eq partition fs
      | Atom (App (Eq, [App (_, _, Some (Fld _)) as fld1; fld2], _)) ->
          Puf.union partition (TermMap.find fld1 fld_map) (TermMap.find fld2 fld_map)
      | Binder (_, _, f, _) -> collect_eq partition f
      | f -> partition
    in
    let fld_partition0 = List.fold_left collect_eq (Puf.create max) fs1 in
    TermSet.fold (fun t partition -> 
      match t with
      | App (Write, fld1 :: _, _) as fld2 -> 
          Puf.union partition (TermMap.find fld1 fld_map) (TermMap.find fld2 fld_map)
      | _ -> partition)
      gts fld_partition0,
    fld_map,
    fields
  in
  let partition_of fld =
    let p = 
      try Puf.find fld_partition (TermMap.find fld fld_map) 
      with Not_found -> failwith ("did not find field " ^ (string_of_term fld)) 
    in
    let res = TermSet.filter (fun fld1 -> Puf.find fld_partition (TermMap.find fld1 fld_map) = p) fields in
    (*print_endline ("partition of " ^ string_of_term fld);*)
    res
  in
  let gts1 = 
    (*let _ = print_endline "All terms: "; TermSet.iter (fun t -> print_endline (string_of_term t)) gts in*)
    TermSet.fold
      (fun t gts1 -> match t with
      | App (Read, [fld; arg], _) 
      | App (Write, [fld; arg; _], _) -> 
          (*let _ = print_endline ("Processing " ^ string_of_term t) in*)
          TermSet.fold (fun fld1 gts1 -> 
            TermSet.add (mk_read fld1 arg) gts1) (partition_of fld) gts1
      | _ -> gts1)
      gts (TermSet.union gts (ground_terms (smk_and null_ax1)))
  in
  let classes1 = CongruenceClosure.congr_classes fs1 gts1 in
  (* generate instances of all write axioms *)
  let write_terms = 
    let rec ft acc = function
      | App (Write, ts, _) as t -> 
          let new_acc = List.fold_left ft acc ts in
          TermSet.add t new_acc
      | App (_, ts, _) -> List.fold_left ft acc ts
      | _ -> acc
    in
    List.fold_left (fold_terms ft) TermSet.empty fs1
  in
  let read_write_ax = 
    TermSet.fold (fun t write_ax ->
      match t with
      | App (Write, [fld; loc1; loc2], _) ->
          open_axioms isFunVar (Axioms.read_write_axioms fld loc1 loc2) @ write_ax
      | _ -> write_ax) write_terms []
  in
  let read_write_ax1 = instantiate_with_terms true read_write_ax classes1 in
  let classes2 = CongruenceClosure.congr_classes (fs1 @ read_write_ax1) gts1 in
  (* instantiate the variables of sort Fld in all reachability axioms *)
  let basic_reach_flds = 
    fold_terms (fun flds -> function
      | App (ReachWO, Var _ :: _, _)
      | App (Btwn, Var _ :: _, _) -> flds
      | App (ReachWO, fld :: _, _) 
      | App (Btwn, fld :: _, _) -> TermSet.union (partition_of fld) flds
      | _ -> flds)
      TermSet.empty (smk_and fs1)
  in
  let reach_write_ax = 
    TermSet.fold (fun t write_ax ->
      match t with
      | App (Write, [fld; loc1; loc2], _) ->
          if TermSet.mem fld basic_reach_flds 
          then open_axioms isFunVar (Axioms.reach_write_axioms fld loc1 loc2) @ write_ax
          else write_ax
      | _ -> write_ax) write_terms []
  in
  let non_updated_flds = 
    TermSet.filter 
      (fun t -> List.for_all 
	  (function 
	    | (App (Write, _, _)) -> false 
	    | _ -> true) (CongruenceClosure.class_of t classes))
      basic_reach_flds
  in
  let reach_ax = open_axioms isFld (Axioms.reach_axioms ()) in
  let reach_ax1 = instantiate_with_terms false reach_ax (CongruenceClosure.restrict_classes classes2 non_updated_flds) in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let reach_ax2 = instantiate_with_terms true (open_axioms isFunVar reach_ax1) classes2 in
  rev_concat [fs1; reach_ax2; read_write_ax1; reach_write_ax], gts1

let reduce_remaining fs gts =
  (* generate local instances of all remaining axioms in which variables occur below function symbols *)
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
  let fs21 = (* Simplify.simplify *) (factorize_axioms fs2) in
  (* no reduction step should introduce implicit or explicit existential quantifiers after this point *)
  let fs3, ep_axioms, gts = reduce_ep fs21 in
  let fs4, gts1 = reduce_sets (fs3 @ ep_axioms) gts in
  let fs5, gts2 = reduce_reach fs4 gts1 in
  let fs6 = reduce_remaining fs5 gts2 in
  (* the following is a (probably stupid) heuristic to sort the formulas for improving the running time *)
  let fs7 = 
    (* sort by decreasing number of disjuncts in formula *)
    let cmp f1 f2 =
      let rec count_disjuncts acc = function
        | BoolOp (Or, fs) -> List.fold_left count_disjuncts (acc + List.length fs) fs
        | BoolOp (_, fs) -> List.fold_left count_disjuncts acc fs
        | Binder (_, _, f, _) -> count_disjuncts acc f
        | Atom _ -> acc
      in
      compare (count_disjuncts 0 f2) (count_disjuncts 0 f1)
    in
    List.stable_sort cmp fs6
  in
  fs7
