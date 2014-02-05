(** Reduction from GRASS to EPR + Stratified Sorts *)

open Util
open Form
open FormUtil
open InstGen
open SimplifyForm


(** Eliminate all implicit and explicit existential quantifiers using skolemization.
 ** Assumes that [f] is typed and in negation normal form. *)
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
    skolemize f1

let massage_field_reads fs = 
  let reach_flds = 
    fold_terms (fun flds -> function
      | App (Btwn, Var _ :: _, _) -> flds
      | App (Btwn, fld :: _, _) -> TermSet.add fld flds
      | _ -> flds)
      TermSet.empty (mk_and fs)
  in
  let rec massage = function 
  | BoolOp (And as op, fs)
  | BoolOp (Or as op, fs) -> BoolOp (op, List.map massage fs)
  | Binder (b, vs, f, a) -> Binder (b, vs, massage f, a)
  | Atom (App (Eq, [App (Read, [fld; Var _ as arg], Some Loc); App (FreeSym _, [], _) as t], _))
  | Atom (App (Eq, [App (FreeSym _, [], _) as t; App (Read, [fld; Var _ as arg], Some Loc)], _)) 
    when TermSet.mem fld reach_flds ->
      let f1 = 
        mk_and [mk_btwn fld arg t t;
                mk_forall [Axioms.l1]
                  (mk_or [mk_eq Axioms.loc1 arg; mk_eq Axioms.loc1 t; 
                          mk_not (mk_btwn fld arg Axioms.loc1 t)])]
      in
      f1
  | f -> f
  in List.map massage fs
    
(** Hoist all universally quantified subformulas to top level.
 ** Assumes that formulas [fs] are in negation normal form. *)
let factorize_axioms fs =
  let rec extract f axioms = 
    match f with
    | Binder (b, [], g, a) ->
        let g1, axioms = extract g axioms in
        Binder (b, [], g1, a), axioms
    | Binder (Forall, (_ :: _ as vs), f1, a) -> 
        let p = mk_atom (FreeSym (fresh_ident "Axiom")) [] in
        let comments, other_annots = List.partition (function Comment _ -> true | _ -> false) a in 
        let fact_axiom = annotate (mk_implies p (Binder (Forall, vs, f1, other_annots))) comments in
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
  let process (axioms, fs1) f = 
    match f with
    | Binder (Forall, _ :: _, _, _) -> f :: fs1, axioms
    | _ -> 
        let f1, axioms1 = extract f axioms in
        f1 :: fs1, axioms1
  in 
  let fs1, axioms = List.fold_left process ([], []) fs in
  axioms @ fs1


(** Add axioms for frame predicates. *)
let field_partitions fs gts =
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
    let fld_partition0 = List.fold_left collect_eq (Puf.create max) fs in
    let fld_partition =
      TermSet.fold (fun t partition -> 
        match t with
        | App (Write, fld1 :: _, _) as fld2 
        | App (Frame, [_; _; fld1; fld2], _) -> 
            Puf.union partition (TermMap.find fld1 fld_map) (TermMap.find fld2 fld_map)
        | _ -> partition)
      gts fld_partition0
    in
    fld_partition, fld_map, fields
  in
  let partition_of fld =
    let p = 
      try Puf.find fld_partition (TermMap.find fld fld_map) 
      with Not_found -> failwith ("did not find field " ^ (string_of_term fld)) 
    in
    let res = TermSet.filter (fun fld1 -> Puf.find fld_partition (TermMap.find fld1 fld_map) = p) fields in
    res
  in
  partition_of

let btwn_fields fs gts =
  let partition_of = field_partitions fs gts in
  fold_terms (fun flds -> function
    | App (Btwn, (App (_, _, _) as fld) :: _, _) -> 
        TermSet.union (partition_of fld) flds
    | _ -> flds)
    TermSet.empty (smk_and fs)  

let btwn_fields_in_fs fs = btwn_fields fs (ground_terms (smk_and fs))

let reduce_frame fs =
  let btwn_flds = btwn_fields_in_fs fs in
  let expand_frame x a f f' =
    let frame = mk_diff a x in
    let reduce_graph () =
      let replacement_pts =
        Axioms.mk_axiom "pts_frame"
          (mk_implies
             (smk_elem Axioms.loc1 frame)
             (mk_eq (mk_read f Axioms.loc1) (mk_read f' Axioms.loc1))
          )
      in
     
      let replacement_reach =
        let ep v = mk_ep f x v in
        let reachwo_f = Axioms.reachwo_Fld f in
        let reach_f x y z = mk_btwn f x z y in
        let reach_f' x y z = mk_btwn f' x z y in
        let open Axioms in
        if TermSet.mem f' btwn_flds then
          match f' with
          | App (FreeSym (p, _), _, _) when p = "parent" ->
              [mk_axiom "reach_frame"
                 (mk_sequent
                    [smk_elem loc1 frame]
                    [mk_iff (reach_f loc1 loc2 loc3) (reach_f' loc1 loc2 loc3)])]
          | _ ->
          [mk_axiom "reach_frame1"
             (mk_sequent
                [reachwo_f loc1 loc2 (ep loc1)]
                [(mk_iff 
                   (reach_f loc1 loc2 loc3)
                   (reach_f' loc1 loc2 loc3))]);
           mk_axiom "reach_frame2"
             (mk_implies
                (mk_and [mk_not (smk_elem loc1 x); mk_eq loc1 (ep loc1)])
                (mk_iff (reach_f loc1 loc2 loc3) (reach_f' loc1 loc2 loc3)))
         ]
        else []
      in
      
      let axioms =
        replacement_pts ::
        replacement_reach
      in
      mk_and axioms
    in
    let reduce_data () =
      Axioms.mk_axiom "data_frame"
        (mk_implies
           (smk_elem Axioms.loc1 frame)
           (mk_eq (mk_read f Axioms.loc1) (mk_read f' Axioms.loc1))
        )
    in
      (*Debug.amsg ("expanding frame for " ^ (string_of_term f) ^ "\n");*)
      match sort_of f with
      | Some (Fld Loc) -> reduce_graph ()
      | Some (Fld Int) | Some (Fld Bool) -> reduce_data ()
      | None ->
        Debug.amsg "reduce_frame: type not given, assuming Fld Loc\n";
        reduce_graph ()
      | Some other -> failwith ("reduce_frame did not expect f with type " ^ (string_of_sort other))
  in
  let rec process f (frame_axioms, fields) = match f with
    | Atom (App (Frame, [x; a; fld; fld'], _)) when fld <> fld' ->
        let fields1 = 
          let _, flds = 
            try TermMap.find x fields
            with Not_found -> a, []
          in
          TermMap.add x (a, fld :: fld' :: flds) fields
        in
        mk_implies f (expand_frame x a fld fld') :: frame_axioms, fields1
    | BoolOp (op, fs) -> 
        List.fold_left (fun acc f -> process f acc)
          (frame_axioms, fields) fs
    | Binder (b, vs, f, a) ->
        process f (frame_axioms, fields)
    | _ -> (frame_axioms, fields)        
  in
  let frame_axioms, fields =
    List.fold_left
      (fun acc f -> process f acc)
      ([], TermMap.empty) fs
  in
  Util.rev_concat [frame_axioms; fs] 
  
let open_axioms open_cond axioms = 
  let rec open_axiom generators = function
    | Binder (b, [], f, a) ->
        let f1, generators1 = open_axiom generators f in
        Binder (b, [], f1, a), generators1
    | Binder (b, vs, f, a) -> 
        (* extract term generators *)
        let generators1, a1, gen_vs =
          List.fold_right 
            (fun ann (generators, a1, gen_vs) ->
              match ann with
              | TermGenerator (bvs, fvs, g, t) ->
                  let gen = (bvs, fvs, g, t) in
                  let gen_vs1 = 
                    List.fold_left 
                      (fun acc (x, _) -> IdSet.add x acc) 
                      gen_vs bvs 
                  in
                  gen :: generators, a1, gen_vs1
              | _ -> generators, ann :: a1, gen_vs
            ) a (generators, [], IdSet.empty)
        in
        let open_generators (x, _) = IdSet.mem x gen_vs in
        let vs1 = List.filter (~~ (open_cond f ||| open_generators)) vs in
        if !Config.instantiate then
          Binder (b, vs1, f, a1), generators1
        else 
          Binder (b, vs, f, a1), generators1
    | BoolOp (op, fs) -> 
        let fs1, generators1 = 
          List.fold_right open_axioms fs ([], generators)
        in
        BoolOp (op, fs1), generators1
    | f -> f, generators
  and open_axioms f (fs1, generators) =
    let f1, generators1 = open_axiom generators f in
    f1 :: fs1, generators1
  in
  List.fold_right open_axioms axioms ([], [])
    
let isFld f = function (_, Fld _) -> true | _ -> false

let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars


(** Simplifies set constraints and adds axioms for set operations.
 ** Assumes that f is typed and in negation normal form. *)
let reduce_sets fs =
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
        (*let s = mk_free_const ?srt:(sort_of t11) (fresh_ident "S") in*)
        App (Eq, [t21; mk_union [t11; t21]], Some Bool)
    | t -> unflatten t
  in
  let rec simplify = function
    | BoolOp (op, fs) -> BoolOp (op, List.map simplify fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, simplify f, a)
    | Atom t -> Atom (simplify_term t)
  in
  let fs1 = List.map simplify fs in
  rev_concat [fs1; Axioms.set_axioms ()]


(** Adds theory axioms for the entry point function to formula f.
 ** Assumes that f is typed and that all frame predicates have been reduced. *)
let instantiate_ep fs =
  let gts = ground_terms (smk_and fs) in
  let flds = btwn_fields fs gts in
  let flds =
    TermSet.filter 
      (fun t -> match t with | App (FreeSym (p, _), _, _) -> p <> "parent" | _ -> true)
      flds
  in
  let classes =  CongruenceClosure.congr_classes fs gts in
  (*List.iter (fun f -> print_form stdout f; print_newline ()) (Axioms.ep_axioms ());*)
  let ep_ax, generators = open_axioms isFld (Axioms.ep_axioms ()) in
  let generators = List.map (fun (a,b,c,d)-> TermGenerator(a, b, c, d)) generators in
  (*print_endline "---";
  List.iter (fun f -> print_form stdout f; print_newline ()) ep_ax;*)
  let ep_ax = instantiate_with_terms false ep_ax (CongruenceClosure.restrict_classes classes flds) in
  (*print_endline "---";
  List.iter (fun f -> print_form stdout f; print_newline ()) ep_ax;*)
    match ep_ax with
    | Binder(b, vs, f, ann) :: xs -> Binder(b, vs, f, ann @ generators):: xs @ fs
    | [] -> fs
    | _ -> failwith "don't know where to put the generators"
  (*List.rev_append (Axioms.ep_axioms ()) fs*)
 
let reduce_read_write fs =
  let gts = ground_terms (smk_and fs) in
  let basic_pt_flds = TermSet.filter (has_sort (Fld Loc) &&& is_free_const) gts in
  (* instantiate null axioms *)
  let classes =  CongruenceClosure.congr_classes fs gts in
  let null_ax, _ = open_axioms isFld (Axioms.null_axioms ()) in
  let null_ax1 = instantiate_with_terms false null_ax (CongruenceClosure.restrict_classes classes basic_pt_flds) in
  let fs1 = null_ax1 @ fs in
  let gts = TermSet.union (ground_terms (smk_and null_ax1)) gts in
  let field_sorts = TermSet.fold (fun t srts ->
    match sort_of t with
    | Some (Fld srt) -> SrtSet.add srt srts
    | _ -> srts)
      gts SrtSet.empty
  in
  (* propagate read terms *)
  let read_propagators =
    SrtSet.fold (fun srt propagators ->
      let f1 = fresh_ident "?f", Fld srt in
      let fld1 = mk_var ~srt:(snd f1) (fst f1) in
      let f2 = fresh_ident "?g", Fld srt in
      let fld2 = mk_var ~srt:(snd f2) (fst f2) in
      let d = fresh_ident "?d" in
      let d1 = d, srt in
      let dvar = mk_var ~srt:srt d in
      let l1 = Axioms.l1 in
      let loc1 = Axioms.loc1 in
      let l2 = Axioms.l2 in
      let loc2 = Axioms.loc2 in
      let s1 = Axioms.s1 in
      let set1 = Axioms.set1 in
      let s2 = Axioms.s2 in
      let set2 = Axioms.set2 in
      (* f = g, x.f -> x.g *)
      ([],
       [f1; f2; l1],
       [Match (mk_eq_term fld1 fld2, FilterTrue);
        Match (mk_read fld1 loc1, FilterTrue)],
       mk_read fld2 loc1) ::
      (* f = g, x.g -> x.f *)
      ([],
       [f1; f2; l1],
       [Match (mk_eq_term fld1 fld2, FilterTrue);
        Match (mk_read fld1 loc1, FilterTrue)],
       mk_read fld2 loc1) :: 
      (* f [x := d], y.(f [x := d]) -> y.f *)
      ([],
       [f1; l1; l2; d1],
       [Match (mk_write fld1 loc1 dvar, FilterTrue);
        Match (mk_read (mk_write fld1 loc1 dvar) loc2, FilterTrue)],
       mk_read fld1 loc2) ::
      (* f [x := d], y.f -> y.(f [x := d]) *)
      ([],
       [f1; l1; l2; d1],
       [Match (mk_write fld1 loc1 dvar, FilterTrue);
        Match (mk_read fld1 loc2, FilterTrue)],
       mk_read (mk_write fld1 loc1 dvar) loc2) ::
      (* Frame (x, a, f, g), y.g -> y.f *)
      ([],
       [f1; f2; s1; s2; l1],
       [Match (mk_frame_term set1 set2 fld1 fld2, FilterTrue);
        Match (mk_read fld2 loc1, FilterTrue)],
       mk_read fld1 loc1) ::
      (* Frame (x, a, f, g), y.f -> y.g *)
      ([],
       [f1; f2; s1; s2; l1],
       [Match (mk_frame_term set1 set2 fld1 fld2, FilterTrue);
        Match (mk_read fld1 loc1, FilterTrue)],
       mk_read fld2 loc1) ::
      propagators)
      field_sorts []
  in
  (* generate instances of all read over write axioms *)
  let read_write_ax = 
    let generators_and_axioms =
      TermSet.fold (fun t acc ->
        match t with
        | App (Write, [fld; _; _], _) ->
            Axioms.read_write_axioms_closed fld @ acc
        | _ -> acc) gts []
    in
    generators_and_axioms 
  in
  (*let gts = generate_terms (read_propagators @ generators) gts in
  let classes1 = CongruenceClosure.congr_classes fs1 gts in
  let read_write_ax1 = instantiate_with_terms true read_write_ax classes1 in
  let gts = TermSet.union gts (ground_terms (mk_and read_write_ax1)) in*)
  rev_concat [read_write_ax; fs1], read_propagators, gts




(** Adds instantiated theory axioms for graph reachability to formula f.
 ** Assumes that f is typed. *)
let reduce_reach fs gts =
  let classes = CongruenceClosure.congr_classes fs gts in
  (* instantiate the variables of sort Fld in all reachability axioms *)
  let btwn_flds = btwn_fields fs gts in
  (*let _ = TermSet.iter (print_term stdout) btwn_flds in*)
  let reach_write_ax = 
    TermSet.fold (fun t write_ax ->
      match t with
      | App (Write, [fld; loc1; loc2], _) ->
          if TermSet.mem fld btwn_flds 
          then Axioms.reach_write_axioms fld loc1 loc2 @ write_ax
          else write_ax
      | _ -> write_ax) gts []
  in
  let non_updated_flds = 
    TermSet.filter 
      (fun t -> List.for_all 
	  (function 
	    | (App (Write, _, _)) -> false 
	    | _ -> true) (CongruenceClosure.class_of t classes))
      btwn_flds
  in
  let reach_ax, _ = open_axioms isFld (Axioms.reach_axioms ()) in
  let reach_ax1 = instantiate_with_terms false reach_ax (CongruenceClosure.restrict_classes classes non_updated_flds) in
  rev_concat [reach_ax1; reach_write_ax; fs], gts

let instantiate_user_def_axioms read_propagators fs gts =
  (* generate local instances of all remaining axioms in which variables occur below function symbols *)
  let fs1, generators = open_axioms isFunVar fs in
  let gts1 = generate_terms (read_propagators @ generators) gts in
  let _ =
    if Debug.is_debug () then
      begin
        print_endline "ground terms:";
        TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) gts;
        print_endline "generated terms:";
        TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) (TermSet.diff gts1 gts)
      end
  in
  let classes = CongruenceClosure.congr_classes fs gts1 in
  instantiate_with_terms true fs1 classes, gts1

let add_terms fs gts =
  if !Config.instantiate then fs else
  let gts_fs = ground_terms (mk_and fs) in
  let extra_gts = TermSet.diff gts gts_fs in
  TermSet.fold (fun t acc ->
    let srt = unsafe_sort_of t in
    let c = mk_free_const ~srt:srt (fresh_ident "t") in
    mk_eq t c :: acc)
    extra_gts fs

(** Reduces the given formula to the target theory fragment, as specified by the configuration.
 ** Assumes that f is typed. *)
let reduce f = 
  let rec split_ands acc = function
    | BoolOp(And, fs) :: gs -> 
        split_ands acc (fs @ gs)
    | Binder(_, [], BoolOp(And, fs), a) :: gs ->
        split_ands acc (List.map (fun f -> annotate f a) fs @ gs)
    | f :: gs -> split_ands (f :: acc) gs
    | [] -> List.rev acc
  in
  let f1 = nnf f in
  let fs = split_ands [] [f1] in
  (* *)
  let fs = massage_field_reads fs in
  let fs = List.map reduce_exists fs in
  (* no reduction step should introduce implicit or explicit existential quantifiers after this point *)
  (* formula rewriting that helps with the solving *)
  let fs = simplify_sets fs in
  let fs = pull_eq_up fs in
  (*TypeStrat.init fs;*)
  TypeStrat.default ();
  let fs = instantiate_ep fs in
  let fs = reduce_frame fs in
  let fs = factorize_axioms (split_ands [] fs) in
  let fs = reduce_sets fs in
  let fs, read_propagators, gts = reduce_read_write fs in
  let fs, gts = reduce_reach fs gts in
  let fs, gts = instantiate_user_def_axioms read_propagators fs gts in
  let fs = add_terms fs gts in
  TypeStrat.reset ();
  (* the following is a (probably stupid) heuristic to sort the formulas for improving the running time *)
  (*let _ = 
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
    List.stable_sort cmp fs
  in*)
  fs
