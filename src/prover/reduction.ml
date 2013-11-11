(** Reduction from GRASS to EPR + Stratified Sorts *)

open Util
open Form
open FormUtil
open InstGen


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
    (*let _ = print_endline "Before propagation: " in
    let _ = print_forms stdout [f1] in
    let _ = print_endline "After propagation: " in
    let _ = print_forms stdout [f2] in*)
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
 ** Assumes that formulas [fs] are in negation normal form *)
let factorize_axioms fs =
  let rec extract f axioms = 
    match f with
    | Binder (b, [], g, a) ->
        let g1, axioms = extract g axioms in
        Binder (b, [], g1, a), axioms
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
  let process (axioms, fs1) f = 
    match f with
    | Binder (Forall, _ :: _, _, _) -> f :: fs1, axioms
    | _ -> 
        let f1, axioms1 = extract f axioms in
        f1 :: fs1, axioms1
  in 
  let fs1, axioms = List.fold_left process ([], []) fs in
  axioms @ fs1

(** Reduce all set constraints to constraints over unary predicates.
 ** Assumes that [f] is typed and in negation normal form *)
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
  fun fs gts -> 
    List.map elim_sets fs, 
    TermSet.fold 
      (fun t gts1 -> TermSet.add (abstract_set_consts t) gts1) 
      gts TermSet.empty
  

(** Reduce all frame predicates to constraints over sets and entry points. *)
let reduce_frame fs =
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
      | Some (Fld Int) -> reduce_data ()
      | None ->
        Debug.amsg "reduce_frame: type not given, assuming Fld Loc\n";
        reduce_graph ()
      | Some other -> failwith ("reduce_frame did not expect f with type " ^ (string_of_sort other))
  in
  (* gather the SL->GRASS predicates *)
  let suffix_s = Str.regexp ".*_struct$" in
  let suffix_d = Str.regexp ".*_domain$" in
  let pred_end_with s t = match t with
    | App (FreeSym id, _, _) -> Str.string_match s (str_of_ident id) 0
    | _ -> false
  in
  let gts = ground_terms (mk_and fs) in
  (*let structs = TermSet.filter (pred_end_with suffix_s) gts in*)
  let domains = TermSet.filter (pred_end_with suffix_d) gts in
  (*TermSet.iter (fun t -> print_endline (string_of_term t)) structs;*)
  (*extract the args, struct has an extra domain arg *)
  let pred_name id =
    let s = str_of_ident id in
      String.sub s 0 (String.length s - 7)
  in
  let decompose t = match t with
    | App (FreeSym id, args, _) ->
      if pred_end_with suffix_s t then
        let r_args = List.rev args in
          (pred_name id, List.rev (List.tl r_args), Some (List.hd r_args))
      else if pred_end_with suffix_d t then
        (pred_name id, args, None)
      else failwith "pred is not struct or domain"
    | _ -> failwith "expected pred"
  in
  (*let d_struct = List.map decompose (TermSet.elements structs) in*)
  let d_domain = List.map decompose (TermSet.elements domains) in
  (* the self framing predicates *)
  let expand_frame2 x a flds =
    let prev, post = List.fold_left (fun (acc1, acc2) x -> (acc2, x::acc1)) ([],[]) flds in
    let paired = List.combine prev post in
    let changed, unchanged = List.partition (fun (a,b) -> a <> b) paired in
    (*todo get the domains/struct which have a changed field*)
    let affected =
      List.filter
        (fun (_, args, _) ->
          List.exists
            (fun a -> List.exists (fun c -> (fst c) = a) changed)
            args)
        d_domain
    in
    let pred_before_after =
      List.map
        (fun (id, args, fp) ->
          ( id,
            args,
            List.map (fun a -> try List.assoc a paired with Not_found -> a) args,
            fp )
        )
        affected
    in
    (*TODO universal quantification ?*)
    let self_frame (id, args_before, args_after, fp) =
      let id_s = mk_ident (id ^ "_struct") in
      let id_d = mk_ident (id ^ "_domain") in
      let b_d = mk_free_app ~srt:(Set Loc) id_d args_before in
      let a_d = mk_free_app ~srt:(Set Loc) id_d args_after in
      let fp = match fp with
        | Some fp -> fp
        | None -> b_d
      in
      let b_s = mk_pred id_s (args_before @ [fp]) in
      let a_s = mk_pred id_s (args_after @ [fp]) in
      let cond = mk_eq (mk_inter [fp; x]) (mk_empty (Some (Set Loc))) in
      let consequences = smk_and [mk_eq b_d a_d; mk_iff b_s a_s] in
        mk_comment "self framing" (mk_implies cond consequences)
    in
    smk_and (List.map self_frame pred_before_after), paired
  in
  let rec process f fields = match f with
    | Atom (App (Frame, [x; a; f; f'], _)) when f <> f' ->
        let fields1 = 
          try 
            let _, flds = TermMap.find x fields in
            TermMap.add x (a, f :: f' :: flds) fields
          with Not_found -> fields
        in
        expand_frame x a f f', fields1
    | BoolOp (op, fs) -> 
        let fs1, fields1 = 
          List.fold_right (fun f (fs1, fields1) ->
            let f1, fields1 = process f fields1 in
            f1 :: fs1, fields1)
            fs ([], fields)
        in
        BoolOp (op, fs1), fields1
    | Binder (b, vs, f, a) ->
        let f1, fields1 = process f fields in
        Binder (b, vs, f1, a), fields1
    | _ -> f, fields        
  in
  let reach_frames, fields =
    List.fold_right  
      (fun f (fs1, fields1) ->
        let f1, fields1 = process f fields1 in
        f1 :: fs1, fields1)
      fs ([], TermMap.empty)
  in
  let pred_frames, framed_fields =
    TermMap.fold 
      (fun x (a, flds) (pred_frames, framed_fields) ->
        let pred_frame, paired_flds = expand_frame2 x a flds in
        (if !Config.optSelfFrame then (pred_frame :: pred_frames)
        else pred_frames),
        paired_flds @ framed_fields
      ) fields ([], [])
  in
  reach_frames @ pred_frames, framed_fields
  
let open_axioms open_cond axioms = 
  if !Config.instantiate then
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
          Binder (b, vs1, f, a1), generators1
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
  else axioms, []

let isFld f = function (_, Fld _) -> true | _ -> false

let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars


(** Reduce all set constraints by adding appropriate instances of the axioms of set operations.
 ** Assumes that f is typed and in negation normal form *)
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
  let gts = TermSet.fold (fun t gts1 -> TermSet.add (unflatten t) gts1) gts TermSet.empty in
  let gts1 = TermSet.union gts (ground_terms (mk_and fs1)) in
  let classes = CongruenceClosure.congr_classes fs1 gts1 in
  let set_ax, _ = open_axioms isFunVar (Axioms.set_axioms ()) in
  let set_ax1 = instantiate_with_terms true set_ax classes in
  rev_concat [fs1; set_ax1], gts1

let reduce_sets fs gts =
  if !Config.keep_sets 
  then reduce_sets_with_axioms fs gts 
  else reduce_sets_to_predicates fs gts


let print_terms terms =
  print_endline "===============================================";
  TermSet.iter (fun t -> print_term stdout t; print_newline ())
    terms;
  print_endline "==============================================="
  

(** Adds instantiated theory axioms for the entry point function to formula f
 ** Assumes that f is typed and that all frame predicates have been reduced *)
let instantiate_ep fs =
  let gts = TermSet.add mk_null (ground_terms (mk_and fs)) in
  let ep_ax, generators = open_axioms isFunVar (Axioms.ep_axioms ()) in
  let gts_eps = InstGen.generate_terms generators gts in
  let classes = CongruenceClosure.congr_classes fs gts_eps in
  let ep_ax1 = instantiate_with_terms true ep_ax classes in
  (*print_endline "===============================================";
  TermSet.iter (fun t -> print_term stdout t; print_newline ())
   (TermSet.filter (function App (EntPnt, _, _) -> true | _ -> false) gts_eps);
  print_endline "===============================================";*)
  fs, ep_ax1, gts_eps
 

let propagate_field_reads fs gts framed_fields =
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
    let fld_partition1 =
      TermSet.fold (fun t partition -> 
        match t with
        | App (Write, fld1 :: _, _) as fld2 -> 
            Puf.union partition (TermMap.find fld1 fld_map) (TermMap.find fld2 fld_map)
        | _ -> partition)
      gts fld_partition0
    in
    let fld_partition =
      List.fold_left 
        (fun partition (fld1, fld2) ->
          match range_sort_of_field fld1 with
          | Int when !Config.stratify -> partition
          | _ -> 
              Puf.union partition (TermMap.find fld1 fld_map) (TermMap.find fld2 fld_map))
        fld_partition1 framed_fields
    in
    fld_partition, fld_map, fields
  in
  let partition_of fld =
    let p = 
      try Puf.find fld_partition (TermMap.find fld fld_map) 
      with Not_found -> failwith ("did not find field " ^ (string_of_term fld)) 
    in
    let res = TermSet.filter (fun fld1 -> Puf.find fld_partition (TermMap.find fld1 fld_map) = p) fields in
    (* print_endline ("partition of " ^ string_of_term fld); *)
    res
  in
  TermSet.fold
    (fun t gts1 -> match t with
    | App (Read, [fld; arg], _) 
    | App (Write, [fld; arg; _], _) -> 
        TermSet.fold (fun fld1 gts1 -> 
          TermSet.add (mk_read fld1 arg) gts1) (partition_of fld) gts1
    | _ -> gts1)
    gts gts,
  partition_of


(** Adds instantiated theory axioms for graph reachability to formula f.
 ** Assumes that f is typed *)
let reduce_reach fs gts framed_fields =
  let basic_pt_flds = TermSet.filter (has_sort (Fld Loc) &&& is_free_const) gts in
  (* instantiate null axioms *)
  let classes =  CongruenceClosure.congr_classes fs gts in
  (* let _ = List.iter (List.iter (fun t -> print_endline (string_of_term t))) classes in *)
  let null_ax, _ = open_axioms isFld (Axioms.null_axioms ()) in
  let null_ax1 = instantiate_with_terms false null_ax (CongruenceClosure.restrict_classes classes basic_pt_flds) in
  let fs1 = null_ax1 @ fs in
  let gts = TermSet.union (ground_terms (smk_and null_ax1)) gts in
  (* propagate read terms *)
  let gts1, partition_of = propagate_field_reads fs1 gts framed_fields in
  (* generate instances of all read over write axioms *)
  let read_write_ax = 
    TermSet.fold (fun t write_ax ->
      match t with
      | App (Write, [fld; loc1; loc2], _) ->
          fst (open_axioms isFunVar (Axioms.read_write_axioms fld loc1 loc2)) @ write_ax
      | _ -> write_ax) gts1 []
  in
  (*let read_write_ax2, generators = open_axioms isFunVar (Axioms.read_write_axioms_closed ()) in
  let gts1 = generate_terms generators gts in
  let _ = print_terms gts1 in*)
  let classes1 = CongruenceClosure.congr_classes fs1 gts1 in
  let read_write_ax1 = instantiate_with_terms true read_write_ax classes1 in
  (*print_forms stdout read_write_ax1;*)
  let classes2 = CongruenceClosure.congr_classes (fs1 @ read_write_ax1) gts1 in
  (* instantiate the variables of sort Fld in all reachability axioms *)
  let basic_reach_flds = 
    fold_terms (fun flds -> function
      | App (Btwn, Var _ :: _, _) -> flds
      | App (Btwn, fld :: _, _) -> TermSet.union (partition_of fld) flds
      | _ -> flds)
      TermSet.empty (smk_and fs1)
  in
  let reach_write_ax = 
    TermSet.fold (fun t write_ax ->
      match t with
      | App (Write, [fld; loc1; loc2], _) ->
          if TermSet.mem fld basic_reach_flds 
          then fst (open_axioms isFunVar (Axioms.reach_write_axioms fld loc1 loc2)) @ write_ax
          else write_ax
      | _ -> write_ax) gts1 []
  in
  let non_updated_flds = 
    TermSet.filter 
      (fun t -> List.for_all 
	  (function 
	    | (App (Write, _, _)) -> false 
	    | _ -> true) (CongruenceClosure.class_of t classes))
      basic_reach_flds
  in
  let reach_ax, _ = open_axioms isFld (Axioms.reach_axioms ()) in
  let reach_ax1 = instantiate_with_terms false reach_ax (CongruenceClosure.restrict_classes classes2 non_updated_flds) in
  (* generate local instances of all axioms in which variables occur below function symbols *)
  let reach_ax2 = instantiate_with_terms true (fst (open_axioms isFunVar reach_ax1)) classes2 in
  rev_concat [fs1; reach_ax2; read_write_ax1; reach_write_ax], gts1

let reduce_remaining fs gts =
  (* generate local instances of all remaining axioms in which variables occur below function symbols *)
  let classes = CongruenceClosure.congr_classes fs gts in
  let fs1, _ = open_axioms isFunVar fs in
  instantiate_with_terms true fs1 classes

(** Reduces the given formula to the target theory fragment, as specified by the configuration.
 ** Assumes that f is typed *)
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
  let fs1 = split_ands [] [f1] in
  let fs11 = massage_field_reads fs1 in
  let fs2 = List.map reduce_exists fs11 in
  (* no reduction step should introduce implicit or explicit existential quantifiers after this point *)
  let fs2, ep_axioms, gts = instantiate_ep fs2 in
  let fs2, framed_fields = reduce_frame fs2 in
  let fs31 = factorize_axioms (split_ands [] fs2) in
  let fs4, gts1 = reduce_sets (fs31 @ ep_axioms) gts in
  let fs5, gts2 = reduce_reach fs4 gts1 framed_fields in
  let fs6 = (*Simplify.simplify*) (reduce_remaining fs5 gts2) in
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
