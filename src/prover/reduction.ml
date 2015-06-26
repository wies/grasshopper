(** {5 Reduction from GRASS to SMT} *)

open Util
open Grass
open GrassUtil
open InstGen
open SimplifyGrass

 
(** Remove binders for universal quantified variables in [axioms] that satisfy the condition [open_cond]. *)
let open_axioms ?(force=false) open_cond axioms =
  let extract_generators generators a =
    List.fold_right 
      (fun ann (generators, a1) ->
        match ann with
        | TermGenerator (g, t) ->
            let gen = (g, t) in
            gen :: generators, a1
        | _ -> generators, ann :: a1
      ) a (generators, [])
  in
  let rec open_axiom generators = function
    | Binder (b, [], f, a) ->
        let f1, generators1 = open_axiom generators f in
        let generators2, a1 = extract_generators generators a in
        Binder (b, [], f1, a1), generators2
    | Binder (b, vs, f, a) -> 
        (* extract term generators *)
        let generators1, a1 = extract_generators generators a in
        let vs1 = List.filter (~~ (open_cond (annotate f a))) vs in
        let f1, generators2 = open_axiom generators1 f in
        if !Config.instantiate || force then
          Binder (b, vs1, f1, a1), generators2
        else 
          Binder (b, vs, f1, a1), generators2
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

(** Open condition that checks whether the given sorted variable is a field. *)
let isFld f = function (_, Map (Loc _, _)) -> true | _ -> false

(* Open condition that checks whether the given sorted variable appears below a function symbol. *) 
let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v -> IdSrtSet.mem v fvars

(** Compute the set of generated ground terms for formulas [fs] *)
let generated_ground_terms fs =
  let _, generators = open_axioms isFunVar fs in
  let gts = generate_terms generators (ground_terms ~include_atoms:true (mk_and fs)) in
  gts
  
(** Eliminate all implicit and explicit existential quantifiers using skolemization.
 ** Assumes that [f] is typed and in negation normal form. *)
let elim_exists =
  let e = fresh_ident "?e" in
  let rec elim_neq bvs = function
    | BoolOp (Not, [Atom (App (Eq, [s1; s2], _), a)]) as f ->
	(match sort_of s1 with
	| Set srt ->
	    let ve = mk_var srt e in
	    mk_exists [(e, srt)] (smk_or [smk_and [smk_elem ~ann:a ve s1; mk_not (smk_elem ~ann:a ve s2)];
					 smk_and [smk_elem ~ann:a ve s2; mk_not (smk_elem ~ann:a ve s1)]])
	| _ -> f)
    | BoolOp (Not, [Atom (App (Disjoint, [s1; s2], _), a)]) when bvs = [] ->
        let srt = element_sort_of_set s1 in
        elim_neq bvs (mk_not (Atom (App (Eq, [mk_inter [s1; s2]; mk_empty (Set srt)], Bool), a)))
    | BoolOp (Not, [Atom (App (SubsetEq, [s1; s2], _), a)]) when bvs = [] ->
	let srt = element_sort_of_set s1 in
	let ve = mk_var srt e in
	mk_exists [(e, srt)] (annotate (smk_and [smk_elem ve s1; mk_not (smk_elem ve s2)]) a)
    | BoolOp (op, fs) -> smk_op op (List.map (elim_neq bvs) fs)
    | Binder (Exists, vs, f, a) -> Binder (Exists, vs, elim_neq bvs f, a)
    | Binder (Forall, vs, f, a) -> Binder (Forall, vs, elim_neq (bvs @ vs) f, a)
    | f -> f
  in
  List.map (fun f -> 
    let f1 = elim_neq [] f in
    let f2 = propagate_exists f1 in
    skolemize f2)

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
        let names, other_annots = List.partition (function Name _ -> true | _ -> false) a in 
        let fact_axiom = annotate (mk_implies p (Binder (Forall, vs, f1, other_annots))) names in
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
  let process (fs1, axioms) f = 
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
      | App (_, _, Map (Loc _, _)) as fld -> 
          n+1, TermMap.add fld n fld_map, TermSet.add fld fields
      | _ -> n, fld_map, fields)
        gts (0, TermMap.empty, TermSet.empty)
    in
    let rec collect_eq partition = function
      | BoolOp (Not, f) -> partition
      | BoolOp (op, fs) -> List.fold_left collect_eq partition fs
      | Atom (App (Eq, [App (_, _, Map (Loc _, _)) as fld1; fld2], _), _) ->
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


(** Compute term generators for Btwn fields *)
let btwn_field_generators fs =
  let make_generators acc f =
    let ts = terms_with_vars f in
    let btwn_fields t flds = match t with
      | App (Btwn, fld :: _, _) ->
          let vs = fv_term fld in
          if IdSet.is_empty vs
          then flds
          else TermSet.add fld flds
      | _ -> flds
    in
    let btwn_flds = TermSet.fold btwn_fields ts TermSet.empty in
    let process t acc = match t with
      | App (FreeSym _, ts, _) ->
          TermSet.fold (fun fld acc ->
            if IdSet.subset (fv_term fld) (fv_term t)
            then ([Match (t, [])], [mk_known fld]) :: acc
            else acc)
            btwn_flds acc
      | _ -> acc
    in
    TermSet.fold process ts acc
  in
  List.fold_left make_generators [] fs 
    
    
(** Add axioms for frame predicates. *)
let add_frame_axioms fs =
  let gs = ground_terms ~include_atoms:true (mk_and fs) in
  let frame_sorts =
    TermSet.fold
      (fun t frame_sorts ->
        match t with
        | App (Frame, [_; _; f; _], _) ->
            SortSet.add (sort_of f) frame_sorts
        | _ -> frame_sorts
      )
      gs SortSet.empty
  in
  SortSet.fold
    (fun srt fs ->
      match srt with
      | Map (Loc srt1, srt2) ->
          Axioms.frame_axioms srt1 srt2 @ fs
      | _ -> fs)
    frame_sorts fs
 

let rec valid = function
  | BoolOp (op, fs) ->
      List.for_all valid fs
  | Binder (Forall, [], f, ann) ->
      let has_gen = List.for_all (function TermGenerator _ -> false | _ -> true) ann in
      if not has_gen then print_form stdout f;
      valid f && has_gen
  | Binder (_, _, f, ann) ->
      valid f
  | Atom (_, ann) -> 
      true


(** Simplifies set constraints and adds axioms for set operations.
 ** Assumes that f is typed and in negation normal form. *)
let add_set_axioms fs =
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
  let rec simplify = function
    | BoolOp (op, fs) -> BoolOp (op, List.map simplify fs)
    | Binder (b, vs, f, a) -> Binder (b, vs, simplify f, a)
    | Atom (App (Disjoint, [t1; t2], _), a) when not !Config.abstract_preds ->
        let srt = element_sort_of_set t1 in
        let t11 = unflatten t1 in
        let t21 = unflatten t2 in
        Atom (mk_eq_term (mk_empty (Set srt)) (mk_inter [t11; t21]), a)
    | Atom (App (SubsetEq, [t1; t2], _), a) when not !Config.abstract_preds -> 
        let t11 = unflatten t1 in
        let t21 = unflatten t2 in
        Atom (mk_eq_term t21 (mk_union [t11; t21]), a)
    | Atom (t, a) -> Atom (unflatten t, a)
  in
  let fs1 = List.map simplify fs in
  let elem_srts = 
    let set_srts =
      List.fold_left 
        (fun acc f -> SortSet.union (sorts f) acc)
        SortSet.empty fs1
    in
    SortSet.fold (fun set_srt acc -> 
      match set_srt with 
      | Set srt -> srt :: acc
      | _ -> acc) set_srts []
  in
  rev_concat [fs1; Axioms.set_axioms elem_srts]

(** Compute the set of struct sorts of the domain sort from the set of field terms [flds]. *)
let struct_sorts_of_fields flds =
  TermSet.fold
    (fun fld structs ->
      match fld with
      | App (_, _, Map (Loc srt, _)) -> SortSet.add srt structs
      | _ -> structs)
    flds SortSet.empty

let array_sorts ts =
  TermSet.fold
    (fun t srts ->
      match t with
      | App (_, _, Loc (Array srt))
      | App (_, _, Loc (ArrayCell srt))
        -> SortSet.add srt srts
      | _ -> srts)
    ts SortSet.empty
    
(** Adds theory axioms for the entry point function to formulas [fs].
 ** Assumes that all frame predicates have been reduced in formulas [fs]. *)
let add_ep_axioms fs =
  let gts = generated_ground_terms fs in
  let struct_sorts =
    TermSet.fold
      (fun t struct_sorts -> match t with
      | App (_, _, Map(Loc srt1, Loc srt2)) 
      | Var (_, Map(Loc srt1, srt2)) when srt1 = srt2 -> SortSet.add srt1 struct_sorts
      | _ -> struct_sorts)
      gts SortSet.empty
  in
  let axioms = SortSet.fold (fun srt axioms -> Axioms.ep_axioms srt @ axioms) struct_sorts [] in
  axioms @ fs
 
let add_read_write_axioms fs =
  let gts = ground_terms ~include_atoms:true (mk_and fs) in
  let has_loc_field_sort = function
    | App (_, _, Map(Loc id1, Loc id2)) -> (*id1 = id2*) true
    | _ -> false
  in
  let basic_pt_flds = TermSet.filter (has_loc_field_sort &&& is_free_const) gts in
  let basic_structs = struct_sorts_of_fields basic_pt_flds in
  (* instantiate null axioms *)
  let axioms = SortSet.fold (fun srt axioms -> Axioms.null_axioms srt @ axioms) basic_structs [] in
  let null_ax, _ = open_axioms ~force:true isFld axioms in
  let classes = CongruenceClosure.congr_classes fs gts in
  (* CAUTION: not forcing the instantiation here would yield an inconsistency with the read/write axioms *)
  let null_ax1 = instantiate_with_terms ~force:true false null_ax (CongruenceClosure.restrict_classes classes basic_pt_flds) in
  let fs1 = null_ax1 @ fs in
  let gts = TermSet.union (ground_terms ~include_atoms:true (mk_and null_ax1)) gts in
  let field_sorts = TermSet.fold (fun t srts ->
    match sort_of t with
    | Map (Loc _, _) as srt -> SortSet.add srt srts
    | _ -> srts)
      gts SortSet.empty
  in
  (* propagate read terms *)
  let read_propagators =
    SortSet.fold (function
      | Map (Loc ssrt, srt) -> fun propagators ->
          let f1 = fresh_ident "?f", field_sort ssrt srt in
          let fld1 = mk_var (snd f1) (fst f1) in
          let f2 = fresh_ident "?g", field_sort ssrt srt in
          let fld2 = mk_var (snd f2) (fst f2) in
          let d = fresh_ident "?d" in
          let dvar = mk_var srt d in
          let loc1 = Axioms.loc1 ssrt in
          let loc2 = Axioms.loc2 ssrt in
          let set1 = Axioms.set1 ssrt in
          let set2 = Axioms.set2 ssrt in
          (* f = g, x.f -> x.g *)
          ([Match (mk_eq_term fld1 fld2, []);
            Match (mk_read fld1 loc1, [])],
           [mk_read fld2 loc1]) ::
          (* f = g, x.g -> x.f *)
          ([Match (mk_eq_term fld1 fld2, []);
            Match (mk_read fld2 loc1, [])],
           [mk_read fld1 loc1]) :: 
          (* f [x := d], y.(f [x := d]) -> y.f *)
          ([Match (mk_write fld1 loc1 dvar, []);
            Match (mk_read (mk_write fld1 loc1 dvar) loc2, [])],
           [mk_read fld1 loc2]) ::
          (* f [x := d], y.f -> y.(f [x := d]) *)
          ([Match (mk_write fld1 loc1 dvar, []);
            Match (mk_read fld1 loc2, [])],
           [mk_read (mk_write fld1 loc1 dvar) loc2]) ::
          (* Frame (x, a, f, g), y.g -> y.f *)
          ([Match (mk_frame_term set1 set2 fld1 fld2, []);
            Match (mk_read fld2 loc1, [])],
           [mk_read fld1 loc1]) ::
          (* Frame (x, a, f, g), y.f -> y.g *)
          ([Match (mk_frame_term set1 set2 fld1 fld2, []);
            Match (mk_read fld1 loc1, [])],
           [mk_read fld2 loc1]) ::
          propagators
      | _ -> fun propagators -> propagators)
      field_sorts []
  in
  (* generate instances of all read over write axioms *)
  let read_write_ax = 
    let generators_and_axioms =
      TermSet.fold (fun t acc ->
        match t with
        | App (Write, [fld; _; _], _) ->
            Axioms.read_write_axioms fld @ acc
        | _ -> acc) gts []
    in
    generators_and_axioms 
  in
  rev_concat [read_write_ax; fs1], read_propagators, gts




(** Adds instantiated theory axioms for graph reachability to formula f.
 ** Assumes that f is typed. *)
let add_reach_axioms fs gts =
  let struct_sorts =
    SortSet.fold
      (fun srt struct_sorts -> match srt with
      | Map(Loc srt1, Loc srt2) when srt1 = srt2 ->
          SortSet.add srt1 struct_sorts
      | _ -> struct_sorts)
      (sorts (mk_and fs)) SortSet.empty
  in
  let classes = CongruenceClosure.congr_classes fs gts in
  let axioms =
    SortSet.fold
      (fun srt axioms -> Axioms.reach_axioms classes srt @ Axioms.reach_write_axioms srt @ axioms)
      struct_sorts []
  in
  rev_concat [axioms; fs], gts

let add_array_axioms fs gts =
  let srts = array_sorts gts in
  let axioms = SortSet.fold (fun srt axioms -> Axioms.array_axioms srt @ axioms) srts [] in
  axioms @ fs
  
let instantiate read_propagators fs gts =
  (* generate local instances of all remaining axioms in which variables occur below function symbols *)
  let fs1, generators = open_axioms isFunVar fs in
  let _ =
    if Debug.is_debug 1 then
      begin
        print_endline "ground terms:";
        TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) gts;
      end  
  in
  let btwn_gen = btwn_field_generators fs in
  let gts1 = generate_terms (read_propagators @ btwn_gen @ generators) gts in
  let _ =
    if Debug.is_debug 1 then
      begin
        print_endline "generated terms:";
        TermSet.iter (fun t -> print_endline ("  " ^ (string_of_term t))) (TermSet.diff gts1 gts)
      end
  in
  let rec is_equation = function
    | BoolOp (_, fs) -> List.for_all is_equation fs
    | Binder (Forall, _, f, _) -> is_equation f
    | Atom (App (Eq, _, _), _) -> true
    | Atom (App (FreeSym _, _, _), _) -> true
    | _ -> false
  in
  let equations, others = List.partition is_equation fs1 in
  let classes = CongruenceClosure.congr_classes fs gts1 in
  let eqs = instantiate_with_terms true equations classes in
  let gts1 = TermSet.union (ground_terms ~include_atoms:true (mk_and eqs)) gts1 in 
  let classes = CongruenceClosure.congr_classes (List.rev_append eqs fs) gts1 in
  let implied =
    List.fold_left
      (fun acc cls ->
        if (List.length cls > 1 && sort_of (List.hd cls) <> Bool) then
          let h = List.hd cls in
          let eq = List.map (fun t -> GrassUtil.mk_eq h t) (List.tl cls) in
          List.rev_append eq acc
        else
          acc
      )
      []
      classes
  in
  List.rev_append implied (List.rev_append eqs (instantiate_with_terms true others classes)), gts1

let add_terms fs gts =
  if not !Config.smtpatterns && !Config.instantiate then fs else
  (*let gts_fs = ground_terms (mk_and fs) in*)
  let extra_gts = (*TermSet.diff gts gts_fs*) gts in
  let fs1 = 
    TermSet.fold (fun t fs1 ->
      match sort_of t with
      | Bool -> fs1
      | srt ->
          mk_pred ("inst-closure", 0) [t] :: fs1)
      extra_gts fs
  in fs1

let encode_labels fs =
  let mk_label annots f = 
    let lbls = 
      Util.partial_map 
        (function 
          | Label id -> Some (mk_pred id [])
          | _ -> None) 
        annots
    in
    mk_and (mk_or (f :: List.map mk_not lbls) :: lbls)
  in
  let rec el = function
    | Binder (b, vs, f, annots) ->
        let f1 = el f in
        mk_label annots (Binder (b, vs, f1, annots))
    | (BoolOp (Not, [Atom (_, annots)]) as f)
    | (Atom (_, annots) as f) ->
        mk_label annots f
    | BoolOp (op, fs) ->
        BoolOp (op, List.map el fs)
  in List.rev_map el fs

let add_split_lemmas fs gts =
  if not !Config.split_lemmas then fs else
  let structs =
    TermSet.fold (fun t structs ->
      match sort_of t with
      | Loc srt -> SortSet.add srt structs
      | _ -> structs)
      gts SortSet.empty
  in
  let classes = CongruenceClosure.congr_classes fs (generated_ground_terms fs) in
  let add_lemmas srt fs1 =
    let loc_gts =
      TermSet.filter (fun t -> sort_of t = Loc srt) gts
    in
    let classes = CongruenceClosure.restrict_classes classes loc_gts in
    let rec lem fs1 = function
      | [] -> fs1
      | c :: cs ->
          let t = List.hd c in
          List.fold_left
            (fun fs1 c ->
              let t1 = List.hd c in
              mk_or [mk_eq t t1; mk_neq t t1] :: fs1)
            fs1 cs
    in
    lem fs1 classes
  in
  SortSet.fold add_lemmas structs fs
    
(** Reduces the given formula to the target theory fragment, as specified by the configuration. *)
let reduce f =
  (* split f into conjuncts and eliminate all existential quantifiers *)
  let rec split_ands acc = function
    | BoolOp(And, fs) :: gs -> 
        split_ands acc (fs @ gs)
    | Binder(_, [], BoolOp(And, fs), a) :: gs ->
        split_ands acc (List.map (fun f -> annotate f a) fs @ gs)
    | f :: gs ->
        split_ands (f :: acc) gs
    | [] -> List.rev acc
  in
  let f1 = nnf f in
  let fs = split_ands [] [f1] in
  (* *)
  let fs = elim_exists fs in
  (* no reduction step should introduce implicit or explicit existential quantifiers after this point *)
  (* some formula rewriting that helps the SMT solver *)
  let fs = massage_field_reads fs in
  let fs = simplify_sets fs in
  let fs = pull_up_equalities fs in
  let fs = add_ep_axioms fs in
  let fs = add_frame_axioms fs in
  let fs = factorize_axioms (split_ands [] fs) in
  let fs = add_set_axioms fs in
  let fs, read_propagators, gts = add_read_write_axioms fs in
  let fs, gts = add_reach_axioms fs gts in
  let fs = add_array_axioms fs gts in
  let fs = if !Config.named_assertions then fs else List.map strip_names fs in
  let _ =
    if Debug.is_debug 1 then begin
      print_endline "VC before instantiation:";
      print_form stdout (mk_and fs);
      print_newline ()
    end
  in
  let fs, gts = instantiate read_propagators fs gts in
  let fs = add_terms fs gts in
  let fs = encode_labels fs in
  let fs = add_split_lemmas fs gts in
  fs
