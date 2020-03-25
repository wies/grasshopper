(** {5 Reduction from GRASS to SMT} *)

open Util
open Grass
open GrassUtil
open Axioms
open SimplifyGrass
  
(** Eliminate all implicit and explicit existential quantifiers using skolemization.
 ** Assumes that [f] is typed and in negation normal form. *)
let elim_exists =
  let e = fresh_ident "?e" in
  let rec elim_neq seen_adts bvs = function
    | BoolOp (Not, [Atom (App (Eq, [t1; t2], _), a)]) as f when bvs = [] ->
	(match sort_of t1 with
	| Set srt ->
	    let ve = mk_var srt e in
	    mk_exists [(e, srt)] (smk_or [smk_and [smk_elem ~ann:a ve t1; mk_not (smk_elem ~ann:a ve t2)];
					 smk_and [smk_elem ~ann:a ve t2; mk_not (smk_elem ~ann:a ve t1)]])
        | Map (dsrts, rsrt) ->
            let dom_vs = List.map (fun dsrts -> List.map (fun srt -> fresh_ident "?i", srt) dsrts) [dsrts] in
            let dom_vts = List.map (fun vs -> List.map (fun (v, srt) -> mk_var srt v) vs) dom_vs in
            let mk_reads t = List.fold_left (fun t_read vts -> mk_read t_read vts) t dom_vts in
            let t1_read = mk_reads t1 in
            let t2_read = mk_reads t2 in
            let vs = List.flatten dom_vs in
            mk_and [f; elim_neq seen_adts bvs (mk_exists vs (annotate (mk_neq t1_read t2_read) a))]
        | Adt (id, adts) when not @@ IdSet.mem id seen_adts ->
            let cstrs = List.assoc id adts in
            let expand new_vs = function
              | App (Constructor cid, ts, _) -> new_vs, [(cid, mk_true, ts)]
              | t ->
                  match cstrs with
                  | [cid, dstrs] ->
                      let ts =
                        List.map (fun (id, srt) -> mk_destr srt id t) dstrs 
                      in
                      (new_vs, [cid, mk_true, ts])
                  | _ ->
                      List.fold_left
                        (fun (new_vs, cases) (cid, dstrs) ->
                          let vs = List.map (fun (id, srt) -> fresh_ident "?x", unfold_adts adts srt) dstrs in
                          let vts = List.map (fun (v, srt) -> mk_var srt v) vs in
                          vs @ new_vs, (cid, mk_eq t (mk_constr (Adt (id, adts)) cid vts), vts) :: cases
                        ) (new_vs, []) cstrs
            in
            let new_vs1, t1_cases = expand [] t1 in
            let new_vs2, t2_cases = expand new_vs1 t2 in
            let cases = List.fold_left
              (fun cases (cid1, def_t1, args1) ->
                List.fold_left
                  (fun cases (cid2, def_t2, args2) ->
                    if cid1 = cid2 then
                      let seen_adts1 = IdSet.add id seen_adts in
                      let sub_cases =
                        List.map2 (fun arg1 arg2 -> elim_neq seen_adts1 bvs (mk_neq arg1 arg2)) args1 args2
                      in
                      mk_and [def_t1; def_t2; mk_or sub_cases] :: cases
                    else mk_and [def_t1; def_t2] :: cases
                  ) cases t2_cases
              ) [] t1_cases
            in
            mk_exists ~ann:a new_vs2 (mk_or cases)
	| _ -> f)
    | BoolOp (Not, [Atom (App (Disjoint, [s1; s2], _), a)]) when bvs = [] ->
        let srt = element_sort_of_set s1 in
        elim_neq seen_adts bvs (mk_not (Atom (App (Eq, [mk_inter [s1; s2]; mk_empty (Set srt)], Bool), a)))
    | BoolOp (Not, [Atom (App (SubsetEq, [s1; s2], _), a)]) when bvs = [] ->
	let srt = element_sort_of_set s1 in
	let ve = mk_var srt e in
	mk_exists [(e, srt)] (annotate (smk_and [smk_elem ve s1; mk_not (smk_elem ve s2)]) a)
    | BoolOp (op, fs) ->
        smk_op op (List.map (elim_neq IdSet.empty bvs) fs)
    | Binder (Exists, vs, f, a) ->
        mk_exists ~ann:a vs (elim_neq seen_adts bvs f)
    | Binder (Forall, vs, f, a) ->
        mk_forall ~ann:a vs (elim_neq seen_adts (bvs @ vs) f)
    | f -> f 
  in
  List.map (fun f -> 
    let f1 = elim_neq IdSet.empty [] f in
    let f2 = propagate_exists_up f1 in
    let f3 = skolemize f2 in
    f3)

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
      | App (_, _, Map (Loc _ :: _, _)) as fld -> 
          n+1, TermMap.add fld n fld_map, TermSet.add fld fields
      | _ -> n, fld_map, fields)
        gts (0, TermMap.empty, TermSet.empty)
    in
    let rec collect_eq partition = function
      | BoolOp (Not, f) -> partition
      | BoolOp (op, fs) -> List.fold_left collect_eq partition fs
      | Atom (App (Eq, [App (_, _, Map (Loc _ :: _, _)) as fld1; fld2], _), _) ->
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
      | Map ((Loc ssrt :: dsrts), rsrt) ->
          Axioms.frame_axioms ssrt dsrts rsrt @ fs
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
  let _split ts = List.fold_left (fun (ts1, ts2) t -> (ts2, t :: ts1)) ([], []) ts in
  let elem_srts = 
    let set_srts =
      List.fold_left 
        (fun acc f -> SortSet.union (sorts f) acc)
        SortSet.empty fs
    in
    SortSet.fold (fun set_srt acc -> 
      match set_srt with 
      | Set srt -> srt :: acc
      | _ -> acc) set_srts []
  in
  rev_concat [fs; Axioms.set_axioms elem_srts]

(** Compute the set of struct sorts of the domain sort from the set of field terms [flds]. *)
let struct_sorts_of_fields flds =
  TermSet.fold
    (fun fld structs ->
      match fld with
      | App (_, _, Map (Loc srt :: _, _)) -> SortSet.add srt structs
      | _ -> structs)
    flds SortSet.empty

let array_sorts fs =
  let rec ars srts = function
    | App (_, ts, srt) ->
        let srts1 = match srt with
        | Loc (Array srt) | Loc (ArrayCell srt) -> SortSet.add srt srts
        | _ -> srts
        in
        List.fold_left ars srts1 ts
    | _ -> srts
  in
  List.fold_left (fold_terms ars) SortSet.empty fs 
    
(** Adds theory axioms for the entry point function to formulas [fs].
 ** Assumes that all frame predicates have been reduced in formulas [fs]. *)
let add_ep_axioms fs =
  (*let gts = generated_ground_terms fs in*)
  let rec get_struct_sorts acc = function
    | App (_, ts, srt) ->
        let acc = List.fold_left get_struct_sorts acc ts in
        (match srt with
        | Map([Loc srt1], Loc srt2) when srt1 = srt2 -> SortSet.add srt1 acc
        | _ -> acc)
    | Var (_, Map([Loc srt1], srt2)) when srt1 = srt2 -> SortSet.add srt1 acc
    | Var _ -> acc
  in
  let struct_sorts = fold_terms get_struct_sorts SortSet.empty (mk_and fs) in
  let axioms = SortSet.fold (fun srt axioms -> Axioms.ep_axioms srt @ axioms) struct_sorts [] in
  axioms @ fs

let get_read_propagators gts =
  let field_sorts = TermSet.fold (fun t srts ->
    match sort_of t with
    | (Loc ArrayCell _ | Map (_ :: _, _)) as srt -> SortSet.add srt srts
    | Adt (_, adts) ->
        List.fold_left
          (fun srts (id, _) -> SortSet.add (Adt (id, adts)) srts)
          srts adts
    | _ -> srts)
      gts SortSet.empty
  in
  let add_propagators = function
    | Adt (id, adts) -> fun propagators ->
          let s = fresh_ident "?s" in
          let t = fresh_ident "?t" in
          let cstrs = List.assoc id adts in
          let adt_srt = Adt (id, adts) in
          let s = mk_var adt_srt s in
          let t = mk_var adt_srt t in
          let destrs = flat_map (fun (_, destrs) -> destrs) cstrs in
          let propagators =
            List.fold_left
              (fun propagators (destr, srt) ->
                let srt = unfold_adts adts srt in
                ([Match (mk_eq_term s t, []);
                  (* s == t, s.destr -> t.destr *)
                  Match (mk_destr srt destr s, [])],
                 [mk_destr srt destr t]) ::
                ([Match (mk_eq_term s t, []);
                  (* s == t, t.destr -> s.destr *)
                  Match (mk_destr srt destr t, [])],
                 [mk_destr srt destr s]) :: propagators
              )
              propagators destrs
          in
          List.fold_left (fun propagators (cid, destrs) ->
            let args =
              List.map (fun (destr, srt) ->
                let srt = unfold_adts adts srt in
                mk_var srt (fresh_ident "?v"))
                destrs
            in
            let t = mk_constr adt_srt cid args in
            let gen_terms =
              List.map (fun (destr, srt) -> mk_destr (unfold_adts adts srt) destr t) destrs
            in
            ([Match (t, [])], gen_terms) :: propagators)
            propagators cstrs
      | Loc (ArrayCell srt) -> fun propagators ->
          let f = fresh_ident "?f", field_sort (ArrayCell srt) srt in
          let fld = mk_var (snd f) (fst f) in
          let a = Axioms.loc1 (Array srt) in
          let b = Axioms.loc2 (Array srt) in
          let i = fresh_ident "?i" in
          let idx = mk_var Int i in
          (* a == b, a.cells[i].f -> b.cells[i].f *)
          ([Match (mk_eq_term a b, []);
            Match (mk_read fld [mk_read (mk_array_cells a) [idx]], [])],
           [mk_read fld [mk_read (mk_array_cells b) [idx]]]) ::
          ([Match (mk_eq_term a b, []);
            (* a == b, b.cells[i].f -> a.cells[i].f *)
            Match (mk_read fld [mk_read (mk_array_cells b) [idx]], [])],
           [mk_read fld [mk_read (mk_array_cells a) [idx]]]) :: propagators
      | Loc (Array srt) -> fun propagators ->
          let f = fresh_ident "?f", Map ([Loc (Array srt); Int], srt) in
          let fld = mk_var (snd f) (fst f) in
          let a = Axioms.loc1 (Array srt) in
          let b = Axioms.loc2 (Array srt) in
          let i = fresh_ident "?i" in
          let idx = mk_var Int i in
          (* a == b, a.f[i] -> b.f[i] *)
          ([Match (mk_eq_term a b, []);
            Match (mk_read fld [a; idx], [])],
           [mk_read fld [b; idx]]) ::
          (* a == b, b.cells[i].f -> a.cells[i].f *)
          ([Match (mk_eq_term a b, []);
            Match (mk_read fld [mk_read (mk_array_cells b) [idx]], [])],
           [mk_read fld [mk_read (mk_array_cells a) [idx]]]) :: propagators
      | Map (dsrts, srt) as mapsrt -> fun propagators ->
          let f = fresh_ident "?f", mapsrt in
          let fvar = mk_var (snd f) (fst f) in
          let g = fresh_ident "?g", mapsrt in
          let gvar = mk_var (snd g) (fst g) in
          let d = fresh_ident "?d" in
          let dvar = mk_var srt d in
          let xvars = List.map (fun srt -> mk_var srt (fresh_ident "?i")) dsrts in
          let yvars = List.map (fun srt -> mk_var srt (fresh_ident "?j")) dsrts in
          let propagators =
            match srt with
            | Adt (id, adts) -> 
                let cstrs = List.assoc id adts in
                let destrs = flat_map (fun (_, destrs) -> destrs) cstrs in
                let propagators =
                  List.fold_left
                    (fun propagators -> function
                      | (destr, (Map ([dsrt2], _) as srt)) ->
                          let srt = unfold_adts adts srt in
                          let zvar = mk_var (unfold_adts adts dsrt2) (fresh_ident "?z") in
                          (* f[x := d], f[y].destr[z] -> f[x := d][y].destr[z] *)
                          ([Match (mk_write fvar xvars dvar, []);
                            Match (mk_read (mk_destr srt destr (mk_read fvar yvars)) [zvar], [])],
                           [mk_read (mk_destr srt destr (mk_read (mk_write fvar xvars dvar) yvars)) [zvar]]) ::
                          (* f[x := d].destr[z] -> f[y].destr[z] *)
                          ([Match (mk_read (mk_destr srt destr (mk_read (mk_write fvar xvars dvar) yvars)) [zvar], [])],
                           [mk_read (mk_destr srt destr (mk_read fvar yvars)) [zvar]])
                          :: propagators
                      | _ -> propagators
                    )
                    propagators destrs
                in
                propagators
            | Map (dsrts2, Adt (id, adts)) ->
                let cstrs = List.assoc id adts in
                let destrs = flat_map (fun (_, destrs) -> destrs) cstrs in
                let uvars = List.map (fun srt -> mk_var srt (fresh_ident "?u")) dsrts2 in
                let propagators =
                  List.fold_left
                    (fun propagators -> function
                      | (destr, (Map ([dsrt2], _) as srt)) ->
                          let srt = unfold_adts adts srt in
                          let zvar = mk_var (unfold_adts adts dsrt2) (fresh_ident "?z") in
                          (* f[x := d], f[y][u].destr[z] -> f[x := d][y][u].destr[z] *)
                          ([Match (mk_write fvar xvars dvar, []);
                            Match (mk_read (mk_destr srt destr (mk_read (mk_read fvar yvars) uvars)) [zvar], [])],
                           [mk_read (mk_destr srt destr (mk_read (mk_read (mk_write fvar xvars dvar) yvars) uvars)) [zvar]]) ::
                          (* f[x := d][u].destr[z], f[y] -> f[y][u].destr[z] *)
                          ([Match (mk_read fvar yvars, []);
                            Match (mk_read (mk_destr srt destr (mk_read (mk_read (mk_write fvar xvars dvar) yvars) uvars)) [zvar], [])],
                           [mk_read (mk_destr srt destr (mk_read (mk_read fvar yvars) uvars)) [zvar]])
                          :: propagators
                      | _ -> propagators
                    )
                    propagators destrs
                in
                propagators
            | Map (dsrts2, Map(dsrts3, rsrt)) ->
                let uvars = List.map (fun srt -> mk_var srt (fresh_ident "?u")) dsrts2 in
                let zvars = List.map (fun srt -> mk_var srt (fresh_ident "?z")) dsrts3 in
                (* f[x := d], f[y][u] -> f[x := d][y][u] *)
                ([Match (mk_write fvar xvars dvar, []);
                  Match (mk_read (mk_read (mk_read fvar yvars) uvars) zvars, [])],
                 [mk_read (mk_read (mk_read (mk_write fvar xvars dvar) yvars) uvars) zvars]) ::
                (* f[x := d][u].destr[z], f[y] -> f[y][u].destr[z] *)
                ([Match (mk_read fvar yvars, []);
                  Match (mk_read (mk_read (mk_read (mk_write fvar xvars dvar) yvars) uvars) zvars, [])],
                 [mk_read (mk_read (mk_read fvar yvars) uvars) zvars]) :: propagators
            | Map (dsrts2, rsrt) ->
                let uvars = List.map (fun srt -> mk_var srt (fresh_ident "?u")) dsrts2 in
                (* f[x := d], f[y][u] -> f[x := d][y][u] *)
                ([Match (mk_write fvar xvars dvar, []);
                  Match (mk_read (mk_read fvar yvars) uvars, [])],
                 [mk_read (mk_read (mk_write fvar xvars dvar) yvars) uvars]) ::
                (* f[x := d][u].destr[z], f[y] -> f[y][u].destr[z] *)
                ([Match (mk_read fvar yvars, []);
                  Match (mk_read (mk_read (mk_write fvar xvars dvar) yvars) uvars, [])],
                 [mk_read (mk_read fvar yvars) uvars]) :: propagators
            | _ -> propagators
          in
          let ssrt_opt = match dsrts with
          | Loc ssrt :: _ -> Some ssrt
          | _ -> None
          in
          let match_ivar1 =
            ssrt_opt |>
            Opt.map (fun _ -> Match (List.hd xvars, [FilterNotNull])) |>
            Opt.to_list
          in
          let gen_frame wrap =
            ssrt_opt |>
            Opt.map (fun ssrt ->
              let set1 = Axioms.set1 ssrt in
              let set2 = Axioms.set2 ssrt in
              [(* Frame (x, a, f, g), y.g -> y.f *)
               ([Match (mk_frame_term set1 set2 fvar gvar, []);
                 Match (wrap (mk_read gvar (xvars)), [])] @
                match_ivar1,
               [wrap (mk_read fvar (xvars))]);
               (* Frame (x, a, f, g), y.f -> y.g *)
               ([Match (mk_frame_term set1 set2 fvar gvar, []);
                 Match (wrap (mk_read fvar (xvars)), [])],
                [wrap (mk_read gvar (xvars))])
              ]) |>
            Opt.get_or_else []
          in
          let mk_generators wrap =
            ([Match (mk_eq_term fvar gvar, []);
              Match (wrap (mk_read fvar (xvars)), []);
            ],
             [wrap (mk_read gvar (xvars))]) ::
            (* f == g, x.f -> x.g *)
            ([Match (mk_eq_term fvar gvar, []);
              Match (wrap (mk_read fvar (xvars)), [])
            ],
             [wrap (mk_read gvar (xvars))]) ::
            (* f == g, x.g -> x.f *)
            ([Match (mk_eq_term fvar gvar, []);
              Match (wrap (mk_read gvar (xvars)), [])] @ match_ivar1,
             [wrap (mk_read fvar (xvars))]) :: 
            (* f [x := d], y.(f [x := d]) -> y.f *)
            ([Match (mk_write fvar xvars dvar, []);
              Match (wrap (mk_read (mk_write fvar xvars dvar) yvars), []);
              (*Match (loc1, [FilterNotNull]);*)
              (*Match (loc2, [FilterNotNull])*)],
             [wrap (mk_read fvar yvars)]) ::
            (* f [x := d], y.f -> y.(f [x := d]) *)
            ([Match (mk_write fvar xvars dvar, []);
              Match (wrap (mk_read fvar (yvars)), []);
              (*Match (loc1, [FilterNotNull]);*)
            (*Match (loc2, [FilterNotNull])*)],
             [wrap (mk_read (mk_write fvar (xvars) dvar) (yvars))]) ::
            gen_frame wrap
          in
          mk_generators (fun t -> t) (*@ mk_generators (fun t -> mk_known t)*) @ propagators
      | _ -> fun propagators -> propagators
  in
  SortSet.fold add_propagators field_sorts []
    
let add_read_write_axioms fs =
  let gts = ground_terms ~include_atoms:true (mk_and fs) in
  let has_loc_field_sort = function
    | App (_, _, Map([Loc id1], Loc id2)) -> (*id1 = id2*) true
    | _ -> false
  in
  let basic_pt_flds = TermSet.filter (has_loc_field_sort &&& is_free_const) gts in
  let basic_structs = struct_sorts_of_fields basic_pt_flds in
  (* instantiate null axioms *)
  let axioms = SortSet.fold (fun srt axioms -> Axioms.null_axioms srt @ axioms) basic_structs [] in
  let null_ax, generators = open_axioms ~force:true isFld axioms in
  let generators = match generators with
  | [[Match (v, _)], t] -> [[Match (v, [FilterGeneric (fun sm t -> TermSet.mem (subst_term sm v) basic_pt_flds)])], t]
  | gs -> gs
  in
  let ccgraph = CongruenceClosure.congruence_classes gts fs in
  let _ =
    let tgcode = EMatching.add_term_generators_to_ematch_code EMatching.empty generators in
    EMatching.generate_terms_from_code tgcode ccgraph
  in
  (* CAUTION: not forcing the instantiation here would yield an inconsistency with the read/write axioms *)
  let null_ax1 = EMatching.instantiate_axioms ~force:true null_ax ccgraph in
  let fs1 = null_ax1 @ fs in
  let gts = TermSet.union (ground_terms ~include_atoms:true (mk_and null_ax1)) (CongruenceClosure.get_terms ccgraph) in
  (* propagate read terms *)
  (* generate instances of all read over write axioms *)
  let read_write_ax = 
    let generators_and_axioms =
      TermSet.fold (fun t acc ->
        match t with
        | App (Write, fld :: _, _) ->
            Axioms.read_write_axioms fld @ acc
        | _ -> acc) gts []
    in
    generators_and_axioms 
  in
  let read_propagators = 
    List.map (fun (ms, t) -> TermGenerator (ms, t)) (get_read_propagators gts)
  in
  let fs1 =
    match fs1 with
    | f :: fs1 ->
        annotate f read_propagators :: fs1
    | [] -> []
  in
  rev_concat [read_write_ax; fs1]


(** Adds instantiated theory axioms for graph reachability to formula f.
 ** Assumes that f is typed. *)
let add_reach_axioms fs =
  let struct_sorts =
    SortSet.fold
      (fun srt struct_sorts -> match srt with
      | Map([Loc srt1], Loc srt2) when srt1 = srt2 ->
          SortSet.add srt1 struct_sorts
      | _ -> struct_sorts)
      (sorts (mk_and fs)) SortSet.empty
  in  
  let classes =
    CongruenceClosure.congruence_classes TermSet.empty fs |>
    CongruenceClosure.get_classes
  in
  let axioms =
    SortSet.fold
      (fun srt axioms -> Axioms.reach_axioms classes srt @ Axioms.reach_write_axioms srt @ axioms)
      struct_sorts []
  in
  rev_concat [axioms; fs]

let add_array_axioms fs =
  let srts = array_sorts fs in
  let axioms = SortSet.fold (fun srt axioms -> Axioms.array_axioms srt @ axioms) srts [] in
  axioms @ fs
           
(** Encode label annotations as propositional guards *)
let encode_labels fs =
  let mk_label annots f = 
    let lbls = 
      Util.partial_map 
        (function 
          | Label (pol, t) ->
              Some (if pol then Atom (t, []) else mk_not (Atom (t, [])))
          | _ -> None)
        annots
    in
    mk_and (f :: lbls)
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
       
(** Reduces the given formula to the target theory fragment, as specified b the configuration. *)
let reduce f =
  (* split f into conjuncts and eliminate all existential quantifiers *)
  let f1 = nnf f in
  let fs = elim_exists [f1] in
  let fs = split_ands fs in
  (* *)
  (* no reduction step should introduce implicit or explicit existential quantifiers after this point *)
  (* some formula rewriting that helps the SMT solver *)
  let fs = massage_field_reads fs in
  let fs = simplify_sets fs in
  let fs = add_ep_axioms fs in
  let fs = add_frame_axioms fs in
  let fs = factorize_axioms (split_ands fs) in
  let fs = add_set_axioms fs in
  let fs = add_read_write_axioms fs in
  let fs = add_reach_axioms fs in
  let fs = add_array_axioms fs in
  let fs = if !Config.named_assertions then fs else List.map strip_names fs in
  let fs = fs |> split_ands in
  let _ =
    if Debug.is_debug 1 then begin
      print_endline "VC before instantiation:";
      print_form stdout (mk_and fs);
      print_newline ()
    end
  in
  let fs = encode_labels fs in
  fs
