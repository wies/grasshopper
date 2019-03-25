(** {5 Axiomatization of GRASS theory } *)

open Grass
open GrassUtil
open Config
open Util

  
(** {6 Variable and short-hand declarations} *)
        
let l1 = mk_loc_var "?x"
let l2 = mk_loc_var "?y"
let l3 = mk_loc_var "?z"
let l4 = mk_loc_var "?u"
let l5 = mk_loc_var "?v"
let f1 = mk_loc_field_var "?f"
let f2 = mk_loc_field_var "?g"
let f3 = mk_loc_field_var "?h"
let s1 = mk_loc_set_var "?X"
let s2 = mk_loc_set_var "?Y"
let s3 = mk_loc_set_var "?Z"
let is1 = fresh_ident "?N", Set Int 
let i1 = fresh_ident "?i", Int
let i2 = fresh_ident "?j", Int
let d = fresh_ident "?d"
let e = fresh_ident "?e"
let arrs = fresh_ident "?array_state"
let witness = fresh_ident "witness"
    
let loc1 struct_srt = mk_var (snd (l1 struct_srt)) (fst (l1 struct_srt))
let loc2 struct_srt = mk_var (snd (l2 struct_srt)) (fst (l2 struct_srt))
let loc3 struct_srt = mk_var (snd (l3 struct_srt)) (fst (l3 struct_srt))
let loc4 struct_srt = mk_var (snd (l4 struct_srt)) (fst (l4 struct_srt))
let loc5 struct_srt = mk_var (snd (l5 struct_srt)) (fst (l5 struct_srt))
let fld1 struct_srt = mk_var (snd (f1 struct_srt)) (fst (f1 struct_srt))
let fld2 struct_srt = mk_var (snd (f2 struct_srt)) (fst (f2 struct_srt))
let fld3 struct_srt = mk_var (snd (f3 struct_srt)) (fst (f3 struct_srt))
let dfld1 struct_srt ind_srts res_srt = mk_var (Map (Loc struct_srt :: ind_srts, res_srt)) d
let dfld2 struct_srt ind_srts res_srt = mk_var (Map (Loc struct_srt :: ind_srts, res_srt)) e 
let set1 struct_srt = mk_var (snd (s1 struct_srt)) (fst (s1 struct_srt))
let set2 struct_srt = mk_var (snd (s2 struct_srt)) (fst (s2 struct_srt))
let set3 struct_srt = mk_var (snd (s3 struct_srt)) (fst (s3 struct_srt))
let intset1 = mk_var (snd is1) (fst is1)
let int1 = mk_var (snd i1) (fst i1)
let int2 = mk_var (snd i2) (fst i2)
let arrst1 srt = mk_var (Map ([Loc (Array srt); Int], srt)) arrs
    
let reachwo_Fld f u v w = 
  mk_or [mk_btwn f u v w; mk_and [mk_reach f u v; mk_not (mk_reach f u w)]]
  
let btwn struct_srt = mk_btwn (fld1 struct_srt)
let reach struct_srt = mk_reach (fld1 struct_srt)

(** {6 Utility functions} *)

let mk_axiom ?(gen=[]) name f =
  let bvars = sorted_free_vars f in
  let annots = 
    Name (name, 0) :: 
    List.map (fun (m, g) -> TermGenerator (m, g)) gen 
  in
  mk_forall ~ann:annots (IdSrtSet.elements bvars) f 

let mk_axiom2 f =
  let fvars = sorted_free_vars f in
  let bvars = IdSrtSet.elements fvars in
  mk_forall bvars f 

let extract_axioms fs =
  List.partition (fun f -> IdSet.empty <> fv f) fs

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
        let generators2, a1 = extract_generators generators1 a in
        Binder (b, [], f1, a1), generators2
    | Binder (b, vs, f, a) -> 
        (* extract term generators *)
        let generators1, a1 = extract_generators generators a in
        let vs1 = List.filter (~~ (open_cond (annotate f a1))) vs in
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
let isFld f = function (_, Map ([Loc _], _)) -> true | _ -> false

(** Open condition that checks whether the given sorted variable appears below a function symbol. *) 
let isFunVar f =
  let fvars = vars_in_fun_terms f in
  fun v ->
    IdSrtSet.mem v fvars

    
(** {6 Axioms} *)

(** Array read over write axioms *)
let read_write_axioms fld1 =
  let ind_srts, res_srt = 
    match sort_of fld1 with
    | Map (ind_srts, srt) -> (ind_srts, srt)
    | _ -> failwith "expected map in read_write_axioms"
  in
  let srt_string = string_of_sort res_srt in
  let d = fresh_ident "?d" in
  let dvar = mk_var res_srt d in
  (*let g = fresh_ident "?g" in
    let g1 = g, Fld res_srt in*)
  let mk_inds () = List.map (fun srt -> mk_var srt (fresh_ident "?i")) ind_srts in
  let loc1 = mk_inds () in
  let loc2 = mk_inds () in
  let loc3 = mk_inds () in
  let new_fld1 = mk_write fld1 loc1 dvar in
  let f x = mk_read fld1 x in
  let g x = mk_read new_fld1 x in
  let f_upd1 =
    if not !Config.instantiate || !Config.smtpatterns
    then mk_or (mk_and (List.map2 mk_eq loc2 loc1) :: List.map2 mk_neq loc2 loc3 @ [mk_eq (f loc2) (g loc3)])
    else mk_or (mk_and (List.map2 mk_eq loc2 loc1) :: [mk_eq (f loc2) (g loc2)])
  in
  let f_upd2 = 
    if not !Config.instantiate || !Config.smtpatterns
    then mk_or (List.map2 mk_neq loc1 loc2 @ [mk_eq (g loc2) dvar])
    else mk_or [mk_eq (g loc1) dvar]
  in
  let generator2 = 
    [Match (new_fld1, [FilterNotNull])],
    [g loc1]
  in      
  if not !encode_fields_as_arrays 
  then [mk_axiom ("read_write_" ^ srt_string ^ "_1") f_upd1;
        mk_axiom ~gen:[generator2] ("read_write_" ^ srt_string ^ "_2") f_upd2]
  else []

(** Write axiom for reachability predicates *)
let reach_write_axioms struct_srt =
  let fld1 = fld1 struct_srt in
  let loc1 = loc1 struct_srt in
  let loc2 = loc2 struct_srt in
  let loc3 = loc3 struct_srt in
  let loc4 = loc4 struct_srt in
  let loc5 = loc5 struct_srt in
  let new_fld1 = mk_write fld1 [loc1] loc2 in
  let btwn_write =
    let b = mk_btwn fld1 in
    let reachwo u v w = reachwo_Fld fld1 u v w in
    let new_btwn u v w = 
      mk_or [mk_and [b u v w; reachwo u w loc1];
             mk_and [mk_neq loc1 w; reachwo u loc1 w; b u v loc1; reachwo loc2 w loc1];
             mk_and [mk_neq loc1 w; reachwo u loc1 w; b loc2 v w; reachwo loc2 w loc1]]
    in
    smk_and [smk_or [mk_eq loc1 (mk_null struct_srt); mk_not (mk_btwn new_fld1 loc3 loc4 loc5); new_btwn loc3 loc4 loc5];
	     smk_or [mk_eq loc1 (mk_null struct_srt); mk_btwn new_fld1 loc3 loc4 loc5; mk_not (new_btwn loc3 loc4 loc5)]]
  in
  if !with_reach_axioms 
  then [mk_axiom "btwn_write" (mk_pattern fld1 [] btwn_write)]
  else []

let f x =
  let struct_srt = match sort_of x with
    | Loc s -> s
    | _ -> failwith "expected Loc sort"
  in
  mk_read (fld1 struct_srt) [x]
let g x =
  let struct_srt = match sort_of x with
    | Loc s -> s
    | _ -> failwith "expected Loc sort"
  in
  mk_read (fld2 struct_srt) [x]

(** Axioms for reachability predicates *)
let reach_axioms classes struct_srt = 
  let btwn = btwn struct_srt in
  let reach = reach struct_srt in
  let loc1 = loc1 struct_srt in
  let loc2 = loc2 struct_srt in
  let loc3 = loc3 struct_srt in
  let loc4 = loc4 struct_srt in
  (* btwn axioms *)
  let btwn_refl = btwn loc1 loc1 loc1 in
  let btwn_step = btwn loc1 (f loc1) (f loc1) in
  let btwn_reac = mk_or [mk_not (reach loc1 loc2); 
                         mk_eq loc1 loc2; btwn loc1 (f loc1) loc2] 
  in
  let btwn_cycl = mk_or [mk_neq (f loc1) loc1; mk_not (reach loc1 loc2); 
                         mk_eq loc1 loc2] 
  in
  let btwn_sndw = mk_or [mk_not (btwn loc1 loc2 loc1); mk_eq loc1 loc2] in
  let btwn_ord1 = mk_or [mk_not (reach loc1 loc2); mk_not (reach loc1 loc3); 
                         btwn loc1 loc2 loc3; btwn loc1 loc3 loc2] 
  in
  let btwn_ord2 = mk_or [mk_not (btwn loc1 loc2 loc3); 
                         mk_and [reach loc1 loc2; reach loc2 loc3]] 
  in
  let btwn_trn1 = mk_or [mk_not (reach loc1 loc2); mk_not (reach loc2 loc3); 
                         reach loc1 loc3] 
  in
  let btwn_trn2 = mk_or [mk_not (btwn loc1 loc2 loc3); mk_not (btwn loc2 loc4 loc3);
                         mk_and [btwn loc1 loc2 loc4; btwn loc1 loc4 loc3]]
  in
  let btwn_trn3 = mk_or [mk_not (btwn loc1 loc2 loc3); mk_not (btwn loc1 loc4 loc2);
                         mk_and [btwn loc1 loc4 loc3; btwn loc4 loc2 loc3]]
  in
  let btwn_trn4 = mk_or [mk_not (btwn loc1 loc2 loc3);
                         mk_and [btwn loc1 loc2 loc2; btwn loc1 loc3 loc3;
                                 btwn loc1 loc1 loc2; btwn loc1 loc1 loc3;
                                 btwn loc2 loc3 loc3; btwn loc2 loc2 loc3]]
  in
  let btwn_sndw2 = mk_or [mk_not (btwn loc1 loc2 loc3); mk_not (btwn loc2 loc3 loc1);
                          btwn loc3 loc1 loc2]
  in
  (**)
  let non_updated_field sm t =
    let fld = subst_term sm (fld1 struct_srt) in
    let cl =
      try CongruenceClosure.class_of fld classes
      with Not_found -> [fld]
    in
    List.for_all 
      (function 
	| (App (Write, _, _)) -> false 
	| _ -> true)
      cl
  in
  let mk_axiom ?(gen=[]) name f =
    mk_axiom ~gen name (mk_pattern (fld1 struct_srt) [FilterGeneric non_updated_field] f)
  in
  let gen =
    let fld1 = fld1 struct_srt in
    let fld2 = fld2 struct_srt in
    let set1 = set1 struct_srt in
    let set2 = set2 struct_srt in
    (* Btwn(f, _, _, _) -> known(f) *)
    ([Match (mk_btwn_term fld1 loc1 loc2 loc3, [])], [mk_known fld1]) ::
    (* f = g, known(f) -> known(g) *)
      ([Match (mk_eq_term fld1 fld2, []);
        Match (mk_known fld1, [])],
       [mk_known fld2]) ::
    (* f = g, known(g) -> known(f) *)
    ([Match (mk_eq_term fld1 fld2, []);
      Match (mk_known fld2, [])],
     [mk_known fld1]) :: 
    (* f [x := d], known(f [x := d]) -> known(f) *)
    ([Match (mk_write fld1 [loc1] loc2, []);
      Match (mk_known (mk_write fld1 [loc1] loc2), [])],
     [mk_known fld1]) ::
    (* f [x := d], known(f) -> known(f [x := d]) *)
    ([Match (mk_write fld1 [loc1] loc2, []);
      Match (mk_known fld1, [])],
     [mk_known (mk_write fld1 [loc1] loc2)]) ::
    (* Frame (x, a, f, g), known(g) -> known(f) *)
    ([Match (mk_frame_term set1 set2 fld1 fld2, []);
      Match (mk_known fld2, [])],
     [mk_known fld1]) ::
    (* Frame (x, a, f, g), known(f) -> known(g) *)
    [([Match (mk_frame_term set1 set2 fld1 fld2, []);
      Match (mk_known fld1, [])],
     [mk_known fld2])]
  in
  if !with_reach_axioms then
    [mk_axiom ~gen:gen "btwn_refl" btwn_refl; 
     mk_axiom "btwn_step" btwn_step; 
     mk_axiom "btwn_cycl" btwn_cycl; 
     mk_axiom "btwn_reach" btwn_reac;
     mk_axiom "btwn_sndw" btwn_sndw; 
     mk_axiom "btwn_ord1" btwn_ord1;
     mk_axiom "btwn_ord2" btwn_ord2;
     mk_axiom "btwn_trn1" btwn_trn1;] @
    if not !Config.with_opt_reach_axioms then
      [mk_axiom "btwn_trn2" btwn_trn2;
       mk_axiom "btwn_trn3" btwn_trn3]
    else
      [mk_axiom "btwn_trn4" btwn_trn4;
       mk_axiom "btwn_snd2" btwn_sndw2]
  else []

(** Axioms for null *)
let null_axioms struct_srt1 =
  let n = mk_null struct_srt1 in
  let nll = mk_eq (f n) n in
  let generator =
    [Match (fld1 struct_srt1, [])], 
    [f n]
  in
  [mk_axiom ~gen:[generator] "read_null" nll]


(** Frame axioms *)
let frame_axioms =
  let sk_frame1 = fresh_ident "closed_frame" in
  let sk_frame2 = fresh_ident "closed_frame" in
  fun struct_srt ind_srts res_srt ->
  let a = set1 struct_srt in
  let x = set2 struct_srt in
  (*let frame_set = mk_diff a x in*)
  let mk_axiom fld1 fld2 ?(gen=[]) name f =
    let frame = mk_frame_term x a fld1 fld2 in
    mk_axiom ~gen name
      (mk_pattern frame [] (mk_implies (mk_frame x a fld1 fld2) f))
  in
  let loc1 = loc1 struct_srt in
  let inds = List.map (fun srt -> mk_var srt (fresh_ident "?i")) ind_srts in
  let read_frame fld1 fld2 =
    let frame = mk_frame_term x a fld1 fld2 in
    let gen = [([Match (frame, [])], [mk_known frame])] in
    mk_axiom fld1 fld2 ~gen:gen "read_frame"
      (mk_sequent
         [smk_elem loc1 a]
         [smk_elem loc1 x;
          mk_eq (mk_read fld1 (loc1 :: inds)) (mk_read fld2 (loc1 :: inds))]
      )
  in
  let reach_frame () =
    let loc2 = loc2 struct_srt in
    let loc3 = loc3 struct_srt in
    let fld1 = fld1 struct_srt in
    let fld2 = fld2 struct_srt in
    let axioms =
      let ep v = mk_ep fld1 x v in
      let reachwo_f1 = reachwo_Fld fld1 in
      let reach_f1 x y z = mk_btwn fld1 x z y in
      let reach_f2 x y z = mk_btwn fld2 x z y in
      let frame = mk_frame_term x a fld1 fld2 in
      let sk1 = mk_free_fun (Loc struct_srt) sk_frame1 [a; fld1] in
      let sk2 = mk_free_fun (Loc struct_srt) sk_frame2 [a; fld1] in
      let gen = [([Match (frame, []); Match (mk_known fld1, [])], [sk1; sk2])] in
      [read_frame fld1 fld2;
       mk_axiom fld1 fld2 "reach_frame1"
         (mk_pattern fld1 []
            (mk_sequent
               [reachwo_f1 loc1 loc3 (ep loc1)]
               [(mk_iff 
                   (reach_f1 loc1 loc2 loc3)
                   (reach_f2 loc1 loc2 loc3))]));
       mk_axiom fld1 fld2 "reach_frame2"
         (mk_pattern fld1 []
            (mk_implies
               (mk_and [mk_not (smk_elem loc1 x); mk_eq loc1 (ep loc1)])
               (mk_iff (reach_f1 loc1 loc2 loc3) (reach_f2 loc1 loc2 loc3))))] @
       if not !Config.with_ep then
         [mk_axiom fld1 fld2  ~gen:gen "reach_frame"
            (mk_pattern fld1 []
               (mk_or [mk_and [reach_f1 sk1 sk2 sk2; mk_not (mk_elem sk1 x); mk_elem sk2 x]; mk_not (mk_elem loc1 a); mk_elem loc1 x;
                       mk_iff (reach_f1 loc1 loc2 loc3) (reach_f2 loc1 loc2 loc3)]))]
       else []
    in
    axioms
  in
  let data_frame () =
    let fld1 = dfld1 struct_srt ind_srts res_srt in
    let fld2 = dfld2 struct_srt ind_srts res_srt in
    [read_frame fld1 fld2]
  in
  if res_srt = Loc struct_srt
  then reach_frame ()
  else data_frame ()
    
  
(** Entry point axioms *)
let ep_axioms struct_srt =
  let reach = reach struct_srt in
  let btwn = btwn struct_srt in
  let fld1 = fld1 struct_srt in
  let fld2 = fld2 struct_srt in
  let fld3 = fld3 struct_srt in
  let set1 = set1 struct_srt in
  let set2 = set2 struct_srt in
  let set3 = set3 struct_srt in
  let loc1 = loc1 struct_srt in
  let loc2 = loc2 struct_srt in
  let loc3 = loc3 struct_srt in
  let loc4 = loc4 struct_srt in
  let f1 = f1 struct_srt in
  let f3 = f3 struct_srt in
  let ep = mk_ep fld1 set1 loc1 in
  let in_set1 v = mk_elem v set1 in
  let ep1 = reach loc1 ep in
  let ep2 = mk_or [mk_not (reach loc1 loc2); mk_not (in_set1 loc2); mk_and [in_set1 ep; (*btwn loc1 ep loc2*)]] in
  let ep3 = mk_or [in_set1 ep; mk_eq loc1 ep] in
  let ep4 = 
    mk_implies (mk_and [reach loc1 loc2; in_set1 loc2]) (btwn loc1 ep loc2)
  in
  let ep5 = mk_eq ep (mk_ep fld1 set1 ep) in
  let ep_generator = 
    let field_filter f1 f2 sm _ =
      try
        match IdMap.find f1 sm, IdMap.find f2 sm with
        | App (FreeSym (name1, _), [], _), App (FreeSym (name2, _), [], _) ->
            name1 = name2
        | _ -> false
      with Not_found -> false
    in
    let filter =
      (* do not generate ep terms for Frames that come from field writes *)
      FilterGeneric (fun sm t ->
        match IdMap.find (fst (s1 struct_srt)) sm with
        | App (SetEnum, _, _) -> false 
        | _ -> true)
    in
    [([Match (mk_known fld1, []);
       Match (mk_frame_term set1 set2 fld1 fld2, [filter]);
       Match (mk_btwn_term fld3 loc1 loc3 loc4, [FilterGeneric (field_filter (fst f1) (fst f3))]);
       Match (loc1, [FilterNotNull; FilterSymbolNotOccurs EntPnt])], 
      [mk_ep fld1 set1 loc1]);
     ((if !Config.full_ep then
       (*let ep_filter sm t =
         let rec count n = function
           | App (sym, ts, _) ->
               let n1 = if sym = EntPnt then n + 1 else n in
               List.fold_left count n1 ts
           | _ -> n
         in
         count 0 t < 2
       in*)
       [Match (mk_known fld1, []);
        Match (mk_frame_term set1 set2 fld1 fld2, [filter]);
        Match (loc1, [FilterNotNull; FilterSymbolNotOccurs EntPnt])]
      else
       [Match (mk_known fld1, []);
        Match (mk_frame_term set1 set2 fld1 fld2, [filter]);
        (*Match (mk_btwn_term fld3 loc2 loc3 loc4, [FilterGeneric (field_filter (fst f1) (fst f3))]);*)
        Match (mk_known (mk_elem_term loc1 set3), []);
        Match (loc1, [FilterNotNull; FilterSymbolNotOccurs EntPnt])]), 
      [mk_ep fld1 set1 loc1])
   ]
  in
  if !Config.with_ep then
    [mk_axiom "entry-point1" ep1; 
     mk_axiom ~gen:ep_generator "entry-point2" ep2; 
     mk_axiom "entry-point3" ep3; 
     mk_axiom "entry-point4" ep4;
     mk_axiom "entry-point5" ep5]
  else []

(** Array axioms *)
let array_axioms elem_srt =
  let a = loc1 (Array elem_srt) in
  let c = loc2 (ArrayCell elem_srt) in
  let i = int1 in
  let arrstate = arrst1 elem_srt in
  let array_length =
    mk_or [mk_eq a (mk_null (Array elem_srt)); mk_leq (mk_int 0) (mk_length a)]
  in
  let array_map_simple1 =
    mk_or [mk_lt i (mk_int 0);
           mk_geq i (mk_length a);
           mk_eq (mk_read arrstate [a; i]) (mk_read (App (ArrayMap, [arrstate; a], Map ([Int], elem_srt))) [i])] 
  in
  let array_map_simple2 =
    mk_or [mk_and [mk_geq i (mk_int 0); mk_lt i (mk_length a)];
           mk_eq (mk_read (App (ArrayMap, [arrstate; a], Map ([Int], elem_srt))) [i]) (mk_free_const (elem_srt) witness)] 
  in
  let array_cells1 =
    mk_eq (mk_array_of_cell (mk_read (mk_array_cells a) [i])) a 
  in
  let array_cells2 =
    mk_eq (mk_index_of_cell (mk_read (mk_array_cells a) [i])) i
  in
  let array_cells3 =
    mk_eq (mk_read (mk_array_cells (mk_array_of_cell c)) [mk_index_of_cell c]) c
  in
  (*
  let array_cells1 = 
    mk_sequent [mk_eq (mk_read (mk_array_cells a) i) c] [mk_and [mk_eq (mk_array_of_cell c) a; mk_eq (mk_index_of_cell c) i]]
  in
  let array_cells2 =
    mk_sequent [mk_eq (mk_array_of_cell c) a; mk_eq (mk_index_of_cell c) i] [mk_eq (mk_read (mk_array_cells a) i) c]
  in
   *)
  let array_map_gen =
    [([Match (mk_read arrstate [a; i], [])], [mk_read (App (ArrayMap, [arrstate; a], Map ([Int], elem_srt))) [i]]);
     ([Match (mk_read (App (ArrayMap, [arrstate; a], Map ([Int], elem_srt))) [i], [])], [mk_read arrstate [a; i]])]
  in
  let array_cell_gen =
    ([Match (c, [FilterSymbolNotOccurs ArrayOfCell;
                 FilterSymbolNotOccurs IndexOfCell;
                 FilterSymbolNotOccurs ArrayCells;
                 FilterNotNull])], 
      [mk_read (mk_array_cells (mk_array_of_cell c)) [mk_index_of_cell c]])
  in
  let index_of_cell_gen =
    ([Match (c, [FilterSymbolNotOccurs IndexOfCell; FilterNotNull])], 
     [mk_index_of_cell c])
  in
  let array_of_cell_gen =
    ([Match (c, [FilterSymbolNotOccurs ArrayOfCell; FilterNotNull])], 
     [mk_array_of_cell c])
  in
  let array_cells_gen =
    ([Match (a, [FilterSymbolNotOccurs ArrayCells; FilterNotNull])], 
     [mk_array_cells a])
  in
  let array_length_gen =
    ([Match (a, [])], [mk_length a])
  in
  if !Config.simple_arrays then
    [mk_axiom ~gen:[array_length_gen] "array-length" array_length] @
    if not !Config.symbexec then
      [mk_axiom ~gen:array_map_gen "array-map1" array_map_simple1;
       mk_axiom "array-map2" array_map_simple2]
    else []
  else 
    [mk_axiom ~gen:[index_of_cell_gen; array_of_cell_gen; array_cells_gen; array_cell_gen] "array-cells1" array_cells1;
     mk_axiom "array-cells2" array_cells2;
     mk_axiom "array-cells3" array_cells3;
     mk_axiom ~gen:[array_length_gen] "array-length" array_length]
     
(** Set axioms *)
let set_axioms elem_srts =
  let mk_set_axioms t =
    let elt1 = mk_var t (mk_ident "x") in
    let elt2 = mk_var t (mk_ident "y") in
    let set1 = mk_var (Set t) (mk_ident "X") in
    let set2 = mk_var (Set t) (mk_ident "Y") in
    let set3 = mk_var (Set t) (mk_ident "Z") in
    let x = mk_var t (mk_ident "x") in
    let empty = 
      (* don't use the smart constructor smk_elem for set membership here *)
      mk_not (mk_elem elt1 (mk_empty (Set t)))
    in
    let union = 
      mk_iff (mk_elem elt1 (mk_union [set1; set2])) 
        (mk_or [mk_elem elt1 set1; mk_elem elt1 set2])
    in
    let inter =
      mk_iff (mk_elem elt1 (mk_inter [set1; set2])) 
        (mk_and [mk_elem elt1 set1; mk_elem elt1 set2])
    in
    let diff =
      mk_iff (mk_elem elt1 (mk_diff set1 set2)) 
        (mk_and [mk_elem elt1 set1; mk_not (mk_elem elt1 set2)])
    in
    let setenum =
      mk_iff (mk_elem elt1 (mk_setenum [elt2])) 
        (mk_eq elt1 elt2)
    in
    let subset_def =
      mk_sequent [mk_subseteq set1 set2; mk_elem elt1 set1] [mk_elem elt1 set2]
    in
    let subset_def_union =
      nnf (mk_iff (mk_subseteq set1 set2) (mk_eq (mk_union [set1; set2]) set2))
    in
    (* Auxiliary subset axioms *)
    let subset_refl =
      mk_subseteq set1 set1
    in
    let subset_trans =
      mk_sequent [mk_subseteq set1 set2; mk_subseteq set2 set3]
        [mk_subseteq set1 set3]
    in
    let subset_empty =
      mk_subseteq (mk_empty (Set t)) set1
    in
    let subset_union1 =
      mk_sequent [mk_subseteq (mk_union [set1; set2]) set3]
        [mk_and [mk_subseteq set1 set3; mk_subseteq set2 set3]]
    in
    let subset_union21 =
      mk_sequent [mk_subseteq set1 set2]
        [mk_subseteq set1 (mk_union [set2; set3])]
    in
    let subset_union22 =
      mk_sequent [mk_subseteq set1 set2]
        [mk_subseteq set1 (mk_union [set3; set2])]
    in
    let subset_inter1 =
      mk_sequent [mk_subseteq set1 (mk_inter [set2; set3])]
        [mk_and [mk_subseteq set1 set2; mk_subseteq set1 set3]]
    in
    let subset_inter21 =
      mk_sequent [mk_subseteq set1 set2]
        [mk_subseteq (mk_inter [set1; set3]) set2]
    in
    let subset_inter22 =
      mk_sequent [mk_subseteq set1 set2]
        [mk_subseteq (mk_inter [set3; set1]) set2]
    in
    let subset_diff =
      mk_sequent [mk_subseteq set1 set2]
        [mk_subseteq (mk_diff set1 set3) set2]
    in
    let disjoint_def =
      mk_sequent [mk_disjoint set1 set2]
        [mk_not (mk_elem elt1 set1); mk_not (mk_elem elt1 set2)]
    in
    let disjoint_empty =
      mk_disjoint set1 (mk_empty (Set t))
    in
    let disjoint_sym =
      mk_sequent [mk_disjoint set1 set2] [mk_disjoint set2 set1]
    in
    let disjoint_union =
      mk_iff (mk_disjoint (mk_union [set1; set2]) set3)
        (mk_and [mk_disjoint set1 set3; mk_disjoint set2 set3])
    in
    let disjoint_inter1 =
      mk_sequent [mk_disjoint set1 set2]
        [mk_disjoint (mk_inter [set1; set3]) set2]
    in
    let disjoint_inter2 =
      mk_sequent [mk_disjoint set1 set2]
        [mk_disjoint (mk_inter [set3; set1]) set2]
    in
    let disjoint_singleton =
      mk_sequent [mk_not (mk_elem x set1)]
        [mk_disjoint (mk_setenum [x]) set1]
    in
    let disjoint_def_inter =
      nnf (mk_iff (mk_eq (mk_inter [set1; set2]) (mk_empty (Set t)))
             (mk_disjoint set1 set2))
    in
    let disjoint_diff =
      mk_sequent [mk_disjoint set1 set2]
        [mk_disjoint (mk_diff set1 set3) set2]
    in
    let disjoint_subset1 =
      mk_sequent [mk_subseteq set1 set2; mk_disjoint set2 set3]
        [mk_disjoint set1 set3]
    in
    let disjoint_subset2 =
      mk_sequent [mk_subseteq set1 set2] [mk_disjoint set1 (mk_diff set3 set2)]
    in
    let disjoint_subset3 =
      mk_sequent [mk_subseteq set1 set2; mk_disjoint set1 set3]
        [mk_subseteq set1 (mk_diff set2 set3)]
    in
    let ssrt = string_of_sort t in
    if !Config.use_set_theory then []
    else [mk_axiom ("def of emptyset" ^ ssrt) empty;
          mk_axiom ("def of union" ^ ssrt) union;
          mk_axiom ("def of inter" ^ ssrt) inter;
          mk_axiom ("def of setminus" ^ ssrt) diff;
          mk_axiom ("def of setenum" ^ ssrt) setenum;
          mk_axiom ("def of disjoint" ^ ssrt) disjoint_def;
          mk_axiom ("def of disjoint inter" ^ ssrt) disjoint_def_inter;
          mk_axiom ("def of subset" ^ ssrt) subset_def;
          mk_axiom ("def of subset union" ^ ssrt) subset_def_union;
        ] @
      if !Config.abstract_preds then
        [mk_axiom ("def of subseteq" ^ ssrt) subset_def;
         mk_axiom ("subset refl" ^ ssrt) subset_refl;
         mk_axiom ("subset empty" ^ ssrt) subset_empty;
         mk_axiom ("subset trans" ^ ssrt) subset_trans;
         mk_axiom ("subset union1" ^ ssrt) subset_union1;
         mk_axiom ("subset union21" ^ ssrt) subset_union21;
         mk_axiom ("subset union22" ^ ssrt) subset_union22;
         mk_axiom ("subset inter1" ^ ssrt) subset_inter1;
         mk_axiom ("subset inter21" ^ ssrt) subset_inter21;
         mk_axiom ("subset inter22" ^ ssrt) subset_inter22;
         mk_axiom ("subset diff" ^ ssrt) subset_diff;
         mk_axiom ("def of Disjoint" ^ ssrt) disjoint_def;
         mk_axiom ("Disjoint sym" ^ ssrt) disjoint_sym;
         mk_axiom ("Disjoint empty" ^ ssrt) disjoint_empty;
         mk_axiom ("Disjoint union" ^ ssrt) disjoint_union;
         mk_axiom ("Disjoint inter1" ^ ssrt) disjoint_inter1;
         mk_axiom ("Disjoint inter2" ^ ssrt) disjoint_inter2;
         mk_axiom ("Disjoint diff" ^ ssrt) disjoint_diff;
         mk_axiom ("Disjoint subset1" ^ ssrt) disjoint_subset1;
         mk_axiom ("Disjoint subset2" ^ ssrt) disjoint_subset2;
         mk_axiom ("Disjoint subset3" ^ ssrt) disjoint_subset3;
         mk_axiom ("Disjoint singleton" ^ ssrt) disjoint_singleton;
       ] else []
  in
  Util.flat_map mk_set_axioms elem_srts
      

