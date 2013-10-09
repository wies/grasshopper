open Form
open FormUtil
open Config

let l1 = fresh_ident "?x", Loc
let l2 = fresh_ident "?y", Loc
let l3 = fresh_ident "?z", Loc
let l4 = fresh_ident "?u", Loc
let l5 = fresh_ident "?v", Loc
let f1 = fresh_ident "?f", Fld Loc
let f2 = fresh_ident "?g", Fld Loc
let s1 = fresh_ident "?X", Set Loc 
let s2 = fresh_ident "?Y", Set Loc 
let i1 = fresh_ident "?m", Int
let i2 = fresh_ident "?n", Int

let loc1 = mk_var ~srt:(snd l1) (fst l1)
let loc2 = mk_var ~srt:(snd l2) (fst l2)
let loc3 = mk_var ~srt:(snd l3) (fst l3)
let loc4 = mk_var ~srt:(snd l4) (fst l4)
let loc5 = mk_var ~srt:(snd l5) (fst l5)
let fld1 = mk_var ~srt:(snd f1) (fst f1)
let fld2 = mk_var ~srt:(snd f2) (fst f2)
let set1 = mk_var ~srt:(snd s1) (fst s1)
let set2 = mk_var ~srt:(snd s2) (fst s2)
let int1 = mk_var ~srt:(snd i1) (fst i1)
let int2 = mk_var ~srt:(snd i2) (fst i2)

let all_vars = [f1; f2; s1; s2; l1; l2; l3; l4; l5; i1; i2]

let mk_axiom name f =
  let fvars = fv f in
  let bvars = List.filter (fun v -> IdSet.mem (fst v) fvars) all_vars in
  mk_forall ~ann:[Comment name] bvars f 

let mk_axiom2 f =
  let fvars = fv f in
  let bvars = List.filter (fun v -> IdSet.mem (fst v) fvars) all_vars in
  mk_forall bvars f 

let f x = mk_read fld1 x
let g x = mk_read fld2 x

let reachwo_Fld f u v w = 
  mk_or [mk_btwn f u v w; mk_and [mk_reach f u v; mk_not (mk_reach f u w)]]
  
(*let reachwo = mk_reachwo fld1*)
let btwn = mk_btwn fld1
let reach = mk_reach fld1

let read_write_axioms fld1 loc1 loc2 =
  let new_fld1 = mk_write fld1 loc1 loc2 in
  let f x = mk_read fld1 x in
  let g x = mk_read new_fld1 x in
  let f_upd1 = 
    mk_or [mk_eq loc3 loc1; mk_eq (f loc3) (g loc3)]
  in
  let f_upd2 = mk_eq (g loc1) loc2 in
  if not !encode_fields_as_arrays then [mk_axiom "read_write1" f_upd1; mk_axiom "read_write2" f_upd2] else []
  
let reach_write_axioms fld1 loc1 loc2 =
  let new_fld1 = mk_write fld1 loc1 loc2 in
  (* deprecated
  let reachwo_write =
    let r = mk_reachwo fld1 in
    let new_reachwo u v w =
      mk_or [mk_and [r u v w; r u v loc1];
	     mk_and [mk_neq loc1 w; r u loc1 w; r loc2 v loc1; r loc2 v w]]
    in
    smk_and [smk_or [mk_not (mk_reachwo new_fld1 loc3 loc4 loc5); new_reachwo loc3 loc4 loc5];
	     smk_or [mk_reachwo new_fld1 loc3 loc4 loc5; mk_not (new_reachwo loc3 loc4 loc5)]]
  in*)
  let btwn_write =
    let b = mk_btwn fld1 in
    let reachwo u v w = reachwo_Fld fld1 u v w in
    let new_btwn u v w = 
      mk_or [mk_and [b u v w; reachwo u w loc1];
             mk_and [mk_neq loc1 w; reachwo u loc1 w; b u v loc1; reachwo loc2 w loc1];
             mk_and [mk_neq loc1 w; reachwo u loc1 w; b loc2 v w; reachwo loc2 w loc1]]
    in
    smk_and [smk_or [mk_not (mk_btwn new_fld1 loc3 loc4 loc5); new_btwn loc3 loc4 loc5];
	     smk_or [mk_btwn new_fld1 loc3 loc4 loc5; mk_not (new_btwn loc3 loc4 loc5)]]
  in
  if !with_reach_axioms 
  then [mk_axiom "btwn_write" btwn_write]
  else []

let reach_axioms () = 
  (* reachwo axioms (depricated) *)
  (*let refl = reachwo loc1 loc1 loc2 in
  let reac = mk_or [mk_not (reachwo loc1 loc2 loc3); 
		    reachwo loc1 loc2 loc2] in 
  let step = mk_or [reachwo loc1 (f loc1) loc2; mk_eq loc1 loc2] in
  let cycl = mk_or [mk_not (mk_eq (f loc1) loc1); 
		    mk_not (reachwo loc1 loc2 loc2); mk_eq loc1 loc2] in
  let sndw = mk_or [mk_not (reachwo loc1 loc2 loc1); mk_eq loc1 loc2] in
  let lin1 = mk_or [mk_not (reachwo loc1 loc2 loc2); reachwo loc1 loc3 loc2; reachwo loc1 loc2 loc3] in
  let lin2  = mk_or [mk_not (reachwo loc1 loc2 loc3); mk_not (reachwo loc1 loc4 loc5); 
		    mk_and [reachwo loc1 loc4 loc3; reachwo loc4 loc2 loc3]; 
		    mk_and [reachwo loc1 loc2 loc5; reachwo loc2 loc4 loc5]] in
  let trn1 = mk_or [mk_not (reachwo loc1 loc2 loc3); mk_not (reachwo loc2 loc4 loc3); 
		    reachwo loc1 loc4 loc3] in
  let trn2 = mk_or [mk_not (reachwo loc1 loc2 loc3); mk_not (reachwo loc2 loc4 loc3); 
		    mk_not (reachwo loc2 loc3 loc3); reachwo loc1 loc2 loc4] in*)
  (* btwn axioms *)
  let btwn_refl = btwn loc1 loc1 loc1 in
  let btwn_step = btwn loc1 (f loc1) (f loc1) in
  let btwn_reac = mk_or [mk_not (reach loc1 loc2); mk_eq loc1 loc2; btwn loc1 (f loc1) loc2] in
  let btwn_cycl = mk_or [mk_neq (f loc1) loc1; mk_not (reach loc1 loc2); mk_eq loc1 loc2] in
  let btwn_sndw = mk_or [mk_not (btwn loc1 loc2 loc1); mk_eq loc1 loc2] in
  let btwn_ord1 = mk_or [mk_not (reach loc1 loc2); mk_not (reach loc1 loc3); btwn loc1 loc2 loc3; btwn loc1 loc3 loc2] in
  let btwn_ord2 = mk_or [mk_not (btwn loc1 loc2 loc3); mk_and [reach loc1 loc2; reach loc2 loc3]] in
  let btwn_trn1 = mk_or [mk_not (reach loc1 loc2); mk_not (reach loc2 loc3); reach loc1 loc3] in
  let btwn_trn2 = mk_or [mk_not (btwn loc1 loc2 loc3); mk_not (btwn loc2 loc4 loc3);
                         mk_and [btwn loc1 loc2 loc4; btwn loc1 loc4 loc3]] in
  let btwn_trn3 = mk_or [mk_not (btwn loc1 loc2 loc3); mk_not (btwn loc1 loc4 loc2);
                         mk_and [btwn loc1 loc4 loc3; btwn loc4 loc2 loc3]] in
  (**)
  if !with_reach_axioms then
    [mk_axiom "btwn_refl" btwn_refl; 
     mk_axiom "btwn_step" btwn_step; 
     mk_axiom "btwn_cycl" btwn_cycl; 
     mk_axiom "btwn_reach" btwn_reac;
     mk_axiom "btwn_sndw" btwn_sndw; 
     mk_axiom "btwn_ord1" btwn_ord1;
     mk_axiom "btwn_ord2" btwn_ord2;
     mk_axiom "btwn_trn1" btwn_trn1; 
     mk_axiom "btwn_trn2" btwn_trn2;
     mk_axiom "btwn_trn3" btwn_trn3]
  else []

let null_axioms () =
  let nll = mk_eq (f mk_null) mk_null in
  if !Config.with_null_axioms then [mk_axiom "read_null" nll] else []


(* entry point axioms: when entering a part of the heap, used for SL*)
let ep_axioms () =
  let ep = mk_ep fld1 set1 loc1 in
  let in_set1 v = mk_elem v set1 in
  let ep1 = reach loc1 ep in
  let ep2 = mk_or [mk_not (reach loc1 loc2); mk_not (in_set1 loc2); in_set1 ep] in
  let ep3 = mk_or [in_set1 ep; mk_eq loc1 ep] in
  let ep4 = 
    mk_implies (mk_and [reach loc1 loc2; in_set1 loc2]) (btwn loc1 ep loc2)
    (*else mk_implies (mk_and [reach loc1 loc2; in_set1 loc2]) (reachwo loc1 ep loc2) *)
  in
  if !Config.with_ep then
    [mk_axiom "entry-point1" ep1; 
     mk_axiom "entry-point2" ep2; 
     mk_axiom "entry-point3" ep3; 
     mk_axiom "entry-point4" ep4]
  else []

(* set axioms *)

let set_axioms () =
  let empty = 
    (* don't use the smart constructor smk_elem for membership here *)
    mk_not (mk_elem loc1 (mk_empty (Some (Set Loc))))
  in
  let union = 
    mk_iff (mk_elem loc1 (mk_union [set1; set2])) 
      (mk_or [mk_elem loc1 set1; mk_elem loc1 set2])
  in
  let inter =
    mk_iff (mk_elem loc1 (mk_inter [set1; set2])) 
      (mk_and [mk_elem loc1 set1; mk_elem loc1 set2])
  in
  let diff =
    mk_iff (mk_elem loc1 (mk_diff set1 set2)) 
      (mk_and [mk_elem loc1 set1; mk_not (mk_elem loc1 set2)])
  in
  let setenum =
    mk_iff (mk_elem loc1 (mk_setenum [loc2])) 
      (mk_eq loc1 loc2)
  in
  [mk_axiom "def of empty" empty;
   mk_axiom "def of union" union;
   mk_axiom "def of inter" inter;
   mk_axiom "def of diff" diff;
   mk_axiom "def of enum" setenum]

let extract_axioms fs =
  List.partition (fun f -> IdSet.empty <> fv f) fs

