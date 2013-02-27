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

let loc1 = mk_var ~srt:(snd l1) (fst l1)
let loc2 = mk_var ~srt:(snd l2) (fst l2)
let loc3 = mk_var ~srt:(snd l3) (fst l3)
let loc4 = mk_var ~srt:(snd l4) (fst l4)
let loc5 = mk_var ~srt:(snd l5) (fst l5)
let fld1 = mk_var ~srt:(snd f1) (fst f1)
let fld2 = mk_var ~srt:(snd f2) (fst f2)
let set1 = mk_var ~srt:(snd s1) (fst s1)
let set2 = mk_var ~srt:(snd s2) (fst s2)

let all_vars = [f1; f2; s1; s2; l1; l2; l3; l4; l5]

let mk_axiom name f =
  let fvars = fv f in
  let bvars = List.filter (fun v -> IdSet.mem (fst v) fvars) all_vars in
  mk_forall ~ann:[Comment name] bvars f 

(*
let reach_name = "Reach_"

let reach_id (f, n) = (reach_name ^ f, n)

let reach f x y z = mk_pred (reach_id f) [x; y; z]

let fun_of_reach = 
  let reach_len = String.length reach_name in
  fun (id : ident) -> (String.sub (fst id) reach_len (String.length (fst id) - reach_len), (snd id))


let is_reach = 
  let re = Str.regexp reach_name in
  fun ((name, _) : ident) -> Str.string_match re name 0
*)

let f x = mk_read fld1 x
let g x = mk_read fld2 x
let reachwo = mk_reachwo fld1
let reach = mk_reach fld1

let write_axioms () =
  let new_fld1 = mk_write fld1 loc1 loc2 in
  let f_upd1 = 
    mk_or [mk_neq new_fld1 fld2; mk_eq loc3 loc1; mk_eq (f loc3) (g loc3)]
  in
  let f_upd2 = mk_or [mk_neq new_fld1 fld2; mk_eq (g loc1) loc2] in
  let reachwo_upd =
    let r = reachwo in
    let new_reachwo u v w =
      mk_or [mk_and [r u v w; r u v loc1];
	     mk_and [mk_not (mk_eq loc1 w); r u loc1 w; r loc2 v loc1; r loc2 v w]]
    in
    smk_and [smk_or [mk_not (mk_reachwo new_fld1 loc3 loc4 loc5); new_reachwo loc3 loc4 loc5];
	    smk_or [mk_reachwo new_fld1 loc3 loc4 loc5; mk_not (new_reachwo loc3 loc4 loc5)]]
  in
  (if not !encode_fields_as_arrays then [mk_axiom "read_write1" f_upd1; mk_axiom "read_write2" f_upd2] else []) @ 
  (if !with_reach_axioms then [mk_axiom "reachwo_write" reachwo_upd] else [])

let reachwo_axioms () = 
  (* axioms *)
  let refl = reachwo loc1 loc1 loc2 in
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
		    mk_not (reachwo loc2 loc3 loc3); reachwo loc1 loc2 loc4] in
  (**)
  if !with_reach_axioms then
    [mk_axiom "refl" refl; 
     mk_axiom "step" step; 
     mk_axiom "cycl" cycl; 
     mk_axiom "reach" reac;
     mk_axiom "sndw" sndw; 
     mk_axiom "linear1" lin1;
     mk_axiom "linear2" lin2;
     mk_axiom "trans1" trn1; 
     mk_axiom "trans2" trn2]
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
  let ep4 = mk_implies (mk_and [reach loc1 loc2; in_set1 loc2]) (reachwo loc1 ep loc2) in
    [mk_axiom "entry-point1" ep1; 
     mk_axiom "entry-point2" ep2; 
     mk_axiom "entry-point3" ep3; 
     mk_axiom "entry-point4" ep4]

(* set axioms *)

let set_axioms () =
  let empty = 
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
  [mk_axiom "empty" empty;
   mk_axiom "union" union;
   mk_axiom "inter" inter;
   mk_axiom "diff" diff;
   mk_axiom "enum" setenum]

let extract_axioms fs =
  List.partition (fun f -> IdSet.empty <> fv f) fs

