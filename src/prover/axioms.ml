open Form
open Config

let l1 = fresh_ident "x", Loc
let l2 = fresh_ident "y", Loc
let l3 = fresh_ident "z", Loc
let l4 = fresh_ident "u", Loc
let l5 = fresh_ident "v", Loc
let f1 = fresh_ident "f", Loc
let s1 = fresh_ident "X", Set Loc 

let loc1 = mk_var ~srt:(snd l1) (fst l1)
let loc2 = mk_var ~srt:(snd l2) (fst l2)
let loc3 = mk_var ~srt:(snd l3) (fst l3)
let loc4 = mk_var ~srt:(snd l4) (fst l4)
let loc5 = mk_var ~srt:(snd l5) (fst l5)
let fld1 = mk_var ~srt:(snd f1) (fst f1)
let set1 = mk_var ~srt:(snd s1) (fst s1)

let all_vars = [f1; s1; l1; l2; l3; l4; l5]

let alloc_id = (mk_ident "Alloc")

let alloc_set = mk_var ~srt:(Set Loc) alloc_id

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

let f x = mk_sel fld1 x
let reachwo = mk_reachwo fld1
let reach = mk_reach fld1

let update_axioms () =
  let new_fld1 = mk_upd fld1 loc1 loc2 in
  let new_f x = mk_sel new_fld1 x in
  let f_upd1 = 
    mk_or [mk_eq loc3 loc1; mk_eq (f loc3) (new_f loc3)]
  in
  let f_upd2 = mk_eq (new_f loc1) loc2 in
  let reachwo_upd =
    let r = reachwo in
    let new_reachwo u v w =
      mk_or [mk_and [r u v w; r u v loc1];
	     mk_and [mk_not (mk_eq loc1 w); r u loc1 w; r loc2 v loc1; r loc2 v w]]
    in
    mk_and [mk_or [mk_not (mk_reachwo new_fld1 loc3 loc4 loc5); new_reachwo loc3 loc4 loc5];
	    mk_or [mk_reachwo new_fld1 loc3 loc4 loc5; mk_not (new_reachwo loc3 loc4 loc5)]]
  in
  (if not !encode_fields_as_arrays then [mk_axiom "upd1" f_upd1; mk_axiom "upd2" f_upd2] else []) @ 
  (if !with_reach_axioms then [mk_axiom "reachwo_upd" reachwo_upd] else [])

let reachwo_axioms () = 
  (* axioms *)
  let refl = reachwo loc1 loc1 loc2 in
  let reac = mk_or [mk_not (reachwo loc1 loc2 loc3); 
		    reachwo loc1 loc2 loc2] in 
  let step = mk_or [reachwo loc1 (f loc1) loc2; mk_eq loc1 loc2] in
  (* let ufld = mk_or [mk_not (reachwo loc1 loc2 loc3); mk_eq loc1 loc2; reachwo (af loc1) loc2 loc3] in *)
  let cycl = mk_or [mk_not (mk_eq (f loc1) loc1); 
		    mk_not (reachwo loc1 loc2 loc2); mk_eq loc1 loc2] in
  (* let cycl2 = mk_or [mk_not (reachwo loc1 loc2 loc3); mk_not (reachwo loc2 loc1 loc3); mk_not (reachwo loc1 loc3 loc3); mk_eq loc1 loc2; mk_eq loc1 loc3] in *)
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
  if !with_null_axioms then [mk_axiom "null" nll] else []

let alloc_axioms () = 
  let alc = mk_not (mk_elem mk_null alloc_set) in
  if !with_alloc_axioms then [mk_axiom "alloc_init" alc] else []

(* the following two axioms should be redundant 

let alloc_update_axioms id alloc new_alloc =
  let x = mk_const id in
  let in_alloc x = mk_elem x alloc_set in
  let mk_new_alloc x = mk_pred new_alloc [x] in
  [mk_not (mk_alloc x); 
   mk_new_alloc x;
   mk_or [mk_eq x var1; mk_not (mk_alloc var1); mk_new_alloc var1];
   mk_or [mk_eq x var1; mk_not (mk_new_alloc var1); mk_alloc var1]]

let alloc_dispose_axioms id alloc new_alloc =
  alloc_update_axioms id new_alloc alloc
*)

(* entry point axioms: when entering a part of the heap, used for SL*)

let ep_axioms () =
  let ep = mk_ep fld1 set1 loc1 in
  let in_set1 v = mk_elem v set1 in
  let ep1 = reach loc1 ep in
  let ep2 = mk_or [mk_not (reach loc1 loc2); mk_not (in_set1 loc2); in_set1 ep] in
  let ep3 = mk_or [in_set1 ep; mk_eq loc1 ep] in
  let ep4 = mk_implies (mk_and [reach loc1 loc2; in_set1 loc2]) (reachwo loc1 ep loc2) in
    [mk_axiom "entrypoint1" ep1; 
     mk_axiom "entrypoint2" ep2; 
     mk_axiom "entrypoint3" ep3; 
     mk_axiom "entrypoint4" ep4]

(*
let get_eps f =
  IdMap.fold 
    (fun id decl acc ->
      if (not decl.is_pred) && decl.arity = 1 && is_ep id then IdSet.add (fun_of_ep id) acc
      else acc)
    (sign f) IdSet.empty
(*******)


let extract_axioms fs =
  List.partition (fun f -> IdSet.empty <> fv f) fs


let unary_funs f =
  IdMap.fold 
    (fun id decl acc ->
      if (not decl.is_pred) then
        begin
          if decl.arity = 1 && not (is_ep id) then IdSet.add id acc
          else if decl.arity = 2 && is_jp id then IdSet.add (fun_of_jp id) acc
          else acc
        end
      else if decl.is_pred && decl.arity = 3 && is_reach id then IdSet.add (fun_of_reach id) acc
      else acc)
    (sign f) IdSet.empty


let make_axioms fs =
  let unaries = List.map (fun f -> unary_funs (mk_and f)) fs in
  let init_funs = List.map (fun set -> IdSet.filter (fun (_, n) -> n = 0) set) unaries in
  let _, rev_already_declared =
    List.fold_left
      (fun (lhs, acc) uns -> (IdSet.union lhs uns, (IdSet.filter (fun id -> IdSet.mem id lhs) uns) :: acc) )
      (IdSet.empty, [])
      unaries
  in
  let already_declared = List.rev rev_already_declared in
  let all_init = List.map2 IdSet.union init_funs already_declared in
  let axioms =
    List.map2
      (fun unary init ->
        IdSet.fold (fun id acc -> reach_axioms id @ acc) init [] @
        IdSet.fold (fun id acc -> null_axioms id @ fun_axioms id @ acc) unary []
      )
      unaries
      all_init
  in
  (alloc_axioms () @ List.hd axioms) :: (List.tl axioms)

let add_axioms fs =
  let axioms = make_axioms fs in
    List.map2 (@) axioms fs
*)

let skolemize fresh_const axiom =
  let vars = fv axiom in
  let subst_map = IdSet.fold (fun v acc -> IdMap.add v (fresh_const ()) acc ) vars IdMap.empty in
    subst subst_map axiom

