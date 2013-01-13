open Form
open Config

let var1 = mk_var (fresh_ident "v")
let var2 = mk_var (fresh_ident "v")
let var3 = mk_var (fresh_ident "v")
let var4 = mk_var (fresh_ident "v")
let var5 = mk_var (fresh_ident "v")

let null_id = (mk_ident "null")
let null = mk_const null_id

let alloc_id = (mk_ident "Alloc")

let reach_name = "Reach_"

let reach_id (f, n) = (reach_name ^ f, n)

let reach f x y z = mk_pred (reach_id f) [x; y; z]

let fun_of_reach = 
  let reach_len = String.length reach_name in
  fun (id : ident) -> (String.sub (fst id) reach_len (String.length (fst id) - reach_len), (snd id))

let is_reach = 
  let re = Str.regexp reach_name in
  fun ((name, _) : ident) -> Str.string_match re name 0

let jp_name = "join_"

let jp_id (f, n) = (jp_name ^ f, n)

let jp f x y = mk_app (jp_id f) [x; y]

let fun_of_jp =
  let jp_len = String.length jp_name in
  fun (id : ident) -> (String.sub (fst id) jp_len (String.length (fst id) - jp_len), (snd id))

let is_jp = 
  let re = Str.regexp jp_name in
  fun ((name, _) : ident) -> Str.string_match re name 0

let lb_name = "lb_"

let lb_id (f, n) = (lb_name ^ f, n)

let lb f x y = mk_app (lb_id f) [x; y] (*DZ: switch for axioms with lb ??*)

let update_axioms f new_f ind upd =
    let f_upd1 = 
      mk_or [mk_eq ind var1; mk_not (mk_eq var1 var2); mk_eq (mk_app f [var1]) (mk_app new_f [var2])]
    in
    let f_upd2 = mk_eq (mk_app new_f [ind]) upd in
    let reach_upd =
      let r = reach f in
      let new_reach u v w =
	mk_or [mk_and [r u v w; r u v ind];
	       mk_and [mk_not (mk_eq ind w); r u ind w; r upd v ind; r upd v w]]
      in
      if !with_reach_axioms then
	[mk_or [mk_not (reach new_f var1 var2 var3); new_reach var1 var2 var3];
	 mk_or [reach new_f var1 var2 var3; mk_not (new_reach var1 var2 var3)]]
      else []
    in
    f_upd1 :: f_upd2 :: reach_upd

let reach_axioms f = 
  let af x = mk_app f [x] in
  let reach = reach f in
  (* axioms *)
  let refl = reach var1 var1 var2 in
  let reac = mk_or [mk_not (reach var1 var2 var3); 
		    reach var1 var2 var2] in 
  let step = mk_or [reach var1 (af var1) var2; mk_eq var1 var2] in
  (* let ufld = mk_or [mk_not (reach var1 var2 var3); mk_eq var1 var2; reach (af var1) var2 var3] in *)
  let cycl = mk_or [mk_not (mk_eq (af var1) var1); 
		    mk_not (reach var1 var2 var2); mk_eq var1 var2] in
  (* let cycl2 = mk_or [mk_not (reach var1 var2 var3); mk_not (reach var2 var1 var3); mk_not (reach var1 var3 var3); mk_eq var1 var2; mk_eq var1 var3] in *)
  let sndw = mk_or [mk_not (reach var1 var2 var1); mk_eq var1 var2] in
  let lin1 = mk_or [mk_not (reach var1 var2 var2); reach var1 var3 var2; reach var1 var2 var3] in
  let lin2  = mk_or [mk_not (reach var1 var2 var3); mk_not (reach var1 var4 var5); 
		    mk_and [reach var1 var4 var3; reach var4 var2 var3]; 
		    mk_and [reach var1 var2 var5; reach var2 var4 var5]] in
  let trn1 = mk_or [mk_not (reach var1 var2 var3); mk_not (reach var2 var4 var3); 
		    reach var1 var4 var3] in
  let trn2 = mk_or [mk_not (reach var1 var2 var3); mk_not (reach var2 var4 var3); 
		    mk_not (reach var2 var3 var3); reach var1 var2 var4] in
  let lbef = mk_or [mk_not (reach var1 var2 var3); mk_not (mk_eq var3 (af var2)); mk_eq (lb f var1 var3) var2]  in
  (**)
  if !with_reach_axioms then
    [mk_comment "refl" refl; 
     mk_comment "step" step; 
     mk_comment "cycl" cycl; 
     mk_comment "reach" reac;
     mk_comment "sndw" sndw; 
     mk_comment "linear1" lin1;
     mk_comment "linear2" lin2;
     mk_comment "trans1" trn1; 
     mk_comment "trans2" trn2;
     mk_comment "before" lbef]
  else []

let jp_axioms f =
  let reach = reach f in
  let jp1 = reach var1 (jp f var1 var3) (jp f var1 var3) in
  let jp2 = mk_or [mk_not (reach var1 var2 var2); mk_not (reach var3 var2 var2); 
		   reach var3 (jp f var1 var3) (jp f var1 var3)] in
  let jp3 = mk_or [mk_not (reach var1 var2 var2); mk_not (reach var3 var2 var2); 
		   reach var1 (jp f var1 var3) var2] in
  let jp4 = mk_or [reach var3 (jp f var1 var3) (jp f var1 var3); mk_eq var1 (jp f var1 var3)] in
  if !with_jp_axioms then 
    [mk_comment "join1" jp1; 
     mk_comment "join2" jp2;
     mk_comment "join3" jp3;
     mk_comment "join4" jp4]
  else []

let null_axioms f =
  [mk_eq (mk_app f [null]) null]

let alloc_axioms = 
  if !with_alloc_axioms then [mk_pred alloc_id [null]] else []

let alloc_update_axioms id alloc new_alloc =
  let x = mk_const id in
  let mk_alloc x = mk_pred alloc [x] in
  let mk_new_alloc x = mk_pred new_alloc [x] in
  [mk_not (mk_alloc x); 
   mk_new_alloc x;
   mk_or [mk_eq x var1; mk_not (mk_alloc var1); mk_new_alloc var1];
   mk_or [mk_eq x var1; mk_not (mk_new_alloc var1); mk_alloc var1]]

let alloc_dispose_axioms id alloc new_alloc =
  (*dispose if the symmetric of new*)
  alloc_update_axioms id new_alloc alloc

(*entry point: when entering a part of the heap, used for SL*)
let ep_name = "ep_"

let ep_id (f, n) = (ep_name ^ f, n)

let ep f x = mk_app (ep_id f) [x]

let fun_of_ep = 
  let ep_len = String.length ep_name in
  fun (id : ident) -> (String.sub (fst id) ep_len (String.length (fst id) - ep_len), (snd id))

let is_ep = 
  let re = Str.regexp ep_name in
  fun ((name, _) : ident) -> Str.string_match re name 0

let extract_ep t = match t with
  | FunApp (id, _) when is_ep id -> Some (fun_of_ep id)
  | _ -> None

(* f is the pred defining an heap zone, h the pointer fct *)
let ep_axioms f h =
  let ep = ep f var1 in
  let reachWo = reach h in
  let reach x y = reach h x y y in
  let in_f v = mk_pred f [v] in
  let ep1 = mk_and [reach var1 ep; mk_or [in_f ep; mk_and [mk_eq var1 ep; mk_implies (reach var1 var2) (mk_not (in_f var2))]]] in
  let ep2 = mk_implies (mk_and [reach var1 var2; in_f var2]) (reachWo var1 ep var2) in
    [mk_comment "entrypoint1" ep1; 
     mk_comment "entrypoint2" ep2]

let get_eps f =
  IdMap.fold 
    (fun id decl acc ->
      if (not decl.is_pred) && decl.arity = 1 && is_ep id then IdSet.add (fun_of_ep id) acc
      else acc)
    (sign f) IdSet.empty
(*******)

let fun_axioms f = (*mk_eq (mk_app f [null]) null ::*) jp_axioms f

let extract_axioms fs =
  List.partition (fun f -> IdSet.empty <> fv f) fs


let simplify f =
  let rec rewrite_atoms = function
    | Not f -> mk_not (rewrite_atoms f)
    | And fs ->
	smk_and (List.map rewrite_atoms fs)
    | Or fs ->
	smk_or (List.map rewrite_atoms fs)
    | Pred (fn, [t1; t2; t3]) when is_reach fn ->
	if t1 = t3 then
	  if t1 = t2 then mk_true
	  else mk_eq t1 t2
	else 
	  if t1 = null then mk_eq t1 t2 
	  else Pred (fn, [t1; t2; t3])
    | Eq (t1, t2) when t1 = t2 -> mk_true
    | f -> f
  in rewrite_atoms (nnf f) 
	
(*
let simplify_model m : Model.model =
  Model.fold (fun id def sm -> 
    if not (is_reach id) then 
      Model.add_def id (def.Model.input, def.Model.output) sm
    else  
      match def.Model.input with 
      | [x1; x2; x3] when x1 = x2 -> 
	  Model.add_def id ([x1; x3; x3], def.Model.output) sm
      | i -> Model.add_def id (i, def.Model.output) sm) 
    m Model.empty
*)


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

(*
let add_axioms pf_a pf_b =
  let a_unary = unary_funs (mk_and pf_a) in
  let b_unary = (*IdSet.diff*) (unary_funs (mk_and pf_b)) (*a_unary*) in
  let a_init_funs = 
    IdSet.filter (function (_, n) -> n = 0) a_unary 
  in
  let b_init_funs = 
    IdSet.filter 
      (function (_, n as id) -> n = 0 || IdSet.mem id a_unary) 
      b_unary 
  in
  let a_axioms =
    IdSet.fold (fun id acc -> reach_axioms id @ acc) a_init_funs [] @
    IdSet.fold (fun id acc -> fun_axioms id @ acc) a_unary [] @
    alloc_axioms 
  in
  let b_axioms =
    IdSet.fold (fun id acc -> reach_axioms id @ acc) b_init_funs [] @
    IdSet.fold (fun id acc -> fun_axioms id @ acc) b_unary []
  in
  a_axioms @ pf_a, b_axioms @ pf_b
*)

let make_axioms fs =
  let unaries = List.map (fun f -> unary_funs (mk_and f)) fs in
  let init_funs = (*List.map (fun set -> IdSet.filter (fun (_, n) -> n = 0) set)*) unaries in
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
    (alloc_axioms @ List.hd axioms) :: (List.tl axioms)

let add_axioms fs =
  let axioms = make_axioms fs in
    List.map2 (@) axioms fs

let skolemize fresh_const axiom =
  let vars = fv axiom in
  let subst_map = IdSet.fold (fun v acc -> IdMap.add v (fresh_const ()) acc ) vars IdMap.empty in
    subst subst_map axiom

