open Form

let with_reach_axioms = ref true
let with_jp_axioms = ref true
let with_alloc_axioms = ref false

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

let is_reach = 
  let re = Str.regexp reach_name in
  fun ((name, _) : ident) -> Str.string_match re name 0

let jp_name = "join_"

let jp_id (f, n) = (jp_name ^ f, n)

let jp f x y = mk_app (jp_id f) [x; y]

let is_jp = 
  let re = Str.regexp jp_name in
  fun ((name, _) : ident) -> Str.string_match re name 0

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
  let trn2 = mk_or [mk_not (reach var1 var2 var2); mk_not (reach var2 var3 var3); 
		    reach var1 var3 var3] in
  let trn3 = mk_or [mk_not (reach var1 var2 var3); mk_not (reach var2 var4 var3); 
		    mk_not (reach var2 var3 var3); reach var1 var2 var4] in
  (**)
  if !with_reach_axioms then
    [refl; step; cycl; reac; sndw; lin1; lin2; trn1; trn2; trn3]
  else []

let jp_axioms f =
  let reach = reach f in
  let jp1 = mk_or [mk_not (reach var1 var2 var2); mk_not (reach var3 var2 var2); 
		   reach (jp f var1 var3) var2 var2] in
  let jp2 = mk_or [mk_not (reach var1 var2 var2); mk_not (reach var3 var2 var2); 
		   reach var1 (jp f var1 var3) (jp f var1 var3)] in
  let jp3 = mk_or [mk_not (reach var1 var2 var2); mk_not (reach var3 var2 var2); 
		   reach var3 (jp f var1 var3) (jp f var1 var3)] in
  if !with_jp_axioms then [jp1; jp2; jp3]
  else []

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

let fun_axioms f = mk_eq (mk_app f [null]) null :: jp_axioms f

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
