open Form
open Util

let form_set_of_list fs =
  List.fold_left 
    (fun acc f -> FormSet.add f acc) 
    FormSet.empty fs

let fresh_ident =
  let used_names = Hashtbl.create 0 in
  fun (name : string) ->
    let last_index = 
      try Hashtbl.find used_names name 
      with Not_found -> -1
    in 
    Hashtbl.replace used_names name (last_index + 1);
    (name, last_index + 1)

let dualize_op op = 
  match op with
  | And -> Or
  | Or -> And
  | Not -> failwith "tried to dualize Not"
  
let dualize_binder = function
  | Forall -> Exists
  | Exists -> Forall

let name id = fst id

let sort_of = function
  | Var (_, s) 
  | App (_, _, s) -> s

let rec sort_ofs = function
  | [] -> None
  | t :: ts -> 
      match sort_of t with
      |	None -> sort_ofs ts
      |	s -> s

let has_sort srt t = 
  match sort_of t with
  | Some srt' -> srt = srt'
  | None -> false

let is_free_const = function
  | App (FreeSym _, [], _) -> true
  | _ -> false

let eq_name id1 id2 = name id1 = name id2

(** Smart constructors *)

let mk_ident name = (name, 0)

let mk_free_const ?srt id = App (FreeSym id, [], srt)
let mk_const ?srt sym = App (sym, [], srt)

let mk_fresh_var ?srt name = Var (fresh_ident ("?" ^ name), srt)

let mk_var ?srt id =  Var (id, srt)

let mk_free_app ?srt id ts = App (FreeSym id, ts, srt)

let mk_app ?srt sym ts = App (sym, ts, srt)

let mk_atom sym ts = Atom (mk_app ~srt:Bool sym ts)

let mk_pred id ts = mk_atom (FreeSym id) ts

let mk_eq s t = mk_atom Eq [s; t]

let mk_null = mk_app ~srt:Loc Null []

let mk_read fld ind = 
  let srt = match sort_of fld with
  | Some (Fld s) -> Some s
  | None -> None
  | Some s -> 
      failwith 
	("tried to read from term" ^ 
         (string_of_term fld) ^ " which is of sort " ^ (string_of_sort s) ^ ".\n" ^
         "Expected sort (Fld X) for some sort X.")
  in mk_app ?srt:srt Read [fld; ind]

let mk_write fld ind upd =
  mk_app ?srt:(sort_of fld) Write [fld; ind; upd]

let mk_ep fld set t = mk_app ~srt:Loc EntPnt [fld; set; t]

let mk_reachwo fld t1 t2 t3 =
  mk_atom ReachWO [fld; t1; t2; t3]
  
let mk_reach fld t1 t2 = mk_reachwo fld t1 t2 t2

let mk_empty srt = mk_app ?srt:srt Empty []

let mk_setenum ts = 
  let srt = match sort_ofs ts with
  | Some esrt -> Some (Set esrt)
  | None -> None
  in mk_app ?srt:srt SetEnum ts

let mk_inter sets = mk_app ?srt:(sort_ofs sets) Inter sets

let mk_union sets = mk_app ?srt:(sort_ofs sets) Union sets

let mk_diff s t = mk_app ?srt:(sort_of s) Diff [s; t]

let mk_elem e s = mk_atom Elem [e; s]

let mk_subseteq s t = mk_atom SubsetEq [s; t]

(* 'a' is the set allocated objects
 * 'x' is the footprint of the SL formula
 * 'f' is the next field
 * (un)primed corresponds to before/after
 *)
let mk_frame x x' a a' f f' = mk_atom Frame [x; x'; a; a'; f; f']

let mk_true = BoolOp (And, [])
let mk_false = BoolOp (Or, [])
let mk_bool b = if b then mk_true else mk_false

let mk_and = function
  | [f] -> f
  | fs -> BoolOp(And, fs)

let mk_or = function
  | [f] -> f
  | fs -> BoolOp (Or, fs)

let mk_not = function
  | BoolOp (op, []) -> BoolOp (dualize_op op, [])
  | f -> BoolOp (Not, [f])

let mk_neq s t = mk_not (mk_eq s t)

let mk_binder ?(ann=[]) b bv f = Binder (b, bv, f, ann)
let mk_forall ?(ann=[]) bv f = Binder (Forall, bv, f, ann) 
let mk_exists ?(ann=[]) bv f = Binder (Exists, bv, f, ann) 

let annotate f ann = 
  match f with
  | Binder (b, vs, f1, ann1) -> Binder (b, vs, f1, ann @ ann1)
  | _ -> Binder (Forall, [], f, ann)

let mk_comment c f = annotate f [Comment c]

let smk_op op fs =
  match op with
  | Not -> mk_not (List.hd fs)
  | _ -> 
      let rec mkop1 fs acc = 
	match fs with
	| [] ->
            begin
              match FormSet.elements acc with
	      | [f] -> f
	      | fs -> BoolOp (op, fs)
            end
	| BoolOp (op', fs0) :: fs1 -> 
	    if op = op' 
	    then mkop1 (fs0 @ fs1) acc
	    else BoolOp (op', [])
	| f :: fs1 -> mkop1 fs1 (FormSet.add f acc)
      in mkop1 fs FormSet.empty

let smk_and fs = smk_op And fs
let smk_or fs = smk_op Or fs

(** compute negation normal form of a formula *)
let rec nnf = function
  | BoolOp (Not, [BoolOp (Not, [f])]) -> nnf f
  | BoolOp (Not, [BoolOp (op, fs)]) -> 
      smk_op (dualize_op op) (List.map (fun f -> nnf (mk_not f)) fs)
  | BoolOp (Not, [Binder (b, xs, f, a)]) -> 
      Binder (dualize_binder b, xs, nnf (mk_not f), a)
  | BoolOp (op, fs) -> smk_op op (List.map nnf fs)
  | Binder (b, vs, f, a) -> Binder (b, vs, nnf f, a)
  | f -> f
  
(** compute conjunctive normal form of a formula *)
(* Todo: avoid exponential blowup *)
let rec cnf = 
  let rec cnf_and acc = function
    | [] -> mk_and acc
    | BoolOp (Or, []) :: _ -> BoolOp (Or, [])
    | BoolOp (And, fs) :: fs1 -> cnf_and acc (fs @ fs1)
    | f :: fs -> cnf_and (f :: acc) fs
  in
  let rec cnf_or acc = function
    | BoolOp (And, []) :: _ -> BoolOp (And, [])
    | [] -> mk_or acc
    | BoolOp(Or, fs) :: fs1 -> cnf_or acc (fs @ fs1)
    | BoolOp (And, fs) :: fs1 -> 
	let fs_or = acc @ fs1 in
	let fs_and = List.map (fun f -> mk_or (f :: fs_or)) fs in
	cnf (mk_and fs_and)
    | f :: fs -> cnf_or (f :: acc) fs  
  in
  function
    | BoolOp(And, fs) -> cnf_and [] (List.rev_map cnf fs)
    | BoolOp (Or, fs) -> cnf_or [] (List.rev_map cnf fs)
    | f -> f

let mk_implies a b =
  smk_or [nnf (mk_not a); b]

let mk_iff a b =
  smk_or [smk_and [a; b]; smk_and [nnf (mk_not a); nnf (mk_not b)]]

(** Fold all terms appearing in the formula f using fold function fn and initial value init *)
let fold_terms fn init f =
  let rec ft acc = function
    | Atom t -> fn acc t
    | BoolOp (_, fs) ->	List.fold_left ft acc fs
    | Binder (_, _, f, _) -> ft acc f
  in ft init f

(** Like fold_terms except that fn takes the set of bound variables of the given context as additional argument *)
let fold_terms_with_bound fn init f =
  let rec ft bv acc = function
    | Atom t -> fn bv acc t
    | BoolOp (_, fs) ->	List.fold_left (ft bv) acc fs
    | Binder (_, vs, f, _) -> 
	ft (List.fold_left (fun bv (x, _) -> IdSet.add x bv) bv vs) acc f
  in ft IdSet.empty init f

(** Computes the set of free variables of term t *)
let fvt vars t =
  let rec fvt1 vars = function
  | Var (id, _) -> IdSet.add id vars
  | App (_, ts, _) -> List.fold_left fvt1 vars ts
  in fvt1 vars t

(** Computes the set of free variables of formula f *)
let fv f = 
  let rec fvt bv vars = function
    | Var (id, _) -> 
	if IdSet.mem id bv 
	then vars 
	else IdSet.add id vars
    | App (_, ts, _) ->
	List.fold_left (fvt bv) vars ts
  in fold_terms_with_bound fvt IdSet.empty f

(** Computes the set of free variables of formula f together with their sorts *)
let sorted_free_vars f = 
  let rec fvt bv vars = function
    | Var (id, Some srt) -> 
	if IdSet.mem id bv 
	then vars 
	else IdSrtSet.add (id, srt) vars
    | App (_, ts, _) ->
	List.fold_left (fvt bv) vars ts
    | _ -> vars
  in fold_terms_with_bound fvt IdSrtSet.empty f

(** Computes the set of ground terms appearing in f
 * free variables are treated as implicitly universally quantified *)
let ground_terms f =
  let rec gt bv terms t = 
    match t with
    | Var (id, _) -> terms, false
    | App (_, ts, srt) ->
	let terms1, is_ground = 
	  List.fold_left 
	    (fun (terms, is_ground) t ->
	      let terms_t, is_ground_t = gt bv terms t in
	      terms_t, is_ground && is_ground_t)
	    (terms, true) ts
	in
	if is_ground && srt <> Some Bool
	then TermSet.add t terms1, true 
	else terms1, is_ground
  in 
  fold_terms_with_bound 
    (fun bv acc t -> fst (gt bv acc t)) 
    TermSet.empty f
  
let vars_in_fun_terms f =
  let rec fvt vars = function
    | Var (id, Some srt) -> IdSrtSet.add (id, srt) vars
    | App (_, ts, _) ->
	List.fold_left fvt vars ts
    | _ -> vars
  in
  let rec ct vars t = 
    match t with
    | App (_, ts, Some Bool) -> 
	List.fold_left ct vars ts
    | App _ -> fvt vars t
    | _ -> vars
  in fold_terms ct IdSrtSet.empty f
     
(** Extracts the signature of f *)
let sign f : signature =
  let fail t = 
    let t_str = string_of_term t in
    let f_str = string_of_form f in
    let msg =
      "tried to extract signature from untyped term:\n" ^
      "  " ^ t_str ^ "\nin formula\n" ^ f_str
    in
    failwith msg
    in
  let rec signt (decls : signature) t = match t with
    | Var _ -> decls
    | App (sym, args, res_srt_opt) ->
	let res_srt = 
	  match res_srt_opt with
	  | Some srt -> srt
	  | None -> fail t
	in
	let arg_srts = 
	  List.map
	    (function 
	      |	Var (_, Some srt) 
	      | App (_, _, Some srt) -> srt 
	      | t -> fail t
	    )
	    args
	in List.fold_left signt (SymbolMap.add sym (arg_srts, res_srt) decls) args
  in 
  fold_terms signt SymbolMap.empty f


(*
let funs_in_term t =
  let rec fts funs = function
    | Var _ -> funs
    | FunApp (sym, ts) ->
	let arity = List.length ts in
	List.fold_left fts (FunSymbolMap.add sym arity funs) ts
  in fts FunSymbolMap.empty t

let proper_funs f =
  let rec fts funs = function
    | Var _  -> funs
    | FunApp (id, ts) ->
	let funs1 = match ts with
	| [] -> funs
	| _ -> FunSymbolSet.add funs
	List.fold_left fts (IdSet.add id funs) ts
  in collect_from_terms fts IdSet.empty f
*)

(* Substitutes all identifiers in term t according to substitution map subst_map *)
let subst_id_term subst_map t =
  let sub_id id =
    try IdMap.find id subst_map with Not_found -> id
  in
  let rec sub = function
    | Var (id, srt) -> Var (sub_id id, srt)
    | App (sym, ts, srt) -> 
	let sym1 = match sym with
	| FreeSym id -> FreeSym (sub_id id)
	| _ -> sym
	in
	App (sym1, List.map sub ts, srt)
  in sub t

(** Substitutes all identifiers in formula f according to substitution map subst_map.
 ** Not capture avoiding. *)
let subst_id subst_map f =
  let subt = subst_id_term subst_map in
  let rec sub = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map sub fs)
    | Atom t -> Atom (subt t)
    | Binder (b, vs, f, a) -> Binder (b, vs, sub f, a)
  in sub f

(** Substitutes all variables in term t according to substitution map subst_map. *)
let subst_term subst_map t =
  let sub_id id t =
    try IdMap.find id subst_map with Not_found -> t
  in
  let rec sub = function
    | (Var (id, srt) as t) -> sub_id id t 
    | App (sym, ts, srt) -> App (sym, List.map sub ts, srt)
  in sub t

(** Substitutes all free variables in formula f according to substitution map subst_map.
 ** Capture avoiding. *)
let subst subst_map f =
  let suba sm = function
    | Comment c -> Comment c
  in
  let rec sub sm = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map (sub sm) fs)
    | Atom t -> Atom (subst_term sm t)
    | Binder (b, vs, f, a) ->
	let not_bound id _ = not (List.mem_assoc id vs) in
	let sm1 = IdMap.filter not_bound sm in 
	let occuring = IdMap.fold (fun _ t acc -> fvt acc t) sm IdSet.empty in
	let vs1, sm2 = 
	  List.fold_right 
	    (fun (x, srt) (vs1, sm2) ->
	      if IdSet.mem x occuring 
	      then 
		let x1 = fresh_ident (name x) in
		(x1, srt) :: vs1, IdMap.add x (Var (x1, Some srt)) sm2
	      else (x, srt) :: vs1, sm2)
	    vs ([], sm1)
	in Binder (b, vs1, sub sm2 f, List.map (suba sm2) a)
  in sub subst_map f

module Clauses = struct

  type clause = form list
  type clauses = clause list
       
  (** convert a formula into a set of clauses *)
  let from_form f : clauses = 
    let nf = cnf (nnf f) in
    let to_clause = function
      | BoolOp (Or, fs) -> fs
      | f -> [f]
    in
    match nf with
    | BoolOp (And, fs) -> List.map to_clause fs
    | f -> [to_clause f]
	  
  (** convert a set of clauses into a formula *)
  let to_form cs = smk_and (List.map smk_or cs)

end


