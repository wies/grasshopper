(** Utility functions for manipulating GRASS formulas *)

open Form
open Util

let form_set_of_list fs =
  List.fold_left 
    (fun acc f -> FormSet.add f acc) 
    FormSet.empty fs

let term_set_of_list ts =
  List.fold_left 
    (fun acc t -> TermSet.add t acc) 
    TermSet.empty ts

let id_set_of_list ids =
  List.fold_left 
    (fun acc id -> IdSet.add id acc) 
    IdSet.empty ids

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

let unsafe_sort_of t = Util.unopt (sort_of t)

let rec sort_ofs = function
  | [] -> None
  | t :: ts -> 
      match sort_of t with
      |	None -> sort_ofs ts
      |	s -> s

let range_sort_of_field f =
  match sort_of f with
  | Some (Fld srt) -> srt
  | _ -> failwith "untyped or illtyped field expression"

let element_sort_of_set s =
  match sort_of s with
  | Some (Set srt) -> srt
  | _ -> failwith "untyped or illtyped set expression"

let has_sort srt t = 
  match sort_of t with
  | Some srt' -> srt = srt'
  | None -> false

let sort_parameters = function
  | Fld srt
  | Set srt -> [srt]
  | _ -> []

let is_free_const = function
  | App (FreeSym _, [], _) -> true
  | _ -> false

let eq_name id1 id2 = name id1 = name id2

(** {6 Smart constructors} *)

let mk_true = BoolOp (And, [])
let mk_false = BoolOp (Or, [])
let mk_bool b = if b then mk_true else mk_false

let mk_int i = App (IntConst i, [], Some Int)

let mk_ident name = (name, 0)

let mk_free_fun ?srt id args = App (FreeSym id, args, srt)
let mk_free_const ?srt id = App (FreeSym id, [], srt)
let mk_const ?srt sym = App (sym, [], srt)

let mk_fresh_var ?srt name = Var (fresh_ident ("?" ^ name), srt)

let mk_var ?srt id =  Var (id, srt)

let mk_free_app ?srt id ts = App (FreeSym id, ts, srt)

let mk_app ?srt sym ts = App (sym, ts, srt)

let mk_atom sym ts = Atom (mk_app ~srt:Bool sym ts)

let mk_pred id ts = mk_atom (FreeSym id) ts

let mk_eq_term s t =
  mk_app ~srt:Bool Eq [s; t]

let mk_eq s t = mk_atom Eq [s; t]

let mk_lt s t = mk_atom Lt [s; t]
let mk_gt s t = mk_atom Gt [s; t]
let mk_leq s t = mk_atom LtEq [s; t]
let mk_geq s t = mk_atom GtEq [s; t]

let mk_plus s t = mk_app ~srt:Int Plus [s; t]
let mk_minus s t = mk_app ~srt:Int Minus [s; t]
let mk_uminus s = mk_app ~srt:Int UMinus [s]
let mk_mult s t = mk_app ~srt:Int Mult [s; t]
let mk_div s t = mk_app ~srt:Int Div [s; t]

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

let mk_read_form fld ind = match sort_of fld with
  | Some (Fld Bool) -> mk_atom Read [fld; ind]
  | _ -> failwith "mk_read_form requries a Fld Bool"

let mk_write fld ind upd =
  mk_app ?srt:(sort_of fld) Write [fld; ind; upd]

let mk_ep fld set t = mk_app ~srt:Loc EntPnt [fld; set; t]

let mk_btwn_term fld t1 t2 t3 =
  mk_app ~srt:Bool Btwn [fld; t1; t2; t3]

let mk_btwn fld t1 t2 t3 =
  mk_atom Btwn [fld; t1; t2; t3]
  
let mk_reach fld t1 t2 = 
  mk_btwn fld t1 t2 t2
  
let mk_empty srt = mk_app ?srt:srt Empty []

let mk_loc_set id = mk_free_const ~srt:(Set Loc) id

let mk_setenum ts = 
  let srt = match sort_ofs ts with
  | Some esrt -> Some (Set esrt)
  | None -> None
  in
    match ts with
    | [] -> mk_empty srt
    | _ -> mk_app ?srt:srt SetEnum ts

let mk_inter sets = 
  if List.exists (function App (Empty, [], _) -> true | _ -> false) sets
  then mk_empty (sort_ofs sets)
  else mk_app ?srt:(sort_ofs sets) Inter sets

let mk_union sets = 
  let sets1 =
    List.filter 
      (function App (Empty, [], _) -> false | _ -> true) 
      sets
  in
  mk_app ?srt:(sort_ofs sets) Union sets1

let mk_diff s t = mk_app ?srt:(sort_of s) Diff [s; t]

let mk_elem_term e s = mk_app ~srt:Bool Elem [e; s]
let mk_elem e s = mk_atom Elem [e; s]

let smk_elem e = function
  | App (Empty, _, _) -> mk_false
  | s -> mk_elem e s

let mk_subseteq s t = mk_atom SubsetEq [s; t]

let mk_frame_term x a f f' = mk_app ~srt:Bool Frame [x; a; f; f']

(* @param a the set of allocated locations
 * @param x the footprint in the pre-state
 * @param f the field in the pre-state
 * @param f' the field in the post-state
 *)
let mk_frame x a f f' = mk_atom Frame [x; a; f; f']

let mk_and = function
  | [f] -> f
  | fs -> BoolOp(And, fs)

let mk_or = function
  | [f] -> f
  | fs -> BoolOp (Or, fs)

let mk_not = function
  | BoolOp (op, []) -> BoolOp (dualize_op op, [])
  | BoolOp (Not, [f]) -> f
  | f -> BoolOp (Not, [f])

let mk_neq s t = mk_not (mk_eq s t)

let mk_strict_subset s t = mk_and [mk_subseteq s t; mk_neq s t]

let rec mk_binder ?(ann=[]) b bv f = 
  match bv, ann with 
  | [], [] -> f
  | _ -> 
      match f with
      | Binder (_, [], f', ann') ->
          mk_binder ~ann:(ann @ ann') b bv f'
      | Binder (b', bv', f', ann') when b = b' ->
          mk_binder ~ann:(ann @ ann') b (bv @ bv') f'
      | _ -> Binder (b, bv, f, ann)
let mk_forall ?(ann=[]) bv f = mk_binder ~ann:ann Forall bv f 
let mk_exists ?(ann=[]) bv f = mk_binder ~ann:ann Exists bv f 
  

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
	| BoolOp (op', fs0) :: fs1 when op = op' -> 
	    mkop1 (fs0 @ fs1) acc
	| BoolOp (And, []) :: fs1 when op = Or -> mk_true
	| BoolOp (Or, []) :: fs1 when op = And -> mk_false
	| f :: fs1 -> mkop1 fs1 (FormSet.add f acc)
      in mkop1 fs FormSet.empty

let smk_and fs = smk_op And fs
let smk_or fs = smk_op Or fs

(** {6 Normal form computation} *)

(** Compute negation normal form of a formula *)
let rec nnf = function
  | BoolOp (Not, [BoolOp (Not, [f])]) -> nnf f
  | BoolOp (Not, [BoolOp (op, fs)]) -> 
      smk_op (dualize_op op) (List.map (fun f -> nnf (mk_not f)) fs)
  | BoolOp (Not, [Binder (b, xs, f, a)]) -> 
      Binder (dualize_binder b, xs, nnf (mk_not f), a)
  | BoolOp (op, fs) -> smk_op op (List.map nnf fs)
  | Binder (b, vs, f, a) -> mk_binder ~ann:a b vs (nnf f)
  | f -> f
  
(** Compute conjunctive normal form of a formula *)
(* Todo: avoid exponential blow-up *)
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

let mk_sequent antecedent succedent =
  smk_or (List.map mk_not antecedent @ succedent)

let mk_iff a b =
  smk_or [smk_and [a; b]; smk_and [nnf (mk_not a); nnf (mk_not b)]]


(** {6 Generic formula manipulation} *)

(** Fold all terms appearing in the formula [f] using catamorphism [fn] and initial value [init] *)
let fold_terms fn init f =
  let rec ft acc = function
    | Atom t -> fn acc t
    | BoolOp (_, fs) ->	List.fold_left ft acc fs
    | Binder (_, _, f, _) -> ft acc f
  in ft init f

(** Apply the function fn to all terms appearing in [f] *)
let map_terms fn f =
  let rec mt = function
    | Atom t -> Atom (fn t)
    | BoolOp (op, fs) -> BoolOp (op, List.map mt fs)
    | Binder (b, vs, f, a) -> 
        let a1 = 
          List.map (function
            | TermGenerator (bvs, fvs, gs, t) ->
                let gs1 = List.map (function Match (t, f) -> Match (fn t, f)) gs in
                TermGenerator (bvs, fvs, gs1, fn t)
            | a -> a) a
        in
        Binder (b, vs, mt f, a1)
  in mt f

(** Like {!fold_terms} except that [fn] takes the set of bound variables of the given context as additional argument *)
let fold_terms_with_bound fn init f =
  let rec ft bv acc = function
    | Atom t -> fn bv acc t
    | BoolOp (_, fs) ->	List.fold_left (ft bv) acc fs
    | Binder (_, vs, f, _) -> 
	ft (List.fold_left (fun bv (x, _) -> IdSet.add x bv) bv vs) acc f
  in ft IdSet.empty init f

(** Computes the set of identifiers of free variables occuring in term [t]
 ** union the accumulated set of identifiers [vars]. *)
let fvt vars t =
  let rec fvt1 vars = function
  | Var (id, _) -> IdSet.add id vars
  | App (_, ts, _) -> List.fold_left fvt1 vars ts
  in fvt1 vars t

(** Computes the set of free variables occuring in term [t]. *)
let fv_term t = fvt IdSet.empty t

(** Computes the set of free variables occuring in formula [f]. *)
let fv f = 
  let rec fvt bv vars = function
    | Var (id, _) -> 
	if IdSet.mem id bv 
	then vars 
	else IdSet.add id vars
    | App (_, ts, _) ->
	List.fold_left (fvt bv) vars ts
  in fold_terms_with_bound fvt IdSet.empty f

(** Computes the set of free variables of formula [f] together with their sorts. *)
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

let sorts f =
  let rec s acc = function
    | Var (_, Some srt) -> SortSet.add srt acc
    | App (_, ts, srt_opt) ->
        let acc1 = match srt_opt with
        | Some srt -> SortSet.add srt acc
        | None -> acc
        in
        List.fold_left s acc1 ts
    | _ -> acc
  in
  fold_terms s SortSet.empty f

(** Computes the set of free constants occuring in term [t].
 ** Takes accumulator as additional argument. *)
let free_consts_term_acc consts t =
  let rec fct consts = function
  | Var _ -> consts
  | App (FreeSym id, [], _) -> IdSet.add id consts
  | App (_, ts, _) -> List.fold_left fct consts ts
  in fct consts t

(** Computes the set of free constants occuring in term [t]. *)
let free_consts_term t = free_consts_term_acc IdSet.empty t

(** Computes the set of free constants occuring in formula [f]. *)
let free_consts f =
  fold_terms free_consts_term_acc IdSet.empty f

(** Computes the set of ground terms appearing in [f].
 ** Free variables are treated as implicitly universally quantified *)
let ground_terms ?(include_atoms=false) f =
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
	if is_ground && (not include_atoms || srt <> Some Bool)
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

let fun_terms_with_vars f =
  let rec process acc t = match t with
    | App (_, ts, Some Bool) ->
      (* skip predicates *)
      List.fold_left process acc ts
    | App (_, ts, _) ->
      let acc = List.fold_left process acc ts in
        if not (IdSet.is_empty (fvt IdSet.empty t))
        then TermSet.add t acc
        else acc
    | Var _ -> acc
  in
    fold_terms process TermSet.empty f
     
(** Extracts the signature of formula [f]. *)
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

(** Extracts the signature of formula [f]. *)
let overloaded_sign f : (arity list SymbolMap.t) =
  let add_to_sign sym tpe decls =
    let old = try SymbolMap.find sym decls with Not_found -> [] in
      if List.mem tpe old then decls
      else SymbolMap.add sym (tpe :: old) decls
  in
  let fail t = 
    let t_str = string_of_term t in
    let f_str = string_of_form f in
    let msg =
      "tried to extract signature from untyped term:\n" ^
      "  " ^ t_str ^ "\nin formula\n" ^ f_str
    in
    failwith msg
    in
  let rec signt (decls : arity list SymbolMap.t) t = match t with
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
	in List.fold_left signt (add_to_sign sym (arg_srts, res_srt) decls) args
  in 
  fold_terms signt SymbolMap.empty f

let map_id_term fct t =
  let rec sub = function
    | Var (id, srt) -> Var (fct id, srt)
    | App (sym, ts, srt) -> 
	let sym1 = match sym with
	| FreeSym id -> FreeSym (fct id)
	| _ -> sym
	in
	App (sym1, List.map sub ts, srt)
  in sub t

let map_id fct f =
  let rec sub = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map sub fs)
    | Atom t -> Atom (map_id_term fct t)
    | Binder (b, vs, f, a) -> Binder (b, vs, sub f, a)
  in sub f

(** Substitutes all identifiers in term [t] according to substitution map [subst_map] *)
let subst_id_term subst_map t =
  let sub_id id =
    try IdMap.find id subst_map with Not_found -> id
  in
    map_id_term sub_id t

(** Substitutes all identifiers in formula [f] according to substitution map [subst_map].
 ** Not capture avoiding. *)
let subst_id subst_map f =
  let subt = subst_id_term subst_map in
  let subg g = match g with
    | Match (t, f) -> Match (subt t, f)
  in
  let suba a = match a with
    | Comment c -> Comment c
    | TermGenerator (bvs, fvs, guards, gen_term) -> 
      TermGenerator (bvs, fvs, List.map subg guards, subt gen_term)
  in
  let rec sub = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map sub fs)
    | Atom t -> Atom (subt t)
    | Binder (b, vs, f, a) -> Binder (b, vs, sub f, List.map suba a)
  in sub f

(** Substitutes all constants in term [t] according to substitution function [subst_fun]. *)
let subst_consts_fun_term subst_fun t =
  let rec sub = function
    | (App (FreeSym id, [], srt) as t) -> subst_fun id t 
    | App (sym, ts, srt) -> App (sym, List.map sub ts, srt)
    | t -> t
  in
  sub t

(** Substitutes all constants in formula [f] according to substitution function [subst_fun]. *)
let subst_consts_fun subst_fun f =
  map_terms (subst_consts_fun_term subst_fun) f

(** Substitutes all constants in term [t] according to substitution map [subst_map]. *)
let subst_consts_term subst_map t =
  let sub_id id t =
    try IdMap.find id subst_map with Not_found -> t
  in
  subst_consts_fun_term sub_id t

(** Substitutes all constants in formula [f] according to substitution map [subst_map]. *)
let subst_consts subst_map f =
  map_terms (subst_consts_term subst_map) f


(** Substitutes all variables in term [t] according to substitution map [subst_map]. *)
let subst_term subst_map t =
  let sub_id id t =
    try IdMap.find id subst_map with Not_found -> t
  in
  let rec sub = function
    | (Var (id, srt) as t) -> sub_id id t 
    | App (sym, ts, srt) -> App (sym, List.map sub ts, srt)
  in sub t

(** Substitutes all free variables in formula [f] according to substitution map [subst_map].
 ** Capture avoiding. *)
let subst subst_map f =
  let rename_vars vs sm =
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
    in vs1, sm2
  in
  let suba bvs1 sm = function
    | Comment c -> Comment c
    | TermGenerator (bvs, fvs, guards, gen_term) -> 
        let fvs1, sm1 = rename_vars fvs sm in
        let guards1 = 
          List.map 
            (function Match (t, f) -> Match (subst_term sm1 t, f))
            guards
        in
        TermGenerator (bvs1, fvs1, guards1, subst_term sm1 gen_term)
  in
  let rec sub sm = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map (sub sm) fs)
    | Atom t -> Atom (subst_term sm t)
    | Binder (b, vs, f, a) ->
        let vs1, sm1 = rename_vars vs sm in
        Binder (b, vs1, sub sm1 f, List.map (suba vs1 sm1) a)
  in sub subst_map f

(** Propagate existentially quantified variables upward in the formula [f].
 ** Assumes that [f] is in negation normal form. *)
let propagate_exists f =
  let rec merge sm zs xs ys ys2 =
    match xs, ys with
    | (x, srt1) :: xs1, (y, srt2) :: ys1 ->
        if srt1 = srt2
        then merge (IdMap.add x (mk_var ~srt:srt1 y) sm) ((y, srt2) :: zs) xs1 (ys2 @ ys1) []
        else merge sm zs xs ys1 ((y, srt2) :: ys2)
    | [], _ -> sm, ys @ ys2 @ zs
    | _, [] -> 
        if ys2 = [] then sm, xs @ zs
        else merge sm (List.hd xs :: zs) (List.tl xs) ys2 []
  in
  let rec prop = function
    | BoolOp (Or, fs) ->
        let fs1, vs = 
          List.fold_right (fun f (fs2, vs2) ->
            let f1, vs1 = prop f in
            let sm, vs = merge IdMap.empty [] vs1 vs2 [] in
            subst sm f1 :: fs2, vs) 
            fs ([], [])
        in BoolOp (Or, fs1), vs
    | BoolOp (And, fs) ->
        let fs1, vss = List.split (List.map prop fs) in
        BoolOp (And, fs1), List.concat vss
    | Binder (Exists, vs, f, a) -> 
        let vars = fv f in
        let vs0 = List.filter (fun (v, _) -> IdSet.mem v vars) vs in
        let sm, vs1 = 
          List.fold_left 
            (fun (sm, vs1) (v, srt) -> 
              let v1 = fresh_ident (name v) in
              IdMap.add v (mk_var ~srt:srt v1) sm, (v1, srt) :: vs1)
            (IdMap.empty, []) vs0
        in
        let f1 = subst sm f in
        (match a with 
        | [] -> f1, vs1
        | _ -> Binder (Exists, [], f1, a), vs1)
    | Binder (Forall, vs, f, a) ->
        let f1, vs1 = prop f in
        (match vs with
        | [] -> Binder (Forall, vs, f1, a), vs1
        | _ -> Binder (Forall, vs, mk_exists vs1 f1, a), [])
    | f -> f, []
  in
  let f1, vs = prop f in 
  mk_exists vs f1

(** Convert universal quantifiers in formula [f] into existentials where possible. *)
(** Assumes that [f] is in negation normal form. *)
let foralls_to_exists f =
  let rec find_defs bvs defs fs =
    let rec find nodefs defs gs = function
      | BoolOp (Not, [Atom (App (Eq, [Var (x, _) as xt; t], _))]) :: fs 
        when IdSet.mem x nodefs && 
          IdSet.is_empty (IdSet.inter nodefs (fv_term t)) ->
          find (IdSet.remove x nodefs) (mk_eq xt t :: defs) gs fs
      | BoolOp (Not, [Atom (App (Eq, [t; Var (x, srt) as xt], _))]) :: fs 
        when IdSet.mem x nodefs && 
          IdSet.is_empty (IdSet.inter nodefs (fv_term t)) ->
          find (IdSet.remove x nodefs) (mk_eq xt t :: defs) gs fs
      | BoolOp (Or, fs1) :: fs ->
          find nodefs defs gs (fs1 @ fs)
      | f :: fs ->
          find nodefs defs (f :: gs) fs
      | [] ->
          if IdSet.subset bvs nodefs 
          then nodefs, defs, gs
          else find_defs nodefs defs gs
    in find bvs defs [] fs
  in
  let rec distribute_and bvs gs = function
    | BoolOp (And, fs) :: gs1 ->
        let fs1 = List.map (fun f -> mk_or (List.rev_append gs (f :: gs1))) fs in
        cf (mk_forall bvs (mk_and fs1))
    | g :: gs1 -> distribute_and bvs (g :: gs) gs1
    | [] -> mk_forall bvs (mk_or (List.rev gs))
  and cf = function
    | Binder (Forall, bvs, BoolOp (And, fs), a) ->
        let fs1 = List.map (fun f -> cf (Binder (Forall, bvs, f, a))) fs in
        mk_and fs1
    | Binder (Forall, bvs, BoolOp (Or, fs), a) ->
        let bvs_set = id_set_of_list (List.map fst bvs) in
        let nodefs, defs, gs = find_defs bvs_set [] fs in
        let ubvs, ebvs = List.partition (fun (x, _) -> IdSet.mem x nodefs) bvs in
        (match ebvs with
        | [] -> distribute_and bvs [] gs
        | _ ->
          let g = cf (mk_forall ubvs (mk_or gs)) in
          Binder (Exists, bvs, mk_and (defs @ [g]), a))
    | Binder (Exists, bvs, f, a) ->
        mk_exists ~ann:a bvs (cf f)
    | BoolOp (And as op, fs)
    | BoolOp (Or as op, fs) ->
        let fs1 = List.map cf fs in
        BoolOp (op, fs1)
    | f -> f
  in
  cf f

(** Skolemize formula [f]. 
 ** Assumes that [f] is in negation normal form. *)
let skolemize f =
  let rec sk vs = function
    | BoolOp (op, fs) -> smk_op op (List.map (sk vs) fs)
    | Binder (Forall, bvs, f, a) ->
	let vs1 = 
	  List.fold_left 
	    (fun vs1 (id, srt) -> IdMap.add id srt vs1) vs bvs 
	in
	Binder (Forall, bvs, sk vs1 f, a)
    | Binder (Exists, bvs, f, a) ->
	let ts = IdMap.fold (fun id srt ts -> mk_var ~srt:srt id :: ts) vs [] in
	let sm = List.fold_left 
	    (fun sm (id, srt) -> 
	      let sk_fn = FreeSym (fresh_ident ("sk_" ^ (name id))) in
	      IdMap.add id (mk_app ~srt:srt sk_fn ts) sm) 
	    IdMap.empty bvs
	in 
	annotate (subst sm (sk vs f)) a
    | f -> f
  in 
  let f1 = propagate_exists f in
  sk IdMap.empty f1

(** Make all comments in formula [f] unique *)
let unique_comments f =
  let rec uc = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map uc fs)
    | Binder (b, vs, f, anns) ->
        let anns1 = List.map (function Comment c -> Comment (str_of_ident (fresh_ident c)) | a -> a) anns in
        Binder (b, vs, uc f, anns1)
    | f -> f
  in
  uc f

let comment_uncommented f = match f with
  | Binder (_, _, _, anns) ->
    if List.exists (fun a -> match a with Comment _ -> true | _ -> false) anns
    then f
    else mk_comment "unnamed" f
  | f -> mk_comment "unnamed" f

module Clauses = struct

  type clause = form list
  type clauses = clause list
       
  (** convert formula [f] into a set of clauses *)
  let from_form f : clauses = 
    let nf = cnf (nnf f) in
    let to_clause = function
      | BoolOp (Or, fs) -> fs
      | f -> [f]
    in
    match nf with
    | BoolOp (And, fs) -> List.map to_clause fs
    | f -> [to_clause f]
	  
  (** convert the set of clauses [cs] into a formula *)
  let to_form cs = smk_and (List.map smk_or cs)

end


