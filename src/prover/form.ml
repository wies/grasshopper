open Util

(** Sorts and symbols *)

type ident = string * int

type sort =
  | Bool | Loc 
  | Set of sort 
  | Fld of sort

type arity = sort list * sort

type symbol =
  (* function symbols *)
  | Null | Select | Store | EntPnt
  | Empty | Union | Inter | Diff
  (* predicate symbols *)
  | Eq
  | ReachWO
  | Elem | SubsetEq 
  (* free constants, functions, and predicates *)
  | FreeSym of ident

(* Terms and formulas *)

type term = 
  | Var of ident * sort option
  | App of symbol * term list * sort option

type boolOp =
  | And | Or | Not

type annot =
  | Comment of string

type binder =
  | Forall | Exists

type form =
  | Atom of term
  | BoolOp of boolOp * form list
  | Binder of binder * (ident * sort) list * form * annot list

module IdSet = Set.Make(struct
    type t = ident
    let compare = compare
  end)

module IdMap = Map.Make(struct
    type t = ident
    let compare = compare
  end)

module TermSet = Set.Make(struct
    type t = term
    let compare = compare
  end)

module TermMap = Map.Make(struct
    type t = term
    let compare = compare
  end)

module FormSet = Set.Make(struct
    type t = form
    let compare = compare
  end)

module SymbolMap = Map.Make(struct
    type t = symbol
    let compare = compare
  end)

type signature = arity SymbolMap.t

type subst_map = term IdMap.t

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

let is_pred_id id = String.capitalize (fst id) = fst id

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

let eq_name id1 id2 = name id1 = name id2

(** Smart constructors *)

let mk_ident name = (name, 0)

let mk_free_const ?srt id = App (FreeSym id, [], srt)
let mk_const ?srt sym = App (sym, [], srt)

let mk_var ?srt id =  Var (id, srt)

let mk_app ?srt sym ts = App (sym, ts, srt)

let mk_atom sym ts = Atom (mk_app ~srt:Bool sym ts)

let mk_pred id ts = mk_atom (FreeSym id) ts

let mk_eq s t = mk_atom Eq [s; t]

let mk_null = mk_app ~srt:Loc Null []

let mk_select fld ind = 
  let srt = match sort_of fld with
  | Some (Fld s) -> Some s
  | _ -> None
  in mk_app ?srt:srt Select [fld; ind]

let mk_store fld ind upd =
  mk_app ?srt:(sort_of fld) Store [fld; ind; upd]

let mk_ep fld set t = mk_app ~srt:Loc EntPnt [fld; set; t]

let mk_reachwo fld t1 t2 t3 =
  mk_atom ReachWO [fld; t1; t2; t3]
  
let mk_reach fld t1 t2 = mk_reachwo fld t1 t2 t2

let mk_empty srt = mk_app ?srt:srt Empty []

let mk_inter sets = mk_app ?srt:(sort_ofs sets) Inter sets

let mk_union sets = mk_app ?srt:(sort_ofs sets) Union sets

let mk_diff s t = mk_app ?srt:(sort_of s) Diff [s; t]

let mk_elem e s = mk_atom Elem [e; s]

let mk_subseteq s t = mk_atom SubsetEq [s; t]

let mk_true = BoolOp (And, [])
let mk_false = BoolOp (Or, [])

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

let mk_equiv a b =
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

(** Computes the set of ground terms appearing in f
 * free variables are treated as implicitly universally quantified *)
let ground_terms f =
  let rec gt bv terms t = 
    match t with
    | Var (id, _) -> terms, false
    | App (_, ts, _) ->
	let terms1, is_ground = 
	  List.fold_left 
	    (fun (terms, is_ground) t ->
	      let terms_t, is_ground_t = gt bv terms t in
	      terms_t, is_ground && is_ground_t)
	    (terms, true) ts
	in
	if is_ground 
	then TermSet.add t terms, true 
	else terms, false
  in 
  fold_terms_with_bound 
    (fun bv acc t -> fst (gt bv acc t)) 
    TermSet.empty f
  
let vars_in_fun_terms f =
  let rec fvt vars = function
    | Var (id, _) -> IdSet.add id vars
    | App (_, ts, _) ->
	List.fold_left fvt vars ts
  in
  let rec ct vars t = 
    match t with
    | App (_, ts, Some Bool) -> 
	List.fold_left ct vars ts
    | App _ -> fvt vars t
    | _ -> vars
  in fold_terms ct IdSet.empty f
     
(** Extracts the signature of f *)
let sign f : signature =
  let fail () = failwith "tried to extract signature from untyped formula" in
  let rec signt (decls : signature) = function
    | Var _ -> decls
    | App (sym, args, res_srt_opt) ->
	let res_srt = 
	  match res_srt_opt with
	  | Some srt -> srt
	  | None -> fail ()
	in
	let arg_srts = 
	  List.map
	    (function 
	      |	Var (_, Some srt) 
	      | App (_, _, Some srt) -> srt 
	      | _ -> fail ()
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

(** Pretty printing *)

open Format

let str_of_ident (name, n) =
  if n = 0 then name else
  Printf.sprintf "%s_%d" name n

let str_of_symbol = function
  (* function symbols *)
  | Null -> "null"
  | Select -> "select"
  | Store -> "store"
  | EntPnt -> "ep"
  | Empty -> "{}"
  | Union -> "+"
  | Inter -> "&"
  | Diff -> "-"
  (* predicate symbols *)
  | Eq -> "="
  | ReachWO -> "ReachWO"
  | Elem -> ":"
  | SubsetEq -> "<="
  (* free symbols *)
  | FreeSym id -> str_of_ident id

let pr_ident ppf (name, n) = fprintf ppf "%s_%d" name n

let pr_sym ppf sym = fprintf ppf "%s" (str_of_symbol sym)


let rec pr_term ppf = function
  | Var (id, _) -> fprintf ppf "%a" pr_ident id
  | App (sym, [], _) -> fprintf ppf "%a" pr_sym sym
  | App (sym, ts, _) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts

and pr_terms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_term t
  | t :: ts -> fprintf ppf "%a@ %a" pr_term t pr_terms ts
      
let pr_binder ppf b =
  let b_str = match b with
  | Forall -> "forall"
  | Exists -> "exists"
  in 
  fprintf ppf "%s" b_str

let pr_boolop ppf op =
  let op_str = match op with
  | And -> "and"
  | Or -> "or"
  | Not -> "not"
  in 
  fprintf ppf "%s" op_str

let loc_sort_string = "Loc"
let fld_sort_string = "Fld"
let set_sort_string = "Set"
let bool_sort_string = "Bool"

let rec pr_sort0 ppf srt = match srt with
  | Loc | Bool -> fprintf ppf "%a" pr_sort srt
  | _ -> fprintf ppf "@[<1>(%a)@]" pr_sort srt

and pr_sort ppf = function
  | Loc -> fprintf ppf "%s" loc_sort_string
  | Bool -> fprintf ppf "%s" bool_sort_string
  | Fld s -> fprintf ppf "@[<4>%s@ %a@]" fld_sort_string pr_sort0 s
  | Set s -> fprintf ppf "@[<4>%s@ %a@]" set_sort_string pr_sort0 s
		
let pr_var ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_sort srt

let rec pr_vars ppf = function
  | [] -> ()
  | [v] -> fprintf ppf "%a" pr_var v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var v pr_vars vs

let extract_comments ann =
  let cmnts = Util.filter_map 
      (function Comment _ -> true (*| _ -> false*)) 
      (function Comment c -> c (*| _ -> ""*)) 
      ann 
  in
  String.concat "_" cmnts

let rec pr_form ppf = function
  | Binder (b, vs, f, a) -> 
      let cmnts = extract_comments a in
      (match cmnts with
      |	"" -> fprintf ppf "%a" pr_quantifier (b, vs, f)
      |	c -> fprintf ppf "@[<2>(!%a@ :named@ %s)@]" pr_quantifier (b, vs, f) c)
  | Atom t -> fprintf ppf "%a" pr_term t
  | BoolOp (And, []) -> fprintf ppf "%s" "true"
  | BoolOp (Or, []) -> fprintf ppf "%s" "false"
  | BoolOp (op, fs) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_boolop op pr_forms fs

and pr_quantifier ppf = function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> fprintf ppf "@[<2>(%a@ @[<1>(%a)@]@ %a)" pr_binder b pr_vars vs pr_form f


and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts

let print_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t
let print_form out_ch f = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_form f

let print_smtlib_sort out_ch s = pr_sort (formatter_of_out_channel out_ch) s
let print_smtlib_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t
let print_smtlib_form out_ch f =  fprintf (formatter_of_out_channel out_ch) "%a@?" pr_form f

let string_of_sort s = pr_sort0 str_formatter s; flush_str_formatter ()
let string_of_term t = pr_term str_formatter t; flush_str_formatter ()
let string_of_form f = pr_form str_formatter f; flush_str_formatter ()

(*

let string_of_term t = 
  let rec st = function
    | Const id 
    | Var id -> str_of_ident id
    | FunApp (id, ts) ->
	let str_ts = List.map st ts in
	str_of_ident id ^ "(" ^ 
	String.concat ", " str_ts ^
	")"
  in st t

let rec string_of_form f = match f with
    | And lst -> "(" ^ (String.concat ") && (" (List.map string_of_form lst)) ^ ")"
    | Or lst -> "(" ^ (String.concat ") || (" (List.map string_of_form lst)) ^ ")"
    | Eq (s, t) -> (string_of_term s) ^ " = " ^ (string_of_term t)
    | Not (Eq (s, t)) -> (string_of_term s) ^ " ~= " ^ (string_of_term t)
    | Not f -> "~ " ^ (string_of_form f)
    | Comment (c, f) -> string_of_form f
    | Pred (p, ts) -> (str_of_ident p) ^ "(" ^ (String.concat ", " (List.map string_of_term ts)) ^ ")"
    | BoolConst b -> if b then "true" else "false" 

let print_form out_ch =
  let print = output_string out_ch in
  let print_list indent delim p = function
    | [] -> ()
    | x :: xs ->
	p "" "" x;
	List.iter (p indent delim) xs 
  in
  let rec pt indent delim = function
    | Const id 
    | Var id -> 
	print (indent ^ delim ^ str_of_ident id)
    | FunApp (id, ts) ->
	print (indent ^ delim ^ str_of_ident id ^ "(");
	print_list "" ", " pt ts;
	print ")"
  in
  let rec pf indent delim = function
    | And fs ->
	print indent;
	print delim;
	print "( ";
	print_list (indent ^ "  ") "& " (fun indent delim f -> pf indent delim f; print "\n") fs;
	print (indent ^ "  )");
    | Or fs ->
	print indent;
	print delim;
	print "( ";
	print_list (indent ^ "  ") "| " (fun indent delim f -> pf indent delim f; print "\n") fs;
	print (indent ^ "  )");
    | Not (Eq (s, t)) ->
	print indent;
	print delim;
	print_list "" " ~= " pt [s;t]
    | Not f ->
	print (indent ^ delim ^ "~");  
	print_list (indent ^ " ") "" pf [f]
    | Comment (c, f) ->
	pf indent delim f
    | Pred (p, ts) ->
	print (indent ^ delim ^ str_of_ident p ^ "(");
	print_list "" ", " pt ts;
	print ")";
    | Eq (s, t) ->
	print indent;
	print delim;
	print_list "" " = " pt [s;t]
    | BoolConst b ->
	print indent;
	print delim;
	if b then print "True" else print "False" 
  in function
    | And fs 
    | Comment (_, And fs) ->
	print "  ";
	print_list "" "& " (fun indent delim f -> pf indent delim f; print "\n") fs;
    | Or fs 
    | Comment (_, Or fs) ->
	print "  ";
	print_list "" "| " (fun indent delim f -> pf indent delim f; print "\n") fs;
    | f -> pf "" "" f; print "\n"
  

let print_smtlib_term out_ch t =
  let print = output_string out_ch in
  let print_list fn xs = List.iter (fun x -> fn x; print " ") xs in
  let rec smt_term = function
    | Const id 
    | Var id -> print (str_of_ident id)
    | FunApp (id, ts) ->
	print "(";
	print (str_of_ident id);
	print " ";
	print_list smt_term ts;
	print ")"
  in
    smt_term t

let print_smtlib_form_generic before_f after_f out_ch f =
  let print = output_string out_ch in
  let print_list fn xs = List.iter (fun x -> fn x; print " ") xs in
  let rec smt_form = function
  | And fs -> 
      print "(and ";
      print_list smt_form fs;
      print ")"
  | Or fs -> 
      print "(or ";
      print_list smt_form fs;
      print ")"
  | Not f -> 
      print "(not ";
      smt_form f;
      print ")";
  | Comment (c, f) ->
      smt_form f
  | Pred (id, ts) -> 
      if (ts = []) then
        print (" " ^ (str_of_ident id))
      else
        begin
          print "(";
          print (str_of_ident id);
          print " ";
          print_list (print_smtlib_term out_ch) ts;
          print ")"
        end
  | Eq (s, t) -> 
      print "(= ";
      print_list (print_smtlib_term out_ch) [s; t];
      print ")"
  | BoolConst b -> if b then print " true" else print " false"
  in 
  before_f out_ch f;
  smt_form f;
  after_f out_ch f

let print_smtlib_form out_ch f =
  let before_quantify out_ch f =
    let print = output_string out_ch in
    let vars = fv f in
    if not (IdSet.is_empty vars) then print "(forall (";
    IdSet.iter (fun id -> print ("(" ^ str_of_ident id ^ " " ^ sort_str ^ ") ")) vars;
    if not (IdSet.is_empty vars) then print ")"
  in
  let after_quantify out_ch f =
    let print = output_string out_ch in
    let vars = fv f in
    if not (IdSet.is_empty vars) then print ")"
  in
    print_smtlib_form_generic before_quantify after_quantify out_ch f

let print_smtlib_form_with_triggers out_ch f =
  let vars = fv f in
  let triggers = 
    let with_vars =
      if !Config.use_triggers then
        begin
          let rec has_var t = match t with 
            | Var _ -> true
            | Const _ -> false
            | FunApp (_, ts) -> List.exists has_var ts
          in
          let rec get acc t =
            if has_var t then TermSet.add t acc
            else acc
          in
            collect_from_terms get TermSet.empty f
        end
      else
        IdSet.fold (fun id acc -> TermSet.add (mk_var id) acc) vars TermSet.empty
    in
      TermSet.filter (fun t -> match t with Var _ -> false | _ -> true) with_vars
  in
  let before_quantify out_ch f =
    let print = output_string out_ch in
    if not (IdSet.is_empty vars) then
       begin
         print "(forall (";
         IdSet.iter (fun id -> print ("(" ^ str_of_ident id ^ " " ^ sort_str ^ ") ")) vars;
         print ") (!";
       end
  in
  let after_quantify out_ch f =
    let print = output_string out_ch in
    let print_list fn xs = List.iter (fun x -> fn x; print " ") xs in
      if not (TermSet.is_empty triggers) then
        begin
          print ":pattern (";
          print_list (print_smtlib_term out_ch) (TermSet.elements triggers);
          print ")))"
        end
      else if not (IdSet.is_empty vars) then
        print "))"
  in
    print_smtlib_form_generic before_quantify after_quantify out_ch f
      

let print_forms ch = function
  | f :: fs -> 
      print_form ch f;
      List.iter (fun f -> output_string ch ";\n"; print_form ch f) fs;
  | [] -> ()

*)

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


