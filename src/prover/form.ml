open Util

(** Sorts and signatures *)

type ident = string * int

type simpleSort =
  | Bool | Loc | LocSet | Fld

type sort = simpleSort list * simpleSort

type symbol =
  (* function symbols *)
  | Null | Sel | Upd 
  | Empty | Union | Inter | Diff
  | Fun of ident
  (* predicate symbols *)
  | FldEq
  | LocEq | ReachWO
  | Elem | SubsetEq | SetEq 
  | Pred of ident

module SymbolMap = Map.Make(struct
    type t = symbol
    let compare = compare
  end)

type signature = sort SymbolMap.t

let base_sig =
  let decls =
    [(* function symbols *)
     (Null, ([], Loc));
     (Sel, ([Fld; Loc], Loc));
     (Upd, ([Fld; Loc; Loc], Fld));
     (Empty, ([], LocSet));
     (Union, ([LocSet; LocSet], LocSet));
     (Inter, ([LocSet; LocSet], LocSet));
     (Diff, ([LocSet; LocSet], LocSet));
     (* predicate symbols *)
     (FldEq, ([Fld; Fld], Bool));
     (LocEq, ([Loc; Loc], Bool));
     (ReachWO, ([Fld; Loc; Loc; Loc], Bool));
     (Elem, ([Loc; LocSet], Bool));
     (SubsetEq, ([LocSet; LocSet], Bool));
     (SetEq, ([LocSet; LocSet], Bool))]
  in
  List.fold_left 
    (fun acc (sym, srt) -> SymbolMap.add sym srt acc)
    SymbolMap.empty decls 


(* Terms and formulas *)

type boolOp =
  | And | Or | Not

type annot =
  | Comment of string

type binder =
  | Forall | Exists

type term =
  | Var of ident
  | FunApp of symbol * term list

type form =
  | Atom of symbol * term list
  | BoolOp of boolOp * form list
  | Binder of binder * (ident * simpleSort) list * form
  | Annot of annot * form  

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
  | Not -> Not
  
let dualize_binder = function
  | Forall -> Exists
  | Exists -> Forall

let is_pred_id id = String.capitalize (fst id) = fst id

let name id = fst id

let eq_name id1 id2 = name id1 = name id2

let mk_ident name = (name, 0)

let mk_const id = FunApp (Fun id, [])
let mk_var id = Var id
let mk_app sym ts = FunApp (sym, ts) 

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

let mk_eq eq s t = Atom (eq, [s; t])

let mk_LocEq s t = mk_eq LocEq s t
let mk_FldEq s t = mk_eq FldEq s t
let mk_SetEq s t = mk_eq SetEq s t

let mk_pred id ts = Atom (Pred id, ts)

let mk_comment c = function
  | Annot (Comment c', f) -> 
      Annot (Comment (c ^ "_" ^ c'), f)
  | f -> Annot (Comment c, f)

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

type subst_map = term IdMap.t

let form_set_of_list fs =
  List.fold_left 
    (fun acc f -> FormSet.add f acc) 
    FormSet.empty fs

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
  | BoolOp (Not, [Binder (b, xs, f)]) -> 
      Binder (dualize_binder b, xs, nnf (mk_not f))
  | BoolOp (Not, [Annot (a, f)]) -> 
      Annot (a, nnf (mk_not f))
  | BoolOp (op, fs) -> smk_op op (List.map nnf fs)
  | Binder (b, vs, f) -> Binder (b, vs, nnf f)
  | Annot (a, f) -> Annot (a, nnf f)
  | f -> f
  
let mk_neq eq s t = mk_not (mk_eq eq s t)

let mk_implies a b =
  smk_or [nnf (mk_not a); b]

let mk_equiv a b =
  smk_or [smk_and [a; b]; smk_and [nnf (mk_not a); nnf (mk_not b)]]

let fold_terms fn init f =
  let rec ft acc = function
    | Atom (_, ts) -> List.fold_left fn acc ts
    | BoolOp (_, fs) ->	List.fold_left ft acc fs
    | Binder (b, vs, f) -> ft acc f
    | Annot (a, f) -> ft acc f
  in ft init f

let fold_terms_with_bound fn init f =
  let rec ft bv acc = function
    | Atom (_, ts) -> List.fold_left (fn bv) acc ts
    | BoolOp (_, fs) ->	List.fold_left (ft bv) acc fs
    | Binder (b, vs, f) -> 
	ft (List.fold_left (fun bv (x, _) -> IdSet.add x bv) bv vs) acc f
    | Annot (a, f) -> ft bv acc f
  in ft IdSet.empty init f

let fvt vars t =
  let rec fvt1 vars = function
  | Var id -> IdSet.add id vars
  | FunApp (_, ts) -> List.fold_left fvt1 vars ts
  in fvt1 vars t

let fv f = 
  let rec fvt bv vars = function
    | Var id -> 
	if IdSet.mem id bv 
	then vars 
	else IdSet.add id vars
    | FunApp (_, ts) ->
	List.fold_left (fvt bv) vars ts
  in fold_terms_with_bound fvt IdSet.empty f

(* free variables are treated as implicitly universally quantified *)
let ground_terms f =
  let rec gt bv terms t = 
    match t with
    | Var id -> terms, false
    | FunApp (_, ts) ->
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
    | Var id -> IdSet.add id vars
    | FunApp (_, ts) ->
	List.fold_left fvt vars ts
  in
  let rec ct vars t = 
    match t with
    | FunApp _ -> fvt vars t
    | _ -> vars
  in fold_terms ct IdSet.empty f
     

(*
let sign f : signature =
  let rec fts decls = function
    | Var id -> decls
    | FunApp (sym, ts) ->
	let arity = List.length ts in
	List.fold_left fts (SymbolMap.add (FunSym sym) arity decls) ts
  in 
  let rec ffs decls = function
    | BoolOp (op, fs) ->
	List.fold_left ffs decls fs
    | Atom (sym, ts) ->
	let arity = List.length ts in
	List.fold_left fts (SymbolMap.add (PredSym sym) arity decls) ts
    | Annot (_, f)
    | Binder (_, _, f) -> ffs decls f
  in
  ffs SymbolMap.empty f


let funs_in_term t =
  let rec fts funs = function
    | Var _ -> funs
    | FunApp (sym, ts) ->
	let arity = List.length ts in
	List.fold_left fts (FunSymbolMap.add sym arity funs) ts
  in fts FunSymbolMap.empty t

let funs f =
  let rec fts funs = function
    | Var _ -> funs
    | FunApp (sym, ts) ->
	let arity = List.length ts in
	List.fold_left fts (FunSymbolMap.add sym arity funs) ts
  in fold_terms fts FunSymbolMap.empty f

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

(* Substitute all identifiers in term t according to substitution map subst_map *)
let subst_id_term subst_map t =
  let sub_id id =
    try IdMap.find id subst_map with Not_found -> id
  in
  let rec sub = function
    | Var id -> Var (sub_id id)
    | FunApp (sym, ts) -> 
	let sym1 = match sym with
	| Fun id -> Fun (sub_id id)
	| _ -> sym
	in
	FunApp (sym1, List.map sub ts)
  in sub t

(* Substitute all identifiers in formula f according to substitution map subst_map *)
(* Not capture avoiding *)
let subst_id subst_map f =
  let sub_id id =
    try IdMap.find id subst_map with Not_found -> id
  in
  let subt = subst_id_term subst_map in
  let rec sub = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map sub fs)
    | Atom (sym, ts) -> 
	let sym1 = match sym with
	| Pred id -> Pred (sub_id id)
	| _ -> sym
	in
	Atom (sym1, List.map subt ts)
    | Binder (b, vs, f) -> Binder (b, vs, sub f)
    | Annot (a, f) -> Annot (a, sub f)
  in sub f

(* Substitute all variables in formula f according to substitution map subst_map *)
let subst_term subst_map t =
  let sub_id id t =
    try IdMap.find id subst_map with Not_found -> t
  in
  let rec sub = function
    | (Var id as t) -> sub_id id t 
    | FunApp (sym, ts) -> FunApp (sym, List.map sub ts)
  in sub t

(* Substitute all free variables in formula f according to substitution map subst_map *)
(* Capture avoiding *)
let subst subst_map f =
  let rec sub sm = function 
    | BoolOp (op, fs) -> BoolOp (op, List.map (sub sm) fs)
    | Atom (sym, ts) -> Atom (sym, List.map (subst_term sm) ts)
    | Binder (b, vs, f) ->
	let not_bound id _ = not (List.mem_assoc id vs) in
	let sm1 = IdMap.filter not_bound sm in 
	let occuring = IdMap.fold (fun _ t acc -> fvt acc t) sm IdSet.empty in
	let vs1, sm2 = 
	  List.fold_right 
	    (fun (x, srt) (vs1, sm2) ->
	      if IdSet.mem x occuring 
	      then 
		let x1 = fresh_ident (name x) in
		(x1, srt) :: vs1, IdMap.add x (Var x1) sm2
	      else (x, srt) :: vs1, sm2)
	    vs ([], sm1)
	in Binder (b, vs1, sub sm2 f)
    | Annot (a, f) -> Annot (a, sub sm f)
  in sub subst_map f

(** Pretty printing *)

open Format

let str_of_ident (name, n) =
  if n = 0 then name else
  Printf.sprintf "%s_%d" name n

let pr_ident ppf (name, n) = fprintf ppf "%s_%d" name n


let pr_sym ppf sym =
  let sym_str = match sym with
  (* function symbols *)
  | Null -> "null"
  | Sel -> "sel"
  | Upd -> "upd"
  | Empty -> "{}"
  | Union -> "+"
  | Inter -> "&"
  | Diff -> "-"
  | Fun id -> str_of_ident id
  (* predicate symbols *)
  | FldEq -> "="
  | LocEq -> "="
  | ReachWO -> "ReachWO"
  | Elem -> ":"
  | SubsetEq -> "<="
  | SetEq -> "="
  | Pred id -> str_of_ident id
  in
  fprintf ppf "%s" sym_str


let rec pr_term ppf = function
  | Var id -> fprintf ppf "%a" pr_ident id
  | FunApp (sym, []) -> fprintf ppf "%a" pr_sym sym
  | FunApp (sym, ts) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts

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

let pr_simple_sort ppf srt =
  let srt_str = match srt with
  | Fld -> "Fld"
  | Loc -> "Loc"
  | LocSet -> "LocSet"
  | Bool -> "Bool"
  in fprintf ppf "%s" srt_str
      

let pr_var ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_simple_sort srt

let rec pr_vars ppf = function
  | [] -> ()
  | [v] -> fprintf ppf "%a" pr_var v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var v pr_vars vs

let rec pr_form ppf = function
  | Binder (b, vs, f) -> fprintf ppf "@[<2>(%a@ @[<1>(%a)@]@ %a)" pr_binder b pr_vars vs pr_form f
  | Atom (sym, []) -> fprintf ppf "%a" pr_sym sym 
  | Atom (sym, ts) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts
  | Annot (Comment c, f) -> fprintf ppf "@[<2>(!@ %a:named@ %s)@]" pr_form f c
  | BoolOp (And, []) -> fprintf ppf "%s" "true"
  | BoolOp (Or, []) -> fprintf ppf "%s" "false"
  | BoolOp (op, fs) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_boolop op pr_forms fs

and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts

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
      |	Annot (a, BoolOp (Or fs)) -> List.map (fun f -> Annot (a, f)) fs
      | f -> [f]
    in
    match nf with
    | BoolOp (And, fs) -> List.map to_clause fs
    | Annot (a, BoolOp (And, fs)) -> List.map (fun f -> to_clause (Annot (a, f))) fs
    | f -> [to_clause f]
	  
  (** convert a set of clauses into a formula *)
  let to_form cs = smk_and (List.map smk_or cs)

end


