open Util

type ident = string * int

type term =
  | Const of ident
  | Var of ident
  | FunApp of ident * term list

type form =
  | BoolConst of bool
  | Pred of ident * term list
  | Eq of term * term
  | Not of form
  | And of form list
  | Or of form list
  
let fresh_ident =
  let used_names = Hashtbl.create 0 in
  fun (name : string) ->
    let last_index = 
      try Hashtbl.find used_names name 
      with Not_found -> -1
    in 
    Hashtbl.replace used_names name (last_index + 1);
    (name, last_index + 1)

let sort_str = "usort"

let str_of_ident (id, n) =
  Printf.sprintf "%s_%d" id n

let is_pred_id id = String.capitalize (fst id) = fst id

let mk_ident id = (id, 0)

let mk_const id = Const id
let mk_var id = Var id
let mk_app id ts = FunApp (id, ts) 

let mk_true = BoolConst true
let mk_false = BoolConst false
let mk_and = function
  | [] -> mk_true
  | [f] -> f
  | fs -> And fs
let mk_or fs = Or fs
let mk_not = function
  | BoolConst b -> BoolConst (not b)
  | f -> Not f
let mk_eq s t = Eq (s, t)
let mk_pred id ts = Pred (id, ts)

let str_true = "True"
let str_false = "False"

let id_true = mk_ident str_true
let id_false = mk_ident str_false

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

let id_set_to_list ids = 
  IdSet.fold (fun v acc -> v :: acc) ids []

let form_set_to_list fs =
  FormSet.fold (fun f acc -> f :: acc) fs []

let form_set_of_list fs =
  List.fold_left (fun acc f -> FormSet.add f acc) FormSet.empty fs

let smk_and fs = 
  let rec mkand1 fs acc = 
    match fs with
    | [] ->
        begin
          match form_set_to_list acc with
	  | [] -> BoolConst true
	  | [f] -> f
	  | fs -> mk_and fs
        end
    | And fs0 :: fs1 -> mkand1 (fs0 @ fs1) acc
    | BoolConst true :: fs1 -> mkand1 fs1 acc
    | BoolConst false :: fs1 -> BoolConst false
    | f::fs1 -> mkand1 fs1 (FormSet.add f acc)
  in mkand1 fs FormSet.empty

let smk_or fs = 
  let rec mkor1 fs acc = 
    match fs with
    | [] ->
        begin
          match form_set_to_list acc with
	  | [] -> BoolConst false
	  | [f] -> f
	  | fs -> mk_or fs
        end
    | Or fs0 :: fs1 -> mkor1 (fs0 @ fs1) acc
    | BoolConst false :: fs1 -> mkor1 fs1 acc
    | BoolConst true :: fs1 -> BoolConst true
    | f::fs1 -> mkor1 fs1 (FormSet.add f acc)
  in mkor1 fs FormSet.empty

(** compute negation normal form of a formula *)
let rec nnf = function
  | Not (BoolConst b) -> BoolConst (not b)
  | Not (Not f) -> nnf f
  | Not (And fs) -> smk_or (List.map (fun f -> nnf (mk_not f)) fs)
  | Not (Or fs) -> smk_and (List.map (fun f -> nnf (mk_not f)) fs)
  | And fs -> smk_and (List.map nnf fs)
  | Or fs -> smk_or (List.map nnf fs)
  | f -> f
  

(** compute conjunctive normal form of a formula *)
(* Todo: avoid exponential blowup *)
let rec cnf = 
  let rec cnf_and acc = function
    | [] ->
	begin
	  match acc with
	  | [] -> BoolConst true
	  | [f] -> f
	  | fs -> mk_and fs
	end
    | And fs :: fs1 -> cnf_and acc (fs @ fs1)
    | BoolConst false :: _ -> BoolConst false
    | BoolConst true :: fs -> cnf_and acc fs
    | f :: fs -> cnf_and (f :: acc) fs
  in
  let rec cnf_or acc = function
    | [] ->
	begin
	  match acc with
	  | [] -> BoolConst false
	  | [f] -> f
	  | fs -> mk_or fs
	end
    | Or fs :: fs1 -> cnf_or acc (fs @ fs1)
    | And fs :: fs1 -> 
	let fs_or = acc @ fs1 in
	let fs_and = List.map (fun f -> Or (f :: fs_or)) fs in
	cnf (And fs_and)
    | BoolConst true :: _ -> BoolConst true
    | BoolConst false :: fs -> cnf_or acc fs
    | f :: fs -> cnf_or (f :: acc) fs  
  in
  function
    | And fs ->  cnf_and [] (List.rev_map cnf fs)
    | Or fs -> cnf_or [] (List.rev_map cnf fs)
    | f -> f

let collect_from_terms col init f =
  let rec ct acc = function
    | And fs 
    | Or fs ->
	List.fold_left ct acc fs
    | Not f -> ct acc f
    | Pred (_, ts) ->
	List.fold_left col acc ts
    | Eq (s, t) -> col (col acc s) t
    | _ -> acc
  in ct init f

let fv f = 
  let rec fvt vars = function
    | Var id -> IdSet.add id vars
    | FunApp (_, ts) ->
	List.fold_left fvt vars ts
    | _ -> vars
  in collect_from_terms fvt IdSet.empty f


let ground_terms f =
  let rec gt terms t = 
    match t with
    | Var _ -> terms, false
    | Const _ -> TermSet.add t terms, true
    | FunApp (_, ts) ->
	let terms1, is_ground = 
	  List.fold_left 
	    (fun (terms, is_ground) t ->
	      let terms_t, is_ground_t = gt terms t in
	      terms_t, is_ground && is_ground_t)
	    (terms, true) ts
	in
	if is_ground then TermSet.add t terms, true else terms, false
  in collect_from_terms (fun acc t -> fst (gt acc t)) TermSet.empty f
  

type decl = {is_pred: bool; arity: int}

let sign f =
  let rec fts decls = function
    | Var _ -> decls
    | Const id -> IdMap.add id {is_pred = false; arity = 0} decls
    | FunApp (id, ts) ->
	let decl = {is_pred = false; arity = List.length ts} in
	List.fold_left fts (IdMap.add id decl decls) ts
  in 
  let rec ffs decls = function
    | And fs 
    | Or fs ->
	List.fold_left ffs decls fs
    | Not f -> ffs decls f
    | Pred (id, ts) ->
	let decl = {is_pred = true; arity = List.length ts} in
	List.fold_left fts (IdMap.add id decl decls) ts
    | Eq (s, t) -> fts (fts decls s) t
    | _ -> decls
  in
  ffs IdMap.empty f


let funs_in_term t =
  let rec fts funs = function
    | Var _ -> funs
    | Const id -> IdSet.add id funs
    | FunApp (id, ts) ->
	List.fold_left fts (IdSet.add id funs) ts
  in fts IdSet.empty t

let funs f =
  let rec fts funs = function
    | Var _ -> funs
    | Const id -> IdSet.add id funs
    | FunApp (id, ts) ->
	List.fold_left fts (IdSet.add id funs) ts
  in collect_from_terms fts IdSet.empty f

let subst_id_term subst_map t =
  let sub_id id =
    try IdMap.find id subst_map with Not_found -> id
  in
  let rec sub = function
    | Const id -> Const  (sub_id id)
    | Var id -> Var (sub_id id)
    | FunApp (id, ts) -> FunApp (sub_id id, List.map sub ts)
  in sub t

let subst_id subst_map f =
  let sub_id id =
    try IdMap.find id subst_map with Not_found -> id
  in
  let subt = subst_id_term subst_map in
  let rec sub = function 
    | And fs -> And (List.map sub fs)
    | Or fs -> Or (List.map sub fs)
    | Not g -> Not (sub g)
    | Eq (s, t) -> Eq (subt s, subt t)
    | Pred (id, ts) -> Pred (sub_id id, List.map subt ts)
    | f -> f
  in sub f

let subst_term subst_map t =
  let sub_id id t =
    try IdMap.find id subst_map with Not_found -> t
  in
  let rec sub = function
    | (Const id as t)
    | (Var id as t) -> sub_id id t 
    | FunApp (id, ts) -> FunApp (id, List.map sub ts)
  in sub t

let subst subst_map f =
  let subt = subst_term subst_map in
  let rec sub = function 
    | And fs -> And (List.map sub fs)
    | Or fs -> Or (List.map sub fs)
    | Not g -> Not (sub g)
    | Eq (s, t) -> Eq (subt s, subt t)
    | Pred (id, ts) -> Pred (id, List.map subt ts)
    | f -> f
  in sub f

let string_of_term t = 
  let rec st = function
    | Const id 
    | Var id -> str_of_ident id
    | FunApp (id, ts) ->
	let str_ts = List.map st ts in
	str_of_ident id ^ " [" ^ 
	String.concat " " str_ts ^
	"]"
  in st t

let print_form out_ch =
  let print = output_string out_ch in
  let print_list indent p = function
    | [] -> ()
    | x :: xs ->
	p "" x;
	List.iter (p indent) xs 
  in
  let rec pt indent = function
    | Const id 
    | Var id -> 
	print (indent ^ str_of_ident id)
    | FunApp (id, ts) ->
	print (indent ^ str_of_ident id ^ " [");
	print_list " " pt ts;
	print "]"
  in
  let rec pf indent = function
    | And fs ->
	print (indent ^ "& [");
	print_list " " pf fs;
	print "]"
    | Or fs ->
      print (indent ^ "| [");
	print_list " " pf fs;
      print "]"
    | Not f ->
	print (indent ^ "~");  
	pf "" f
    | Pred (p, ts) ->
	print (indent ^ "= " ^ str_of_ident p ^ " [");
	print_list " " pt ts;
	print "] ";
	pt "" (mk_const id_true)
    | Eq (s, t) ->
	print (indent ^ "= ");
	print_list " " pt [s;t];
    | BoolConst b ->
	if b then pf indent (mk_eq (mk_const id_true) (mk_const id_true))
	else pf indent (mk_not (mk_eq (mk_const id_true) (mk_const id_true)))
  in function
    | And fs ->
	print "& [";
	print_list "\n   " pf fs;
	print "\n]\n"
    | Or fs ->
	print "| [";
	print_list "\n   " pf fs;
	print "\n]\n"
    | f -> pf "" f; print "\n"
  

let print_smtlib_form out_ch f =
  let print = output_string out_ch in
  let print_list fn xs = List.iter (fun x -> fn x; print " ") xs in
  let rec smt_term = function
    | Const id 
    | Var id -> print (str_of_ident id)
    | FunApp (id, ts) ->
	print ("(" ^ str_of_ident id ^ " ");
	print_list smt_term ts;
	print ")"
  in
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
  | Pred (id, ts) -> 
      print ("(" ^ str_of_ident id ^ " ");
      print_list smt_term ts;
      print ")" 
  | Eq (s, t) -> 
      print "(= ";
      print_list smt_term [s; t];
      print ")"
  | BoolConst b -> if b then print "true" else print "false"
  in 
  let vars = fv f in
  if not (IdSet.is_empty vars) then print "(forall ";
  IdSet.iter (fun id -> print ("(" ^ str_of_ident id ^ " " ^ sort_str ^ ") ")) vars;
  smt_form f;
  if not (IdSet.is_empty vars) then print ")"
      

let print_forms ch = function
  | f :: fs -> 
      print_form ch f;
      List.iter (fun f -> output_string ch ";\n"; print_form ch f) fs;
  | [] -> ()

module Clauses = struct

  type clause = form list
  type clauses = clause list
       
  (** convert a formula into a set of clauses *)
  let from_form f : clauses = 
    let nf = cnf (nnf f) in
    let to_clause = function
      | Or fs -> fs
      | BoolConst false -> []
      | f -> [f]
    in
    match nf with
    | And fs -> List.map to_clause fs
    | BoolConst true -> []
    | f -> [to_clause f]
	  
  (** convert a set of clauses into a formula *)
  let to_form cs = smk_and (List.map smk_or cs)

end

module Model = struct
  type output_sort = 
      Int of int 
    | Bool of bool

  type def = { input : int list;
	       output : output_sort}
  type model = def list IdMap.t
  
  let empty : model = IdMap.empty

  let add_def id (i, o) model = 
    let defs = 
      try IdMap.find id model
      with Not_found -> []
    in
    IdMap.add id ({input=i; output=o} :: defs) model 

  let filter_defs p model =
    IdMap.fold 
      (fun id defs fmodel ->
	match List.filter (p id) defs with
	| [] -> fmodel
	| fdefs -> IdMap.add id defs fmodel)
      model IdMap.empty

  let fold f model init = 
    IdMap.fold 
      (fun id defs acc ->
	List.fold_left (fun acc def -> f id def acc) acc defs)
      model init

  let const_map m =
    let consts = 
      IdMap.fold 
	(fun id defs acc ->
	  match defs with
	  | [def] when def.input = [] -> 
	      (match def.output with
	      |	Int o -> IntMap.add o id acc
	      |	_ -> acc)
	  | _ -> acc)
	m IntMap.empty
    in
    IdMap.fold 
      (fun id defs acc ->
	List.fold_left (fun acc def ->
	  List.fold_left (fun acc i ->
	    if IntMap.mem i acc then acc
	    else IntMap.add i (fresh_ident "c") acc)
	    acc def.input)
	  acc defs)
      m consts
      
  let to_clauses model =
    let const_map = const_map model in 
    let mk_rep n = mk_const (IntMap.find n const_map) in
    let constants = IntMap.fold (fun n _ acc -> mk_rep n :: acc) const_map [] in
    let form_of_def id def = 
      match def.output with
      |	Bool b -> 
	  let a = mk_pred id (List.map mk_rep def.input) in
	  if b then a else mk_not a
      |	Int out ->
	  let rhs = mk_rep out in
	  let lhs =
	    match def.input with
	    | [] -> mk_const id
	    | reps -> mk_app id (List.map mk_rep reps)
	  in mk_eq lhs rhs
    in
    let def_forms =
      IdMap.fold 
	(fun id defs acc ->
	  List.fold_left (fun acc def -> form_of_def id def :: acc) acc defs)
	model []
    in
    let diseqs = List.fold_left (fun acc c1 -> 
      List.fold_left (fun acc c2 ->
	if c1 = c2 then acc else [mk_not (mk_eq c1 c2)] :: acc) acc constants) 
	[] constants
    in
    diseqs @ List.map (fun f -> [f]) def_forms

  let to_form model = Clauses.to_form (to_clauses model)

  let print_model model =
    print_form stdout (to_form model)

  let print_model2 model =
    IdMap.iter
      (fun id defs ->
	print_string (str_of_ident id ^ " = ");
	match defs with
	| [def] when List.length def.input = 0 -> 
	    (match def.output with
	      |	Int out -> Printf.printf " -> %d\n" out
	      |	Bool out -> Printf.printf " -> %b\n" out)
	| _ ->
	    print_string "\n  [";
	    List.iter (fun def -> 
	      begin
		match def.input with
		| is -> 
		    Printf.printf "(%d" (List.hd is);
		    List.iter (Printf.printf ", %d") (List.tl is);
		    print_string ")"
	      end;
	      (match def.output with
	      |	Int out -> Printf.printf " -> %d" out
	      |	Bool out -> Printf.printf " -> %b" out);
	      print_string "\n   ")
	      defs;
	    print_string "]\n") model
		      
  let eval_term model t = 
    let apply id args = 
      let defs = try IdMap.find id model with Not_found -> [] in
      try 
	let def = List.find (fun def -> def.input = args) defs in
	match def.output with
	| Int out -> out
	| Bool b -> failwith "expected Int"
      with Not_found -> begin
	match args with
	| [] -> failwith ("Model.class_of_term: constant " ^ str_of_ident id ^ " is undefined")
	| _ -> failwith ("Model.class_of_term: function " ^ str_of_ident id ^ " is not totally defined")
      end
    in 
    let rec eval = function
    | Var v -> failwith "Model.class_of_term: term is not ground"
    | Const id -> apply id []
    | FunApp (id, ts) ->
	let args = List.map eval ts in
	apply id args
    in try Some (eval t) with _ -> None

  let prune model terms =
    fold (fun id def sm -> 
      let keep_def = 
	match def.input, def.output with
	| _ :: _ as inputs, Int _ -> 
	    TermSet.exists (function 
	      | FunApp (id', ts) when id = id' -> 
		  List.fold_left2 
		    (fun acc t i -> acc && 
		      (match eval_term model t with
		      | Some i' -> i = i'
		      | None -> false))
		    true ts inputs
	      | _ -> false) terms
	| _ :: _ as inputs, Bool _ ->
	    List.for_all 
	      (fun i -> 
		TermSet.exists 
		  (fun t -> 
		    match eval_term model t with
		    | Some i' -> i = i'
		    | None -> false)
		  terms)
	      inputs
	| _ -> true
      in
      if keep_def then add_def id (def.input, def.output) sm else sm)
      model empty
end
