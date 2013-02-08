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
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_sort0 srt

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
  String.concat "_" (List.rev cmnts)

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

