(** Abstract syntax tree for formulas in sorted first-order logic *)

open Util

(** {6 Sorts and symbols} *)

type ident = string * int

type sort =
  | Bool | Loc | Int (** basic sorts *)
  | Set of sort (** sets *)
  | Fld of sort (** fields *)
  | FreeSrt of ident (** uninterpreted sorts *)

type arity = sort list * sort

type symbol =
  (* interpreted constant symbols *)
  | BoolConst of bool
  | IntConst of int
  (* interpreted function symbols *)
  | Null | Read | Write | EntPnt
  | UMinus | Plus | Minus | Mult | Div 
  | Empty | SetEnum | Union | Inter | Diff
  (* interpreted predicate symbols *)
  | Eq
  | LtEq | GtEq | Lt | Gt
  | Btwn | Frame
  | Elem | SubsetEq 
  (* uninterpreted constants, functions, and predicates *)
  | FreeSym of ident

let symbols = 
  [BoolConst true; BoolConst false; 
   Null; Read; Write; EntPnt;
   UMinus; Plus; Minus; Mult;
   Empty; SetEnum; Union; Inter; Diff;
   Eq; LtEq; GtEq; Lt; Gt;
   Btwn; Frame; Elem; SubsetEq]

(** {6 Terms and formulas} *)

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

module IdSrtSet = Set.Make(struct
    type t = ident * sort
    let compare = compare
  end)

module SrtSet = Set.Make(struct
    type t = sort
    let compare = compare
  end)

module SrtMap = Map.Make(struct
    type t = sort
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

module SymbolSet = Set.Make(struct
    type t = symbol
    let compare = compare
  end)

module SymbolMap = Map.Make(struct
    type t = symbol
    let compare = compare
  end)

type signature = arity SymbolMap.t

type subst_map = term IdMap.t

(** {6 Pretty printing} *)

(** {5 SMT-LIB 2 Notation} **)

open Format

let str_of_ident0 (name, n) =
  Printf.sprintf "%s_%d" name n

let str_of_ident (name, n) =
  if n = 0 then name else
  Printf.sprintf "%s_%d" name n

let str_of_symbol = function
  (* function symbols *)
  | BoolConst b -> Printf.sprintf "%b" b
  | IntConst i -> string_of_int i
  | Null -> "null"
  | Read -> 
      if !Config.encode_fields_as_arrays 
      then "select"
      else "read"
  | Write -> 
      if !Config.encode_fields_as_arrays 
      then "store"
      else "write"
  | EntPnt -> "ep"
  | UMinus -> "-"
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "div"
  | Empty -> "emptyset"
  | SetEnum -> "setenum"
  | Union -> "union"
  | Inter -> "inter"
  | Diff -> "diff"
  (* predicate symbols *)
  | Eq -> "="
  | LtEq -> "<="
  | GtEq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Btwn -> "Btwn"
  | Elem -> "Elem"
  | SubsetEq -> "Subseteq"
  | Frame -> "Frame"
  (* uninterpreted symbols *)
  | FreeSym id -> str_of_ident id

let pr_ident ppf id = fprintf ppf "%s" (str_of_ident id)

let rec pr_ident_list ppf = function
  | [] -> ()
  | [id] -> pr_ident ppf id
  | id :: ids -> fprintf ppf "%a,@ %a" pr_ident id pr_ident_list ids

let pr_sym ppf sym = fprintf ppf "%s" (str_of_symbol sym)

let rec pr_term ppf = function
  | Var (id, _) -> fprintf ppf "%a" pr_ident id
  | App (sym, [], _) -> fprintf ppf "%a" pr_sym sym
  | App (sym, ts, _) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts

and pr_terms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_term t
  | t :: ts -> fprintf ppf "%a@ %a" pr_term t pr_terms ts

let rec pr_term_list ppf = function
  | [] -> ()
  | [t] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a,@ %a" pr_term t pr_term_list ts
      
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
let int_sort_string = "Int"

let rec pr_sort0 ppf srt = match srt with
  | Loc | Bool | Int -> fprintf ppf "%a" pr_sort srt
  | FreeSrt id -> pr_ident ppf id
  | _ -> fprintf ppf "@[<1>(%a)@]" pr_sort srt

and pr_sort ppf = function
  | Loc -> fprintf ppf "%s" loc_sort_string
  | Bool -> fprintf ppf "%s" bool_sort_string
  | Int -> fprintf ppf "%s" int_sort_string
  | FreeSrt id -> pr_ident ppf id
  (*| Fld s -> fprintf ppf "@[<4>%s@ %a@]" fld_sort_string pr_sort0 s*)
  | Fld s -> fprintf ppf "@[<4>%s%a@]" fld_sort_string pr_sort0 s
  (*| Set s -> fprintf ppf "@[<4>%s@ %a@]" set_sort_string pr_sort0 s*)
  | Set s -> fprintf ppf "@[<4>%s%a@]" set_sort_string pr_sort0 s
		
let pr_var ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_sort0 srt

let rec pr_vars ppf = function
  | [] -> ()
  | [v] -> fprintf ppf "%a" pr_var v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var v pr_vars vs

let extract_comments smt ann =
  let cmnts = Util.filter_map 
      (function Comment _ -> true (*| _ -> false*)) 
      (function Comment c -> c (*| _ -> ""*)) 
      ann 
  in
  if smt 
  then Str.global_replace (Str.regexp " ") "_" (String.concat "_" (List.rev cmnts))
  else String.concat "; " (List.rev cmnts)

let rec pr_form ppf = function
  | Binder (b, vs, f, a) -> 
      let cmnts = extract_comments true a in
      (match cmnts with
      |	"" -> fprintf ppf "%a" pr_quantifier (b, vs, f)
      |	c -> fprintf ppf "@[<3>(! %a@ @[:named@ %s@])@]" pr_quantifier (b, vs, f) c)
  | Atom t -> fprintf ppf "%a" pr_term t
  | BoolOp (And, []) -> fprintf ppf "%s" "true"
  | BoolOp (Or, []) -> fprintf ppf "%s" "false"
  | BoolOp (Or, fs) -> fprintf ppf "@[<4>(%a@ %a)@]" pr_boolop Or pr_forms fs
  | BoolOp (op, fs) -> fprintf ppf "@[<5>(%a@ %a)@]" pr_boolop op pr_forms fs

and pr_quantifier ppf = function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> fprintf ppf "@[<8>(%a@ @[<1>(%a)@]@ %a)@]" pr_binder b pr_vars vs pr_form f


and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts


let print_smtlib_sort out_ch s = pr_sort (formatter_of_out_channel out_ch) s
let print_smtlib_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t
let print_smtlib_form out_ch f =  fprintf (formatter_of_out_channel out_ch) "@[<8>%a@]@?" pr_form f

let string_of_smtlib_sort s = pr_sort str_formatter s; flush_str_formatter ()

(** Print term [t] to out channel [out_chan]. *)
let print_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t

(** Print formula [f] to out channel [out_chan]. *)
let print_form out_ch f = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_form f

(** {5 Infix Notation} *)

let rec pr_sort ppf = function
  | Loc -> fprintf ppf "%s" loc_sort_string
  | Bool -> fprintf ppf "%s" bool_sort_string
  | Int -> fprintf ppf "%s" int_sort_string
  | FreeSrt id -> pr_ident ppf id
  | Fld s -> fprintf ppf "%s<@[%a@]>" fld_sort_string pr_sort s
  | Set s -> fprintf ppf "%s<@[%a@]>" set_sort_string pr_sort s
		
let pr_var ppf (x, srt) =
  fprintf ppf "@[%a: %a@]" pr_ident x pr_sort srt

let rec pr_vars ppf = function
  | [] -> ()
  | [v] -> pr_var ppf v
  | v :: vs -> fprintf ppf "%a,@ %a" pr_var v pr_vars vs 

let rec pr_term0 ppf t =
  match t with
  | App (sym, _, _) ->
      (match sym with
      | Diff | Union | Inter | Plus | Minus | Mult | Div -> 
          fprintf ppf "(%a)" pr_term t
      | _ -> pr_term ppf t)
  | _ -> pr_term ppf t

and pr_term ppf = function
  | Var (id, _) -> fprintf ppf "%a" pr_ident id
  | App (Empty, _, _) -> fprintf ppf "{}"
  | App (sym, [], _) -> fprintf ppf "%a" pr_sym sym
  | App (Read, [fld; t], _) -> fprintf ppf "%a.%a" pr_term t pr_term fld
  | App (Write, [fld; t1; t2], _) -> fprintf ppf "%a[%a :=@ %a]" pr_term fld pr_term t1 pr_term t2
  | App (Minus, [t1; t2], _) -> fprintf ppf "%a -@ @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Plus, [t1; t2], _) -> fprintf ppf "%a +@ @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Mult, [t1; t2], _) -> fprintf ppf "%a *@ @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Div, [t1; t2], _) -> fprintf ppf "%a /@ @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Diff, [t1; t2], _) -> fprintf ppf "%a --@ @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Inter, ss, _) -> pr_inter ppf ss
  | App (Union, ss, _) -> pr_union ppf ss
  | App (Eq, [t1; t2], _) -> fprintf ppf "@[%a@] ==@ @[<2>%a@]" pr_term t1 pr_term t2
  | App (SubsetEq, [t1; t2], _)
  | App (LtEq, [t1; t2], _) -> fprintf ppf "%a <=@ @[<2>%a@]" pr_term t1 pr_term t2
  | App (GtEq, [t1; t2], _) -> fprintf ppf "%a >=@ @[<2>%a@]" pr_term t1 pr_term t2
  | App (Lt, [t1; t2], _) -> fprintf ppf "%a <@ @[<2>%a@]" pr_term t1 pr_term t2
  | App (Gt, [t1; t2], _) -> fprintf ppf "%a >@ @[<2>%a@]" pr_term t1 pr_term t2
  | App (Elem, [t1; t2], _) -> fprintf ppf "@[%a@] in@ @[<2>%a@]" pr_term t1 pr_term t2
  | App (SetEnum, ts, _) -> fprintf ppf "{@[%a@]}" pr_term_list ts
  | App (sym, ts, _) -> fprintf ppf "%a(@[%a@])" pr_sym sym pr_term_list ts

and pr_term_list ppf = function
  | [] -> ()
  | [t] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a,@ %a" pr_term t pr_term_list ts

and pr_inter ppf = function
  | [] -> fprintf ppf "Univ"
  | [App (Diff, _, _) as s] -> 
      fprintf ppf "(@[%a@])" pr_term s
  | [s] -> pr_term ppf s
  | App (Inter, ss1, _) :: ss2 -> 
      pr_inter ppf (ss1 @ ss2)
  | (App (Union, _, _) as s) :: ss 
  | (App (Diff, _, _) as s) :: ss -> 
      fprintf ppf "(@[<2>%a@]) **@ %a" pr_term s pr_inter ss
  | s :: ss -> 
      fprintf ppf "@[<2>%a@] **@ %a" pr_term s pr_inter ss

and pr_union ppf = function
  | [] -> fprintf ppf "{}"
  | [App (Diff, _, _) as s] -> 
      fprintf ppf "(@[%a@])" pr_term s
  | [s] -> pr_term ppf s
  | (App (Diff, _, _) as s) :: ss -> 
      fprintf ppf "(@[<2>%a@]) ++@ %a" pr_term s pr_union ss
  | s :: ss -> 
      fprintf ppf "@[<2>%a@] ++@ %a" pr_term s pr_union ss

let rec pr_form ppf = function
  | Binder (b, vs, f, a) -> 
      let cmnts = extract_comments false a in
      (match cmnts with
      |	"" -> fprintf ppf "@[(%a)@]" pr_quantifier (b, vs, f)
      |	c -> fprintf ppf "@[(%a@ /* %s */)@]" pr_quantifier (b, vs, f) c)
  | BoolOp (And, fs) -> pr_ands ppf fs
  | BoolOp (Or, fs) -> pr_ors ppf fs
  | BoolOp (Not, [f]) -> pr_not ppf f
  | BoolOp (_, _) -> ()
  | Atom t -> fprintf ppf "%a" pr_term t

and pr_ands ppf = function
  | [] -> fprintf ppf "%s" "true"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Or, _) as f) :: fs -> fprintf ppf "(@[<2>%a@]) &&@ %a" pr_form f pr_ands fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &&@ %a" pr_form f pr_ands fs

and pr_ors ppf = function
  | [] -> fprintf ppf "%s" "false"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | f :: fs -> fprintf ppf "@[<2>%a@] ||@ %a" pr_form f pr_ors fs

and pr_not ppf = function
  | Atom (App (Eq, [t1; t2], _)) ->
      fprintf ppf "@[%a@]@ !=@ @[<2>%a@]" pr_term t1 pr_term t2
  | Atom (App (Elem, [t1; t2], _)) ->
      fprintf ppf "@[%a@]@ !in@ @[<2>%a@]" pr_term t1 pr_term t2
  | Atom (App (_, [], _)) as f -> 
      fprintf ppf "!@[%a@]" pr_form f
  | f -> fprintf ppf "!(@[%a@])" pr_form f

and pr_quantifier ppf = function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> fprintf ppf "@[<2>%a @[%a@] ::@ %a@]" pr_binder b pr_vars vs pr_form f


and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts


let string_of_sort s = pr_sort0 str_formatter s; flush_str_formatter ()
let string_of_term t = pr_term str_formatter t; flush_str_formatter ()
let string_of_form f = pr_form str_formatter f; flush_str_formatter ()

let print_forms ch fs = 
  List.iter (fun f -> print_form ch f;  output_string ch "\n") fs
  
