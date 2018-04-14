(** Abstract syntax tree for GRASS formulas (a fragment of sorted first-order logic) *)

open Util

(** {6 Source position} *)

type source_position = {
    sp_file : string;
    sp_start_line : int;
    sp_start_col : int;
    sp_end_line : int;
    sp_end_col : int;
  }


(** {6 Identifiers, sorts, and symbols} *)

(** identifiers *)
type ident = string * int

module IdSet = Set.Make(struct
    type t = ident
    let compare = compare
  end)

module IdMap = Map.Make(struct
    type t = ident
    let compare = compare
end)

module IdGraph = Graph.Make(struct
    type t = ident
    let compare = compare
    let hash = Hashtbl.hash
    let equal = (=)
  end)(IdSet)

    
(** sorts *)
type sort =
  | Bool | Byte | Int (** basic sorts *)
  | Loc of sort (** memory locations *)
  | Set of sort (** sets *)
  | Map of sort list * sort (** maps *)
  | Array of sort (** arrays *)
  | ArrayCell of sort (** array cells *)
  | Adt of ident * adt_def list (** algebraic data types *)
  | Pat (** patterns *)
  | FreeSrt of ident (** uninterpreted sorts *)
and adt_def = ident * (ident * (ident * sort) list) list (** data type constructor *)
        
module IdSrtSet = Set.Make(struct
    type t = ident * sort
    let compare = compare
  end)

module SortSet = Set.Make(struct
    type t = sort
    let compare = compare
  end)

module SortMap = Map.Make(struct
    type t = sort
    let compare = compare
  end)

type sorted_ident = ident * sort

type arity = sort list * sort

(** symbols *)
type symbol =
  (* interpreted constant symbols *)
  | BoolConst of bool
  | IntConst of Int64.t
  (* interpreted function symbols *)
  | Null | Read | Write | EntPnt
  | UMinus | Plus | Minus | Mult | Div | Mod (* Int *)
  | BitAnd | BitOr | BitNot | ShiftLeft | ShiftRight (* Bit Vector *)
  | Empty | SetEnum | Union | Inter | Diff  (* Set *)
  | Length | IndexOfCell | ArrayOfCell | ArrayCells
  | ByteToInt | IntToByte (* explicit conversion *)
  | Ite (* if-then-else *)
  (* interpreted predicate symbols *)
  | Eq
  | LtEq | GtEq | Lt | Gt
  | Btwn | Frame
  | Elem | SubsetEq | Disjoint
  (* constructors and destructors *)
  | Constructor of ident | Destructor of ident    
  (* uninterpreted constants, functions, and predicates *)
  | FreeSym of ident
  (* oldification *)
  | Old      
  (* for patterns *)
  | Known

let symbols = 
  [BoolConst true; BoolConst false; 
   Null; Read; Write; EntPnt;
   UMinus; Plus; Minus; Mult; Div; Mod;
   BitAnd; BitOr; BitNot; ShiftLeft; ShiftRight;
   Empty; SetEnum; Union; Inter; Diff;
   Length; IndexOfCell; ArrayOfCell; ArrayCells;
   Ite;
   Eq; LtEq; GtEq; Lt; Gt;
   Btwn; Frame; Elem; SubsetEq; Disjoint;
   Known; Old]

module SymbolSet = Set.Make(struct
    type t = symbol
    let compare = compare
  end)

module SymbolMap = Map.Make(struct
    type t = symbol
    let compare = compare
  end)

module SortedSymbolSet = Set.Make(struct
    type t = symbol * arity
    let compare = compare
  end)

module SortedSymbolMap = Map.Make(struct
    type t = symbol * arity
    let compare = compare
  end)

type signature = arity SymbolMap.t

(** {6 Terms and formulas} *)

(** terms *)
type term = 
  | Var of ident * sort
  | App of symbol * term list * sort

let symbol_of = function
  | Var _ -> None
  | App (sym, _, _) -> Some sym
        
let sort_of = function
  | Var (_, s) 
  | App (_, _, s) -> s

let rec sort_ofs = function
  | [] -> failwith "tried to extract sort from empty list of terms"
  | t :: ts -> sort_of t

type subst_map = term IdMap.t

module TermSet = Set.Make(struct
    type t = term
    let compare = compare
  end)

module TermMap = Map.Make(struct
    type t = term
    let compare = compare
  end)

(** filters for term generators *)
type filter =
  | FilterNotNull
  | FilterSymbolNotOccurs of symbol
  | FilterReadNotOccurs of string * arity
  | FilterGeneric of (subst_map -> term -> bool)

(** matching guards for term generators *)
type guard =
  | Match of term * filter list
        
(** annotations *)
type annot =
  | Comment of string
  | SrcPos of source_position
  | ErrorMsg of source_position * string
  | Label of bool * term
  | Name of ident
  | TermGenerator of guard list * term list
  | Pattern of term * filter list
        
(** Boolean operators *)
type bool_op =
  | And | Or | Not

(** quantifiers *)
type binder =
  | Forall | Exists

(** GRASS formulas *)
type form =
  | Atom of term * annot list
  | BoolOp of bool_op * form list
  | Binder of binder * (ident * sort) list * form * annot list

(** {6 Pretty printing} *)

(** {5 Infix Notation} *)

open Format

let string_of_src_pos pos =
  if pos.sp_end_line = pos.sp_start_line 
  then 
    Printf.sprintf "File \"%s\", line %d, columns %d-%d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_col
  else 
    Printf.sprintf "File \"%s\", line %d, column %d to line %d, column %d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_line pos.sp_end_col

let string_of_ident0 (name, n) =
  Printf.sprintf "%s^%d" name n

let string_of_ident (name, n) =
  if n = 0 then name else
  Printf.sprintf "%s^%d" name n

let string_of_symbol = function
  (* function symbols *)
  | BoolConst b -> Printf.sprintf "%b" b
  | IntConst i -> Int64.to_string i
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
  | Length -> "length"
  | IndexOfCell -> "index"
  | ArrayOfCell -> "array"
  | ArrayCells -> "cells"
  | UMinus -> "-"
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Empty -> "{}"
  | SetEnum -> "singleton"
  | Union -> "++"
  | Inter -> "**"
  | Diff -> "--"
  | BitAnd -> "&"
  | BitOr -> "|"
  | BitNot -> "!"
  | ShiftLeft -> "<<"
  | ShiftRight -> ">>"
  | ByteToInt -> "toInt"
  | IntToByte -> "toByte"
  | Ite -> "ite"
  (* predicate symbols *)
  | Eq -> "=="
  | LtEq -> "<="
  | GtEq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Btwn -> "Btwn"
  | Elem -> "in"
  | SubsetEq -> "subsetof"
  | Disjoint -> "Disjoint"
  | Frame -> "Frame"
  (* constructors and destructors *)
  | Constructor id 
  | Destructor id -> string_of_ident id 
  (* uninterpreted symbols *)
  | FreeSym id -> string_of_ident id
  (* oldification *)
  | Old -> "old"      
  (* patterns *)
  | Known -> "known"

let string_of_bop = function
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"

let prio_of_symbol = function
  | Null | Empty | IntConst _ | BoolConst _ -> 0
  | Read | Write | Constructor _ | Destructor _ | Old | SetEnum
  | Length | IndexOfCell | ArrayOfCell | ArrayCells | EntPnt | ByteToInt | IntToByte
  | Btwn | Frame | Disjoint | Known | FreeSym _ -> 1
  | UMinus | BitNot -> 2 
  | Mult | Div | Mod -> 3
  | Minus | Plus -> 4
  | ShiftLeft | ShiftRight -> 5
  | Diff | Union | Inter -> 6
  | Gt | Lt | GtEq | LtEq | Elem | SubsetEq -> 7
  | Eq -> 8
  | BitAnd -> 9
  | BitOr -> 10
  | Ite -> 11

let prio_of_term = function
  | App (sym, _, _) -> prio_of_symbol sym
  | Var _ -> 0
        
let prio_of_form = function
  | Atom (t, []) -> prio_of_term t
  | Atom (_, _) -> 0
  | BoolOp (Not, _) -> 2
  | BoolOp (And, _) -> 12
  | BoolOp (Or, _) -> 16
  | Binder _ -> 18
        
let pr_ident ppf id = fprintf ppf "%s" (string_of_ident id)

let rec pr_ident_list ppf = function
  | [] -> ()
  | [id] -> pr_ident ppf id
  | id :: ids -> fprintf ppf "%a,@ %a" pr_ident id pr_ident_list ids

let loc_sort_string = "Loc"
let map_sort_string = "Map"
let array_sort_string = "Array"
let array_cell_sort_string = "ArrayCell"
let set_sort_string = "Set"
let bool_sort_string = "Bool"
let int_sort_string = "Int"
let byte_sort_string = "Byte"
let pat_sort_string = "Pat"
    
let name_of_sort = function
  | Int -> int_sort_string
  | Bool -> bool_sort_string
  | Byte -> byte_sort_string
  | Loc _ -> loc_sort_string
  | Set _ -> set_sort_string
  | Map _ -> map_sort_string
  | Array _ -> array_sort_string
  | ArrayCell _ -> array_cell_sort_string
  | Adt (id, _) -> string_of_ident id
  | Pat -> pat_sort_string
  | FreeSrt id -> string_of_ident id
    
let pr_sym ppf sym = fprintf ppf "%s" (string_of_symbol sym)
  
let rec pr_sort ppf srt = match srt with
  | Bool
  | Int
  | Byte
  | Pat -> fprintf ppf "%s" (name_of_sort srt)
  | Loc e
  | Set e
  | Array e
  | ArrayCell e -> fprintf ppf "%s<@[%a@]>" (name_of_sort srt) pr_sort e
  | Adt (id, cnsts) -> fprintf ppf "%a" pr_ident id
  | FreeSrt id -> pr_ident ppf id
  | Map (ds, r) -> fprintf ppf "%s<@[%a,@ %a@]>" map_sort_string pr_sorts ds pr_sort r
        
and pr_sorts ppf = function
  | [srt] ->  fprintf ppf "%a" pr_sort srt
  | srts -> fprintf ppf "(%a)" (pr_list_comma pr_sort) srts
        
let pr_var ppf (x, srt) =
  fprintf ppf "@[%a: %a@]" pr_ident x pr_sort srt

let rec pr_vars = pr_list_comma pr_var

let rec pr_term ppf = function
  | Var (id, _) -> fprintf ppf "%a" pr_ident id
  | App (Union, [], _) -> fprintf ppf "{}"
  | App (Inter, [], _) -> fprintf ppf "Univ"
  | App (sym, [], _) -> fprintf ppf "%a" pr_sym sym
  | App (Read, [map; t], _) ->
      (match map, sort_of t with
      | App (FreeSym _, [], _), Loc _ -> fprintf ppf "%a.%a" pr_term t pr_term map
      | _ -> fprintf ppf "%a[%a]" pr_term map pr_term t)
  | App (Read, map :: t :: ts, _) ->
      fprintf ppf "%a[%a].%a" pr_term t pr_term_list ts pr_term map
  | App (Write, [map; t1; t2], _) ->
      fprintf ppf "%a[%a := %a]" pr_term map pr_term t1 pr_term t2
  | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq | SubsetEq | LtEq | GtEq | Lt | Gt | Elem as sym), [t1; t2], _) ->
      let pr_t1 = 
        if prio_of_symbol sym < prio_of_term t1
        then pr_term_paran
        else pr_term
      in
      let pr_t2 =
        if prio_of_symbol sym <= prio_of_term t2
        then pr_term_paran
        else pr_term
      in        
      fprintf ppf "@[<2>%a %a@ %a@]" pr_t1 t1 pr_sym sym pr_t2 t2
  | App (Length, [t], _) -> fprintf ppf "%a.%s" pr_term t (string_of_symbol Length)
  | App (ArrayCells, [t], _) -> fprintf ppf "%a.%s" pr_term t (string_of_symbol ArrayCells)
  | App (SetEnum, ts, _) -> fprintf ppf "{@[%a@]}" pr_term_list ts
  | App (Destructor d, [t], _) -> fprintf ppf "%a.%a" pr_term t pr_ident d
  | App (sym, ts, _) -> fprintf ppf "%a(@[%a@])" pr_sym sym pr_term_list ts

and pr_term_paran ppf t = fprintf ppf "(%a)" pr_term t        

and pr_term_list ppf = pr_list_comma pr_term ppf

let extract_name ann =
  let names = Util.filter_map 
      (function Name _ -> !Config.named_assertions && true | _ -> false) 
      (function Name id -> string_of_ident id | _ -> "")
      ann 
  in
  String.concat "; " (List.rev names)

let rec extract_src_pos = function
  | SrcPos pos :: _ -> Some pos
  | _ :: ann -> extract_src_pos ann
  | [] -> None

let rec extract_label = function
  | Label (pol, t) :: _ -> Some (pol, t)
  | _ :: ann -> extract_label ann
  | [] -> None

let rec extract_gens = function
  | TermGenerator (ms, ts) :: ann ->
      (List.map (function Match (t, f) -> t, f) ms, ts) :: extract_gens ann
  | _ :: ann -> extract_gens ann
  | [] -> []

let rec extract_patterns = function
  | Pattern (t, _) :: ann -> t :: extract_patterns ann
  | _ :: ann -> extract_patterns ann
  | [] -> []
        
let pr_binder ppf b =
  let b_str = match b with
  | Forall -> "forall"
  | Exists -> "exists"
  in 
  fprintf ppf "%s" b_str

       
let rec pr_form ppf = function
  | Binder (b, vs, f, a) -> 
      fprintf ppf "@[%a%a@]" pr_quantifier (b, vs, f) pr_annot a
  | BoolOp (And, []) -> fprintf ppf "true"
  | BoolOp (Or, []) -> fprintf ppf "false"
  | BoolOp (And, [f])
  | BoolOp (Or, [f]) -> pr_form ppf f
  | BoolOp ((And | Or as bop), f1 :: f2 :: fs) as f ->
      let pr_f1 =
        if prio_of_form f < prio_of_form f1
        then pr_form_paran
        else pr_form
      in
      let pr_f2 ppf = function
        | f2, [] ->
            if prio_of_form f <= prio_of_form f2
            then pr_form_paran ppf f2
            else pr_form ppf f2
        | f2, fs ->
            pr_form ppf (BoolOp (bop, f2 :: fs))
      in
      fprintf ppf "@[<2>%a@] %s@ %a" pr_f1 f1 (string_of_bop bop) pr_f2 (f2, fs)
  | BoolOp (Not, [f]) -> pr_not ppf f
  | BoolOp (_, _) -> ()
  | Atom (t, []) -> fprintf ppf "@[%a@]" pr_term t
  | Atom (t, a) -> fprintf ppf "@[(%a%a)@]" pr_term t pr_annot a

and pr_form_paran ppf f = fprintf ppf "(%a)" pr_form f
        
and pr_annot ppf a =
  let gen = extract_gens a in
  let name = extract_name a in
  let pos = extract_src_pos a in
  let lbl = extract_label a in
  let pat = extract_patterns a in
  let pr_filter ppf fs =
    let ids =
      List.fold_right
        (fun f ids -> match f with
          | FilterSymbolNotOccurs sym ->
              string_of_symbol sym :: ids
          | FilterReadNotOccurs (name, _) ->
              name :: ids
          | FilterNotNull ->
              string_of_symbol Null :: ids
          | _ ->
              ids)
        fs []
    in
    match ids with
    | [] -> ()
    | _ -> fprintf ppf "@ without@ %s" (String.concat ", " ids)
  in
  let rec pr_match_list ppf = function
    | [] -> ()
    | [(m, f)] ->
        fprintf ppf "%a%a" pr_term m pr_filter f
    | (m, f) :: ms ->
        fprintf ppf "%a%a@ and@ %a" pr_term m pr_filter f pr_match_list ms
  in
  let rec pr_generators ppf = function
    | (ms, ts) :: gen ->
        fprintf ppf "@ @[<3>@@(matching %a@ yields %a)@]%a" pr_match_list ms pr_term_list ts pr_generators gen
    | [] -> ()
  in
  let rec pr_patterns ppf = function
    | t :: patterns ->
        fprintf ppf "@ @[<3>@@(pattern %a)@]%a" pr_term t pr_patterns patterns
    | [] -> ()
  in
  let pr_comment ppf (name, pos, lbl) =
      (match name, pos, lbl with
      | "", None, None -> fprintf ppf ""
      | "", Some pos, None -> fprintf ppf "@ /* %s */" (string_of_src_pos pos)
      | "", Some pos, Some (pol, t) ->
          let lbl = if pol then Atom (t, []) else BoolOp (Not, [Atom (t, [])]) in
          fprintf ppf "@ /* %a -> %s */" pr_form lbl (string_of_src_pos pos)
      | n, Some pos, None -> fprintf ppf "@ /* %s: %s */" (string_of_src_pos pos) n
      | n, Some pos, Some (pol, t) ->
          let lbl = if pol then Atom (t, []) else BoolOp (Not, [Atom (t, [])]) in
          fprintf ppf "@ /* %a -> %s: %s */" pr_form lbl (string_of_src_pos pos) n
      | n, None, _ -> fprintf ppf "@ /* %s */" n)
  in
  fprintf ppf "%a%a%a" pr_generators gen pr_patterns pat pr_comment (name, pos, lbl)
 
and pr_not ppf = function
  | Atom (App (Eq, [t1; t2], _), []) ->
      fprintf ppf "@[%a@]@ !=@ @[<2>%a@]" pr_term t1 pr_term t2
  | Atom (App (Elem, [t1; t2], _), []) ->
      fprintf ppf "@[%a@]@ !in@ @[<2>%a@]" pr_term t1 pr_term t2
  | Atom (App (Eq, [t1; t2], _), a) ->
      fprintf ppf "@[(@[%a@]@ !=@ @[<2>%a@]%a)@]" pr_term t1 pr_term t2 pr_annot a
  | Atom (App (Elem, [t1; t2], _), a) ->
      fprintf ppf "@[(@[%a@]@ !in@ @[<2>%a@]%a)@]" pr_term t1 pr_term t2 pr_annot a
  | f ->
      if prio_of_form (BoolOp (Not, [f]))  < prio_of_form f
      then fprintf ppf "!(@[%a@])" pr_form f
      else fprintf ppf "!@[%a@]" pr_form f

and pr_quantifier ppf = function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> fprintf ppf "@[<2>%a @[%a@] ::@ %a@]" pr_binder b pr_vars vs pr_form f


and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts


let string_of_sort s = pr_sort str_formatter s; flush_str_formatter ()

let string_of_term t = 
  let margin = pp_get_margin str_formatter () in
  pp_set_margin str_formatter 9999;
  pr_term str_formatter t; 
  let res = flush_str_formatter () in
  pp_set_margin str_formatter margin;
  res

let string_of_form f = 
  pr_form str_formatter f; 
  flush_str_formatter ()

let string_of_arity arity =
  List.fold_right
    (fun s acc -> (string_of_sort s) ^ " -> " ^ acc)
    (fst arity)
    (string_of_sort (snd arity))


(** Print term [t] to out channel [out_chan]. *)
let print_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t

(** Print formula [f] to out channel [out_chan]. *)
let print_form out_ch f = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_form f

let print_forms ch fs = 
  List.iter (fun f -> print_form ch f;  output_string ch "\n") fs
  
let print_subst_map subst_map =
  Printf.printf "[";
  IdMap.iter (fun id t -> Printf.printf "  %s -> %s\n" (string_of_ident id) (string_of_term t)) subst_map;
  print_endline "]"
    
let string_of_filter = function
  | FilterNotNull -> "null filter"
  | FilterSymbolNotOccurs sym -> "symbol filter: " ^ (string_of_symbol sym)
  | FilterReadNotOccurs (name, arity) -> "name filter: " ^ name ^ ": " ^ (string_of_arity arity)
  | FilterGeneric _ -> "generic filter ..."
