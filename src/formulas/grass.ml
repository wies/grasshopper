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

(** sorts *)
type sort =
  | Bool | Byte | Int (** basic sorts *)
  | Loc of sort (** memory locations *)
  | Set of sort (** sets *)
  | Map of sort list * sort (** maps *)
  | Array of sort (** arrays *)
  | ArrayCell of sort (** array cells *)
  | Pat (** patterns *)
  | FreeSrt of ident (** uninterpreted sorts *)

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

module FormSet = Set.Make(struct
    type t = form
    let compare = compare
  end)

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
  Printf.sprintf "%s_%d" name n

let string_of_ident (name, n) =
  if n = 0 then name else
  Printf.sprintf "%s_%d" name n

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
  | Div -> "div"
  | Mod -> "mod"
  | Empty -> "emptyset"
  | SetEnum -> "singleton"
  | Union -> "union"
  | Inter -> "intersection"
  | Diff -> "setminus"
  | BitAnd -> "&"
  | BitOr -> "|"
  | BitNot -> "!"
  | ShiftLeft -> "<<"
  | ShiftRight -> ">>"
  | ByteToInt -> "toInt"
  | IntToByte -> "toByte"
  | Ite -> "ite"
  (* predicate symbols *)
  | Eq -> "="
  | LtEq -> "<="
  | GtEq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Btwn -> "Btwn"
  | Elem -> "member"
  | SubsetEq -> "subset"
  | Disjoint -> "Disjoint"
  | Frame -> "Frame"
  (* uninterpreted symbols *)
  | FreeSym id -> string_of_ident id
  (* oldification *)
  | Old -> "old"      
  (* patterns *)
  | Known -> "known"
        
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
  | Pat -> pat_sort_string
  | FreeSrt id -> string_of_ident id
    
let pr_sym ppf sym = fprintf ppf "%s" (string_of_symbol sym)

let rec pr_list pr_x ppf = function
  | [] -> ()
  | [x] -> fprintf ppf "%a" pr_x x
  | x :: xs -> fprintf ppf "%a,@ %a" pr_x x (pr_list pr_x) xs
  
let rec pr_sort ppf srt = match srt with
  | Bool
  | Int
  | Byte
  | Pat -> fprintf ppf "%s" (name_of_sort srt)
  | Loc e
  | Set e
  | Array e
  | ArrayCell e -> fprintf ppf "%s<@[%a@]>" (name_of_sort srt) pr_sort e
  | FreeSrt id -> pr_ident ppf id
  | Map (ds, r) -> fprintf ppf "%s<@[%a,@ %a@]>" map_sort_string pr_sorts ds pr_sort r
        
and pr_sorts ppf = function
  | [srt] ->  fprintf ppf "%a" pr_sort srt
  | srts -> fprintf ppf "(%a)" (pr_list pr_sort) srts
        
let pr_var ppf (x, srt) =
  fprintf ppf "@[%a: %a@]" pr_ident x pr_sort srt

let rec pr_vars = pr_list pr_var

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
  | App (Read, [map; t], _) ->
      (match sort_of t with
      | Loc _ -> fprintf ppf "%a.%a" pr_term t pr_term map
      | _ -> fprintf ppf "%a[%a]" pr_term map pr_term t)
  | App (Read, map :: t :: ts, _) ->
      fprintf ppf "%a[%a].%a" pr_term t pr_term_list ts pr_term map
  | App (Write, [map; t1; t2], _) ->
      fprintf ppf "%a[%a := %a]" pr_term map pr_term t1 pr_term t2
  | App (Minus, [t1; t2], _) -> fprintf ppf "%a - @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Plus, [t1; t2], _) -> fprintf ppf "%a + @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Mult, [t1; t2], _) -> fprintf ppf "%a * @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Div, [t1; t2], _) -> fprintf ppf "%a / @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Mod, [t1; t2], _) -> fprintf ppf "%a % @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Diff, [t1; t2], _) -> fprintf ppf "%a -- @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Length, [t], _) -> fprintf ppf "%a.%s" pr_term t (string_of_symbol Length)
  | App (ArrayCells, [t], _) -> fprintf ppf "%a.%s" pr_term t (string_of_symbol ArrayCells)
  | App (Inter, ss, _) -> pr_inter ppf ss
  | App (Union, ss, _) -> pr_union ppf ss
  | App (Eq, [t1; t2], _) -> fprintf ppf "@[%a@] == @[<2>%a@]" pr_term t1 pr_term t2
  | App (SubsetEq, [t1; t2], _) -> fprintf ppf "@[%a@] subsetof @[<2>%a@]" pr_term t1 pr_term t2
  | App (LtEq, [t1; t2], _) -> fprintf ppf "%a <= @[<2>%a@]" pr_term t1 pr_term t2
  | App (GtEq, [t1; t2], _) -> fprintf ppf "%a >= @[<2>%a@]" pr_term t1 pr_term t2
  | App (Lt, [t1; t2], _) -> fprintf ppf "%a < @[<2>%a@]" pr_term t1 pr_term t2
  | App (Gt, [t1; t2], _) -> fprintf ppf "%a > @[<2>%a@]" pr_term t1 pr_term t2
  | App (Elem, [t1; t2], _) -> fprintf ppf "@[%a@] in @[<2>%a@]" pr_term t1 pr_term t2
  | App (SetEnum, ts, _) -> fprintf ppf "{@[%a@]}" pr_term_list ts
  | App (sym, ts, _) -> fprintf ppf "%a(@[%a@])" pr_sym sym pr_term_list ts

and pr_term_list ppf = pr_list pr_term ppf

and pr_inter ppf = function
  | [] -> fprintf ppf "Univ"
  | [App (Diff, _, _) as s] -> 
      fprintf ppf "(@[%a@])" pr_term s
  | [s] -> pr_term ppf s
  | App (Inter, ss1, _) :: ss2 -> 
      pr_inter ppf (ss1 @ ss2)
  | (App (Union, _, _) as s) :: ss 
  | (App (Diff, _, _) as s) :: ss -> 
      fprintf ppf "(@[<2>%a@]) ** %a" pr_term s pr_inter ss
  | s :: ss -> 
      fprintf ppf "@[<2>%a@] ** %a" pr_term s pr_inter ss

and pr_union ppf = function
  | [] -> fprintf ppf "{}"
  | [App (Diff, _, _) as s] -> 
      fprintf ppf "(@[%a@])" pr_term s
  | [s] -> pr_term ppf s
  | (App (Diff, _, _) as s) :: ss -> 
      fprintf ppf "(@[<2>%a@]) ++ %a" pr_term s pr_union ss
  | s :: ss -> 
      fprintf ppf "@[<2>%a@] ++ %a" pr_term s pr_union ss

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
      fprintf ppf "@[(%a%a)@]" pr_quantifier (b, vs, f) pr_annot a
  | BoolOp (And, [f])
  | BoolOp (Or, [f]) -> pr_form ppf f
  | BoolOp (And, fs) -> pr_ands ppf fs
  | BoolOp (Or, fs) -> pr_ors ppf fs
  | BoolOp (Not, [f]) -> pr_not ppf f
  | BoolOp (_, _) -> ()
  | Atom (t, []) -> fprintf ppf "@[%a@]" pr_term t
  | Atom (t, a) -> fprintf ppf "@[(%a%a)@]" pr_term t pr_annot a
     
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
 

and pr_ands ppf = function
  | [] -> fprintf ppf "%s" "true"
  | [f] -> fprintf ppf "(@[<2>%a@])" pr_form f
  | (BoolOp (Or, _) as f) :: fs -> fprintf ppf "(@[<2>%a@]) &&@ %a" pr_form f pr_ands fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &&@ %a" pr_form f pr_ands fs

and pr_ors ppf = function
  | [] -> fprintf ppf "%s" "false"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | f :: fs -> fprintf ppf "@[<2>%a@] ||@ %a" pr_form f pr_ors fs

and pr_not ppf = function
  | Atom (App (Eq, [t1; t2], _), a) ->
      fprintf ppf "@[(@[%a@]@ !=@ @[<2>%a@]%a)@]" pr_term t1 pr_term t2 pr_annot a
  | Atom (App (Elem, [t1; t2], _), a) ->
      fprintf ppf "@[(@[%a@]@ !in@ @[<2>%a@]%a)@]" pr_term t1 pr_term t2 pr_annot a
  | Atom (App (_, [], _), _) as f -> 
      fprintf ppf "!@[%a@]" pr_form f
  | f -> fprintf ppf "!(@[%a@])" pr_form f

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
